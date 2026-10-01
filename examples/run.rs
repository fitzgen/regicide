//! Replay serialized register allocation inputs and print what the allocator
//! did with them.
//!
//! A corpus of captured inputs, together with this example, measures a change
//! to the allocator without rebuilding the program that produced them: the
//! per-function counts at the end of each allocation are what to diff between
//! two builds, and the allocation above them is what explains a diff.
//!
//! ```text
//! cargo run --example run -- corpus/
//! cargo run --example run -- --check -q corpus/
//! cargo run --example run -- -r none -d none corpus/one-input.json
//! ```
//!
//! Build a corpus with `scripts/make-corpus` in the `regalloc2` repository.

use regicide::{
    Context, EdgeEdit, Edit, Error, Input, InputFunction, InputOptions, InstOrEdit, Move,
    MoveEliminationLevel, Output, deserialize::DeserializedInput,
};
use std::{
    env,
    fs::File,
    io::{BufReader, BufWriter, Write},
    path::{Path, PathBuf},
    process,
};

const USAGE: &str = "\
usage: run [OPTIONS] <path>...

Run register allocation on each serialized input and print the result. A path
is either a directory, in which case every `*.json` file directly in it is an
input, or a single input file.

  -r, --redundant-moves LEVEL  redundant-move elimination: none, local or
                               global
  -d, --dead-moves LEVEL       dead-move elimination: none, local or global
      --dead-reg-moves         let dead-move elimination consider registers
      --no-dead-reg-moves      restrict it to spill slots
      --validate               validate each input before allocating
      --no-validate            do not validate
      --check                  check each allocation against the checker
  -q, --quiet                  print only the counts, not the allocations
  -h, --help                   print this message

Each option defaults to what the input file itself asked for, so a run with no
options replays the allocation as it was captured.";

fn main() {
    // `RUST_LOG=regicide=trace` then reports what the allocator did on its way
    // to the result, which is where a surprising allocation is explained.
    env_logger::init();

    let args = match Args::parse(env::args().skip(1)) {
        Ok(args) => args,
        Err(message) => {
            eprintln!("{message}\n\n{USAGE}");
            process::exit(2);
        }
    };

    let inputs = match collect(&args.paths) {
        Ok(inputs) => inputs,
        Err(message) => {
            eprintln!("{message}");
            process::exit(1);
        }
    };
    if inputs.is_empty() {
        eprintln!("no `*.json` inputs among the given paths");
        process::exit(1);
    }

    // One `Context`, reset between inputs: allocating is the thing being
    // measured, so do not pay to rebuild the allocator's state each time.
    let mut context = Context::new();
    let mut totals = Counts::default();
    let mut ran = 0_usize;
    let mut skipped = 0_usize;
    let mut failed = 0_usize;

    // Held open across every input, because a corpus is large enough that
    // per-line flushing to a pipe dominates the run.
    let stdout = std::io::stdout();
    let mut out = BufWriter::new(stdout.lock());

    for path in &inputs {
        let name = path
            .file_name()
            .unwrap_or(path.as_os_str())
            .to_string_lossy();

        let input = match load(path) {
            Ok(input) => input,
            Err(message) => {
                // Naming the file matters most for a corpus that predates an
                // encoding change, where every entry fails the same way.
                let _ = writeln!(out, "=== {name} ===\n  could not read: {message}\n");
                failed += 1;
                continue;
            }
        };

        let options = args.options.resolve(input.options());
        let input = Input {
            options: &options,
            machine: input.machine(),
            func: input.func(),
        };

        let _ = writeln!(out, "=== {name} ===");
        if !args.quiet {
            let _ = writeln!(out, "  {}", describe_options(&options));
        }

        // Everything that reads the `Output` happens here, because it borrows
        // the context that printing the allocation needs back.
        let allocated = match regicide::run(&mut context, &input) {
            Ok(output) => {
                let counts = Counts::of(&output, &input);
                let checked = match args.check {
                    true => regicide::checker::check(&input, &output).map_err(|e| format!("{e:?}")),
                    false => Ok(()),
                };
                Ok((counts, checked))
            }
            Err(e) => Err(e),
        };

        match allocated {
            Ok((counts, checked)) => {
                if !args.quiet {
                    let _ = writeln!(out, "{}", input.func.display_with_context(&mut context));
                }
                let _ = writeln!(out, "  {counts}");

                if let Err(e) = checked {
                    let _ = writeln!(out, "  CHECKER FAILED: {e}");
                    failed += 1;
                }

                totals.add(&counts);
                ran += 1;
            }
            // A property of the input rather than a bug in the allocator: this
            // function wants more registers at once than its machine has.
            Err(Error::TooManyLiveRegs) => {
                let _ = writeln!(out, "  skipped: needs more registers than the machine has");
                skipped += 1;
            }
            Err(e) => {
                let _ = writeln!(out, "  FAILED: {e}");
                failed += 1;
            }
        }

        // `run` asserts a reset context, and the `Output` borrowed it until
        // here.
        context.reset();
        let _ = writeln!(out);
    }

    let _ = writeln!(out, "=== totals ({ran} function(s)) ===");
    let _ = writeln!(out, "  {totals}");
    if skipped > 0 {
        let _ = writeln!(out, "  {skipped} skipped");
    }
    if failed > 0 {
        let _ = writeln!(out, "  {failed} failed");
    }
    let _ = out.flush();

    if failed > 0 {
        process::exit(1);
    }
}

/// Expand the given paths into the input files to run.
///
/// A directory contributes the `*.json` files directly in it, sorted so that
/// two runs over one corpus print in the same order and can be diffed.
fn collect(paths: &[String]) -> Result<Vec<PathBuf>, String> {
    let mut inputs = vec![];

    for path in paths {
        let path = Path::new(path);
        if !path.is_dir() {
            if !path.exists() {
                return Err(format!("no such path: {}", path.display()));
            }
            inputs.push(path.to_path_buf());
            continue;
        }

        let dir = path
            .read_dir()
            .map_err(|e| format!("could not read {}: {e}", path.display()))?;
        let mut found = vec![];
        for entry in dir {
            let entry = entry.map_err(|e| format!("could not read {}: {e}", path.display()))?;
            let path = entry.path();
            if path.extension().is_some_and(|ext| ext == "json") {
                found.push(path);
            }
        }
        found.sort();
        inputs.extend(found);
    }

    Ok(inputs)
}

/// Read one serialized input.
fn load(path: &Path) -> Result<DeserializedInput, String> {
    let file = File::open(path).map_err(|e| e.to_string())?;
    serde_json::from_reader(BufReader::new(file)).map_err(|e| e.to_string())
}

/// How many of each kind of edit an allocation introduced.
///
/// These are the numbers to compare between two builds of the allocator: fewer
/// moves and fewer spills is better code, and a corpus makes the comparison
/// over a realistic population rather than one function.
#[derive(Default)]
struct Counts {
    reg_moves: usize,
    spills: usize,
    reloads: usize,
    remats: usize,
    critical_edges: usize,
    spill_slots: usize,
}

impl Counts {
    fn of(output: &Output<'_>, input: &Input<'_, impl InputFunction>) -> Self {
        let mut counts = Self {
            spill_slots: output.spill_slots().len(),
            ..Self::default()
        };

        for (block, _) in input.func.blocks() {
            for item in output.block_insts_and_edits(input.func, block) {
                let InstOrEdit::Edit(edit) = item else {
                    continue;
                };
                match edit {
                    Edit::Move(mv) => counts.count_move(mv),
                    Edit::Remat(_) => counts.remats += 1,
                    Edit::CriticalEdge(edit) => {
                        counts.critical_edges += 1;
                        // Counted as its own kind too: splitting the edge is
                        // what the client must do, but the move is still a
                        // move once the edge is split.
                        match edit.edit {
                            EdgeEdit::Move(mv) => counts.count_move(mv),
                            EdgeEdit::Remat(_) => counts.remats += 1,
                        }
                    }
                }
            }
        }

        counts
    }

    fn count_move(&mut self, mv: Move) {
        match mv {
            Move::RegReg { .. } => self.reg_moves += 1,
            Move::Spill { .. } => self.spills += 1,
            Move::Reload { .. } => self.reloads += 1,
        }
    }

    fn add(&mut self, other: &Self) {
        self.reg_moves += other.reg_moves;
        self.spills += other.spills;
        self.reloads += other.reloads;
        self.remats += other.remats;
        self.critical_edges += other.critical_edges;
        self.spill_slots += other.spill_slots;
    }
}

impl std::fmt::Display for Counts {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "moves {}  spills {}  reloads {}  remats {}  \
             critical-edges {}  slots {}",
            self.reg_moves,
            self.spills,
            self.reloads,
            self.remats,
            self.critical_edges,
            self.spill_slots,
        )
    }
}

/// Render the options a run is using, since the default comes from each file.
fn describe_options(options: &InputOptions) -> String {
    let level = |level: MoveEliminationLevel| match level {
        MoveEliminationLevel::None => "none",
        MoveEliminationLevel::Local => "local",
        MoveEliminationLevel::Global => "global",
    };
    format!(
        "options: validate {}, redundant-moves {}, dead-moves {}, dead-reg-moves {}",
        options.validate_input,
        level(options.redundant_move_elimination_level),
        level(options.dead_move_elimination_level),
        options.eliminate_dead_register_moves,
    )
}

/// The options given on the command line, each absent unless asked for.
///
/// Absent means "whatever the input asked for", so that a bare run reproduces
/// the captured allocation rather than today's defaults.
#[derive(Default)]
struct OptionOverrides {
    validate_input: Option<bool>,
    redundant_move_elimination_level: Option<MoveEliminationLevel>,
    dead_move_elimination_level: Option<MoveEliminationLevel>,
    eliminate_dead_register_moves: Option<bool>,
}

impl OptionOverrides {
    fn resolve(&self, from_file: &InputOptions) -> InputOptions {
        InputOptions {
            validate_input: self.validate_input.unwrap_or(from_file.validate_input),
            redundant_move_elimination_level: self
                .redundant_move_elimination_level
                .unwrap_or(from_file.redundant_move_elimination_level),
            dead_move_elimination_level: self
                .dead_move_elimination_level
                .unwrap_or(from_file.dead_move_elimination_level),
            eliminate_dead_register_moves: self
                .eliminate_dead_register_moves
                .unwrap_or(from_file.eliminate_dead_register_moves),
        }
    }
}

struct Args {
    paths: Vec<String>,
    options: OptionOverrides,
    check: bool,
    quiet: bool,
}

impl Args {
    fn parse(args: impl Iterator<Item = String>) -> Result<Self, String> {
        let mut paths = vec![];
        let mut options = OptionOverrides::default();
        let mut check = false;
        let mut quiet = false;
        let mut args = args;

        while let Some(arg) = args.next() {
            // Split on `=` only for a flag: a path may contain one.
            let (name, inline) = match arg.starts_with('-') {
                true => match arg.split_once('=') {
                    Some((name, value)) => (name.to_string(), Some(value.to_string())),
                    None => (arg, None),
                },
                false => (arg, None),
            };

            // A flag's value is the inline half if it had one, and otherwise
            // the next argument.
            let mut value = |name: &str| match inline.clone() {
                Some(value) => Ok(value),
                None => args.next().ok_or(format!("{name} needs a value")),
            };

            match name.as_str() {
                "-h" | "--help" => {
                    println!("{USAGE}");
                    process::exit(0);
                }
                "-r" | "--redundant-moves" => {
                    options.redundant_move_elimination_level =
                        Some(parse_level(&name, &value(&name)?)?);
                }
                "-d" | "--dead-moves" => {
                    options.dead_move_elimination_level = Some(parse_level(&name, &value(&name)?)?);
                }
                "--dead-reg-moves" => options.eliminate_dead_register_moves = Some(true),
                "--no-dead-reg-moves" => options.eliminate_dead_register_moves = Some(false),
                "--validate" => options.validate_input = Some(true),
                "--no-validate" => options.validate_input = Some(false),
                "--check" => check = true,
                "-q" | "--quiet" => quiet = true,
                _ if name.starts_with('-') => return Err(format!("unknown flag {name}")),
                _ => paths.push(name),
            }
        }

        if paths.is_empty() {
            return Err("no input path".to_string());
        }

        Ok(Args {
            paths,
            options,
            check,
            quiet,
        })
    }
}

fn parse_level(flag: &str, value: &str) -> Result<MoveEliminationLevel, String> {
    match value {
        "none" => Ok(MoveEliminationLevel::None),
        "local" => Ok(MoveEliminationLevel::Local),
        "global" => Ok(MoveEliminationLevel::Global),
        _ => Err(format!("{flag} wants none, local or global, not `{value}`")),
    }
}
