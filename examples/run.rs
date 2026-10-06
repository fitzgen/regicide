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
//! cargo run --example run -- -r none -d none corpus/one-input.postcard
//! cargo run --release --example run -- --insts -q corpus/
//! cargo run --release --example run -- --profile 30 corpus/
//! ```
//!
//! Build a corpus with `scripts/make-corpus` in the `regalloc2` repository.

use regicide::{
    Allocation, BlockFrequency, Context, EdgeEdit, Edit, Error, Input, InputBlock, InputFunction,
    InputOptions, InstOrEdit, Move, MoveEliminationLevel, Output, deserialize::DeserializedInput,
};
use std::{
    env,
    io::{BufWriter, Write},
    path::{Path, PathBuf},
    process,
    time::{Duration, Instant},
};

#[path = "support/encoding.rs"]
mod encoding;

const USAGE: &str = "\
usage: run [OPTIONS] <path>...

Run register allocation on each serialized input and print the result. A path
is either a directory, in which case every `*.postcard` and `*.json` file
directly in it is an input, or a single input file. Either encoding is read,
whichever a file turns out to be in.

  -r, --redundant-moves LEVEL  redundant-move elimination: none, local or
                               global
  -d, --dead-moves LEVEL       dead-move elimination: none, local or global
      --dead-reg-moves         let dead-move elimination consider registers
      --no-dead-reg-moves      restrict it to spill slots
      --narrow-slots           reserve each spill slot only where its value is
                               both live and spilled
      --no-narrow-slots        reserve it across the whole live range
      --validate               validate each input before allocating
      --no-validate            do not validate
      --check                  check each allocation against the checker
      --insts                  count the instructions retired while
                               allocating each input (Linux and macOS only;
                               leave `RUST_LOG` unset, since logging inside
                               the allocator is counted too)
  -q, --quiet                  print only the counts, not the allocations
      --profile SECONDS        after the first pass over the inputs, keep
                               allocating them, printing nothing, until
                               SECONDS have elapsed, so that a sampling
                               profiler gathers enough samples
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
        eprintln!(
            "no `*.{}` inputs among the given paths",
            encoding::EXTENSIONS.join("` or `*.")
        );
        process::exit(1);
    }

    // Read everything before allocating anything, so that a profile of this
    // process is allocation and not deserialization.
    let inputs: Vec<Loaded> = inputs
        .iter()
        .map(|path| Loaded {
            name: path
                .file_name()
                .unwrap_or(path.as_os_str())
                .to_string_lossy()
                .into_owned(),
            input: encoding::load(path).map(|input| {
                let options = args.options.resolve(input.options());
                (input, options)
            }),
        })
        .collect();

    // One `Context`, reset between inputs: allocating is the thing being
    // measured, so do not pay to rebuild the allocator's state each time.
    let mut context = Context::new();
    let mut totals = Counts::default();
    let mut ran = 0_usize;
    let mut skipped = 0_usize;
    let mut failed = 0_usize;

    let mut insts_retired = match args.count_insts {
        true => match insts::InstsRetired::new() {
            Ok(counter) => Some(counter),
            Err(message) => {
                eprintln!("{message}");
                process::exit(1);
            }
        },
        false => None,
    };
    let mut total_insts = 0_u64;
    let mut total_out_of_fuel = None;

    // Held open across every input, because a corpus is large enough that
    // per-line flushing to a pipe dominates the run.
    let stdout = std::io::stdout();
    let mut out = BufWriter::new(stdout.lock());

    // Under `--profile`, keep going in whole passes so that every input is
    // allocated equally often.
    let start = Instant::now();
    let mut passes = 0_usize;
    while passes == 0
        || args
            .profile
            .is_some_and(|duration| start.elapsed() < duration)
    {
        let first = passes == 0;
        for Loaded { name, input } in &inputs {
            let (input, options) = match input {
                Ok(input) => input,
                Err(_) if !first => continue,
                Err(message) => {
                    // Naming the file matters most for a corpus that predates
                    // an encoding change, where every entry fails the same
                    // way.
                    let _ = writeln!(out, "=== {name} ===\n  could not read: {message}\n");
                    failed += 1;
                    continue;
                }
            };

            let input = Input {
                options,
                machine: input.machine(),
                func: input.func(),
            };

            // Every pass allocates the same way, and the first reported it.
            if !first {
                let _ = regicide::run(&mut context, &input);
                context.reset();
                continue;
            }

            let _ = writeln!(out, "=== {name} ===");
            if !args.quiet {
                let _ = writeln!(out, "  {}", describe_options(options));
            }

            // Everything that reads the `Output` happens here, because it
            // borrows the context that printing the allocation needs back.
            if let Some(counter) = &mut insts_retired {
                counter.start();
            }
            let result = regicide::run(&mut context, &input);
            let insts = insts_retired.as_mut().map(|counter| counter.end());

            let allocated = match result {
                Ok(output) => {
                    let counts = Counts::of(&output, &input);
                    let out_of_fuel = output.coalesce_out_of_fuel();
                    let checked = match args.check {
                        true => {
                            regicide::checker::check(&input, &output).map_err(|e| format!("{e:?}"))
                        }
                        false => Ok(()),
                    };
                    Ok((counts, out_of_fuel, checked))
                }
                Err(e) => Err(e),
            };

            match allocated {
                Ok((counts, out_of_fuel, checked)) => {
                    if !args.quiet {
                        let _ = writeln!(out, "{}", input.func.display_with_context(&mut context));
                    }
                    let _ = writeln!(out, "  {counts}");
                    if let Some(insts) = insts {
                        let _ = writeln!(out, "  insts-retired {insts}");
                        total_insts += insts;
                    }
                    if let Some(out_of_fuel) = out_of_fuel {
                        let _ = writeln!(out, "  coalesce-out-of-fuel {out_of_fuel}");
                        *total_out_of_fuel.get_or_insert(0) += out_of_fuel;
                    }

                    if let Err(e) = checked {
                        let _ = writeln!(out, "  CHECKER FAILED: {e}");
                        failed += 1;
                    }

                    totals.add(&counts);
                    ran += 1;
                }
                // A property of the input rather than a bug in the allocator:
                // this function wants more registers at once than its machine
                // has.
                Err(Error::TooManyLiveRegs) => {
                    let _ = writeln!(out, "  skipped: needs more registers than the machine has");
                    skipped += 1;
                }
                Err(e) => {
                    let _ = writeln!(out, "  FAILED: {e}");
                    failed += 1;
                }
            }

            // `run` asserts a reset context, and the `Output` borrowed it
            // until here.
            context.reset();
            let _ = writeln!(out);
        }
        passes += 1;
    }
    let elapsed = start.elapsed();

    let _ = writeln!(out, "=== totals ({ran} function(s)) ===");
    let _ = writeln!(out, "  {totals}");
    if insts_retired.is_some() {
        let _ = writeln!(out, "  insts-retired {total_insts}");
    }
    if let Some(total_out_of_fuel) = total_out_of_fuel {
        let _ = writeln!(out, "  coalesce-out-of-fuel {total_out_of_fuel}");
    }
    if args.profile.is_some() {
        let _ = writeln!(
            out,
            "  profiled {passes} pass(es) in {:.3}s",
            elapsed.as_secs_f64()
        );
    }
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

/// One input file, read and ready to allocate.
struct Loaded {
    name: String,
    /// The input with the options to allocate it under, or why it could not
    /// be read.
    input: Result<(DeserializedInput, InputOptions), String>,
}

/// Expand the given paths into the input files to run.
///
/// A directory contributes the input files directly in it, sorted so that two
/// runs over one corpus print in the same order and can be diffed.
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
            if encoding::is_input(&path) {
                found.push(path);
            }
        }
        found.sort();
        inputs.extend(found);
    }

    Ok(inputs)
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

    /// The share of the edits above that sit in blocks the input marks cold.
    /// The allocator trades hot moves for cold ones on purpose, so a change can
    /// improve the code while raising the total.
    cold: ColdCounts,

    estimated: EstimatedCycles,
}

/// The edits of [`Counts`] that land in cold blocks.
#[derive(Default)]
struct ColdCounts {
    reg_moves: usize,
    spills: usize,
    reloads: usize,
    remats: usize,
}

impl Counts {
    fn of(output: &Output<'_>, input: &Input<'_, impl InputFunction>) -> Self {
        let mut counts = Self {
            spill_slots: output.spill_slots().len(),
            ..Self::default()
        };

        for (block, input_block) in input.func.blocks() {
            let frequency = input_block.frequency();
            let cold = frequency.is_cold();
            let weight = EstimatedCycles::block_weight(output.loop_depth(block), frequency);
            for item in output.block_insts_and_edits(input.func, block) {
                let edit = match item {
                    InstOrEdit::Inst(inst) => {
                        counts
                            .estimated
                            .count_operands(output.inst_allocs(inst), weight);
                        continue;
                    }
                    InstOrEdit::Edit(edit) => edit,
                };
                match edit {
                    Edit::Move(mv) => counts.count_move(mv, cold, weight),
                    Edit::Remat(_) => counts.count_remat(cold, weight),
                    Edit::CriticalEdge(edit) => {
                        counts.critical_edges += 1;
                        // Counted as its own kind too: splitting the edge is
                        // what the client must do, but the move is still a
                        // move once the edge is split.
                        match edit.edit {
                            EdgeEdit::Move(mv) => counts.count_move(mv, cold, weight),
                            EdgeEdit::Remat(_) => counts.count_remat(cold, weight),
                        }
                    }
                }
            }
        }

        counts
    }

    fn count_move(&mut self, mv: Move, cold: bool, weight: f64) {
        let (all, cold_only, estimated) = match mv {
            Move::RegReg { .. } => (
                &mut self.reg_moves,
                &mut self.cold.reg_moves,
                &mut self.estimated.reg_moves,
            ),
            Move::Spill { .. } => (
                &mut self.spills,
                &mut self.cold.spills,
                &mut self.estimated.spills,
            ),
            Move::Reload { .. } => (
                &mut self.reloads,
                &mut self.cold.reloads,
                &mut self.estimated.reloads,
            ),
        };
        *all += 1;
        *cold_only += usize::from(cold);
        *estimated += weight;
    }

    fn count_remat(&mut self, cold: bool, weight: f64) {
        self.remats += 1;
        self.cold.remats += usize::from(cold);
        self.estimated.remats += weight;
    }

    fn add(&mut self, other: &Self) {
        self.reg_moves += other.reg_moves;
        self.spills += other.spills;
        self.reloads += other.reloads;
        self.remats += other.remats;
        self.critical_edges += other.critical_edges;
        self.spill_slots += other.spill_slots;
        self.cold.reg_moves += other.cold.reg_moves;
        self.cold.spills += other.cold.spills;
        self.cold.reloads += other.cold.reloads;
        self.cold.remats += other.cold.remats;
        self.estimated.add(&other.estimated);
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
        )?;
        write!(
            f,
            "\n  of which cold: moves {}  spills {}  reloads {}  remats {}",
            self.cold.reg_moves, self.cold.spills, self.cold.reloads, self.cold.remats,
        )?;
        write!(f, "\n  {}", self.estimated)
    }
}

/// A static estimate of how many cycles an allocation's code costs to run.
///
/// Each operand and edit costs 1 cycle when it is in a register (register
/// operands, register-register moves, remats) and 5 when it touches the stack
/// (stack operands, spills, reloads), times its block's weight: 10x per
/// enclosing loop, and 0.05x for a cold block up to 10x for a hot one (see
/// `block_weight`). The fields are those weighted counts.
///
/// It ignores the instructions' own costs, latency and parallelism, and uses
/// loop depth and the input's frequency hints in place of real execution
/// counts, so it only ranks two allocations of the same inputs.
#[derive(Default)]
struct EstimatedCycles {
    reg_operands: f64,
    stack_operands: f64,
    reg_moves: f64,
    remats: f64,
    spills: f64,
    reloads: f64,
}

impl EstimatedCycles {
    const STACK_COST: f64 = 5.0;
    const LOOP_WEIGHT: f64 = 10.0;
    const COLD_WEIGHT: f64 = 0.05;
    const HOT_WEIGHT: f64 = 10.0;

    /// How much each operand and edit in a block counts.
    ///
    /// The frequency weight is 0.05 at `COLD`, 1 at `NORMAL` and 10 at `HOT`,
    /// clamped outside those, and log-log linear between them, i.e. a power
    /// of the frequency on each side of `NORMAL`.
    fn block_weight(loop_depth: usize, frequency: BlockFrequency) -> f64 {
        let f = f64::from(frequency.as_f32());
        let cold = f64::from(BlockFrequency::COLD.as_f32());
        let hot = f64::from(BlockFrequency::HOT.as_f32());
        let frequency_weight = if f <= cold {
            Self::COLD_WEIGHT
        } else if f >= hot {
            Self::HOT_WEIGHT
        } else if f < 1.0 {
            f.powf(Self::COLD_WEIGHT.ln() / cold.ln())
        } else {
            f.powf(Self::HOT_WEIGHT.ln() / hot.ln())
        };
        let depth = i32::try_from(loop_depth).unwrap_or(i32::MAX);
        Self::LOOP_WEIGHT.powi(depth) * frequency_weight
    }

    fn count_operands(&mut self, allocs: &[Allocation], weight: f64) {
        for alloc in allocs {
            match alloc {
                Allocation::Reg(_) => self.reg_operands += weight,
                Allocation::Stack(_) => self.stack_operands += weight,
            }
        }
    }

    fn total(&self) -> f64 {
        self.reg_operands
            + self.reg_moves
            + self.remats
            + Self::STACK_COST * (self.stack_operands + self.spills + self.reloads)
    }

    fn add(&mut self, other: &Self) {
        self.reg_operands += other.reg_operands;
        self.stack_operands += other.stack_operands;
        self.reg_moves += other.reg_moves;
        self.remats += other.remats;
        self.spills += other.spills;
        self.reloads += other.reloads;
    }
}

impl std::fmt::Display for EstimatedCycles {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "estimated-cycles {:.1}  reg-operands {:.1}  stack-operands {:.1}  moves {:.1}  \
             remats {:.1}  spills {:.1}  reloads {:.1}",
            self.total(),
            self.reg_operands,
            self.stack_operands,
            self.reg_moves,
            self.remats,
            self.spills,
            self.reloads,
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
        "options: validate {}, redundant-moves {}, dead-moves {}, dead-reg-moves {}, \
         narrow-slots {}",
        options.validate_input,
        level(options.redundant_move_elimination_level),
        level(options.dead_move_elimination_level),
        options.eliminate_dead_register_moves,
        options.narrow_spill_slot_live_ranges,
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
    narrow_spill_slot_live_ranges: Option<bool>,
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
            narrow_spill_slot_live_ranges: self
                .narrow_spill_slot_live_ranges
                .unwrap_or(from_file.narrow_spill_slot_live_ranges),
        }
    }
}

struct Args {
    paths: Vec<String>,
    options: OptionOverrides,
    check: bool,
    count_insts: bool,
    quiet: bool,
    profile: Option<Duration>,
}

impl Args {
    fn parse(args: impl Iterator<Item = String>) -> Result<Self, String> {
        let mut paths = vec![];
        let mut options = OptionOverrides::default();
        let mut check = false;
        let mut count_insts = false;
        let mut quiet = false;
        let mut profile = None;
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
                "--narrow-slots" => options.narrow_spill_slot_live_ranges = Some(true),
                "--no-narrow-slots" => options.narrow_spill_slot_live_ranges = Some(false),
                "--validate" => options.validate_input = Some(true),
                "--no-validate" => options.validate_input = Some(false),
                "--check" => check = true,
                "--insts" => count_insts = true,
                "-q" | "--quiet" => quiet = true,
                "--profile" => {
                    let value = value(&name)?;
                    let seconds = value
                        .parse::<f64>()
                        .ok()
                        .and_then(|s| Duration::try_from_secs_f64(s).ok())
                        .ok_or(format!("{name} wants a number of seconds, not `{value}`"))?;
                    profile = Some(seconds);
                }
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
            count_insts,
            quiet,
            profile,
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

/// Counting the instructions this process retires, which is far less noisy
/// than timing when comparing two builds of the allocator.
mod insts {
    pub struct InstsRetired(imp::State);

    impl InstsRetired {
        pub fn new() -> Result<Self, String> {
            imp::new().map(Self)
        }

        pub fn start(&mut self) {
            imp::start(&mut self.0);
        }

        /// The instructions retired since the last `start`.
        pub fn end(&mut self) -> u64 {
            imp::end(&mut self.0)
        }
    }

    #[cfg(target_os = "linux")]
    mod imp {
        use perf_event::{Builder, events::Hardware};

        pub use perf_event::Counter as State;

        pub fn new() -> Result<State, String> {
            Builder::new()
                .kind(Hardware::INSTRUCTIONS)
                .build()
                .map_err(|e| {
                    format!(
                        "could not create an INSTRUCTIONS hardware counter: {e}. Does this \
                         system have one? If it does, the kernel may not fully support this \
                         processor."
                    )
                })
        }

        pub fn start(counter: &mut State) {
            counter.reset().unwrap();
            counter.enable().unwrap();
        }

        pub fn end(counter: &mut State) -> u64 {
            counter.disable().unwrap();
            counter.read().unwrap()
        }
    }

    /// User space cannot read the PMU on macOS, but the kernel keeps a
    /// per-process count that `proc_pid_rusage` reads without sudo. It covers
    /// every thread, which is fine because the allocator runs on one.
    #[cfg(target_os = "macos")]
    mod imp {
        /// The count when the measurement started.
        pub type State = u64;

        pub fn new() -> Result<State, String> {
            Ok(0)
        }

        pub fn start(start: &mut State) {
            *start = read();
        }

        pub fn end(start: &mut State) -> u64 {
            read().wrapping_sub(*start)
        }

        fn read() -> u64 {
            // SAFETY: `rusage_info_v4` is plain old data for which all zeroes is
            // valid, and it is large enough for the `RUSAGE_INFO_V4` flavor
            // requested.
            let mut info: libc::rusage_info_v4 = unsafe { std::mem::zeroed() };
            let ret = unsafe {
                libc::proc_pid_rusage(
                    libc::getpid(),
                    libc::RUSAGE_INFO_V4,
                    &mut info as *mut libc::rusage_info_v4 as *mut libc::rusage_info_t,
                )
            };
            assert_eq!(ret, 0, "proc_pid_rusage failed");
            info.ri_instructions
        }
    }

    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    mod imp {
        pub type State = ();

        pub fn new() -> Result<State, String> {
            Err("counting instructions retired is only supported on Linux and macOS".to_string())
        }

        pub fn start(_: &mut State) {}

        pub fn end(_: &mut State) -> u64 {
            unreachable!()
        }
    }
}
