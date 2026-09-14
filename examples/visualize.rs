//! Write a visualization of a small allocation to the given path.
//!
//! ```text
//! cargo run --example visualize --all-features -- /tmp/regicide.html
//! cargo run --example visualize --all-features -- -s 42 -i 200 /tmp/other.html
//! cargo run --example visualize --all-features -- -r 8 /tmp/roomy.html
//! ```

use regicide::{
    Context, Error, Input, InputFunction,
    deserialize::DeserializedInput,
    serialize::SerializeInput,
    test::{TestInput, TestMachine},
};
use std::{
    env,
    fs::File,
    io::{BufReader, BufWriter},
    process,
};

const USAGE: &str = "\
usage: visualize [-s SEED] [-i ITERS] [-r REGS] [-d FILE] <path.html>
       visualize --input FILE <path.html>

  -s, --seed SEED    seed the `mutatis::Session` that mutates the input
                     (default 21)
  -i, --iters ITERS  mutate it this many times (default 100); 0 means the
                     unmutated default `TestInput`
  -r, --regs REGS    give every register bank this many registers, keeping
                     the machine's shape; 1 to 64, and a two-bank machine
                     ends up with twice as many (default: whatever the
                     mutations produced, which is at most four per bank)
  -d, --dump FILE    write the input to FILE, as JSON, before allocating
      --input FILE   read the input from FILE instead of generating one,
                     which rules out -s, -i and -r
  -h, --help         print this message";

const DEFAULT_SEED: u64 = 21;
const DEFAULT_ITERS: u64 = 100;

fn main() {
    let args = match Args::parse(env::args().skip(1)) {
        Ok(args) => args,
        Err(message) => {
            eprintln!("{message}\n\n{USAGE}");
            process::exit(2);
        }
    };

    if let Some(path) = &args.input {
        let input = load(path);
        // No closure, unlike the generated path: a `DeserializedInput` owns
        // its machine, so `as_input` can borrow everything from it.
        emit(&input.as_input(), &args.path);
        return;
    }

    let seed = args.seed.unwrap_or(DEFAULT_SEED);
    let iters = args.iters.unwrap_or(DEFAULT_ITERS);
    let regs = match args.regs {
        Some(regs) => format!("{regs} regs per bank"),
        None => "generated registers".to_string(),
    };
    eprintln!("mutating the default TestInput: seed {seed}, {iters} iterations, {regs}");

    let mut input = TestInput::default();
    if let Some(regs) = args.regs {
        input.machine.set_regs_per_bank(regs);
        input.fixup();
    }
    let mut session = mutatis::Session::new().seed(seed);
    for i in 0..iters {
        if let Err(e) = session.mutate(&mut input) {
            eprintln!("mutation {i} failed: {e}");
            process::exit(1);
        }
    }
    input.with_input(|input| {
        if let Some(path) = &args.dump {
            dump(input, path);
        }
        emit(input, &args.path);
    });
}

/// Write `input` to `path` as JSON, for a later `--input` run.
fn dump(input: &Input<'_, impl InputFunction>, path: &str) {
    let write = || -> Result<(), String> {
        let file = File::create(path).map_err(|e| e.to_string())?;
        serde_json::to_writer(BufWriter::new(file), &SerializeInput::new(input))
            .map_err(|e| e.to_string())
    };
    if let Err(e) = write() {
        eprintln!("could not write {path}: {e}");
        process::exit(1);
    }
    println!("wrote {path}");
}

/// Read back what `dump` wrote.
fn load(path: &str) -> DeserializedInput {
    let read = || -> Result<DeserializedInput, String> {
        let file = File::open(path).map_err(|e| e.to_string())?;
        serde_json::from_reader(BufReader::new(file)).map_err(|e| e.to_string())
    };
    match read() {
        Ok(input) => input,
        Err(e) => {
            eprintln!("could not read {path}: {e}");
            process::exit(1);
        }
    }
}

/// Allocate registers for `input` and write the page.
fn emit(input: &Input<'_, impl InputFunction>, path: &str) {
    let mut context = Context::new();
    let output = match regicide::run(&mut context, input) {
        Ok(output) => output,
        Err(Error::TooManyLiveRegs) => {
            eprintln!(
                "this input needs more registers at one point than its machine has; \
                 try another --seed, or more --regs"
            );
            process::exit(1);
        }
        Err(e) => {
            eprintln!("register allocation failed: {e}");
            process::exit(1);
        }
    };

    if let Err(e) = output.write_visualization_html(input, path) {
        eprintln!("could not write {path}: {e}");
        process::exit(1);
    }

    println!("wrote {path}");
}

struct Args {
    path: String,
    seed: Option<u64>,
    iters: Option<u64>,
    regs: Option<usize>,
    dump: Option<String>,
    input: Option<String>,
}

impl Args {
    fn parse(args: impl Iterator<Item = String>) -> Result<Self, String> {
        let mut path = None;
        let mut seed = None;
        let mut iters = None;
        let mut regs = None;
        let mut dump = None;
        let mut input = None;
        let mut args = args.peekable();

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
                "-s" | "--seed" => seed = Some(parse_u64(&name, &value(&name)?)?),
                "-i" | "--iters" => iters = Some(parse_u64(&name, &value(&name)?)?),
                "-r" | "--regs" => {
                    let n = parse_u64(&name, &value(&name)?)?;
                    let most = TestMachine::MAX_REGS_PER_BANK_TARGET;
                    let within = usize::try_from(n).is_ok_and(|n| (1..=most).contains(&n));
                    if !within {
                        return Err(format!("{name} wants 1 to {most} registers, not {n}"));
                    }
                    regs = Some(usize::try_from(n).unwrap());
                }
                "-d" | "--dump" => dump = Some(value(&name)?),
                "--input" => input = Some(value(&name)?),
                _ if name.starts_with('-') => return Err(format!("unknown flag {name}")),
                _ if path.is_some() => return Err(format!("more than one path: {name}")),
                _ => path = Some(name),
            }
        }

        // Rejected rather than ignored: a generation flag beside --input
        // asks for an input that is not the one being read.
        if input.is_some() {
            let generating = [("-s", seed.is_some()), ("-i", iters.is_some())]
                .into_iter()
                .chain([("-r", regs.is_some())])
                .find_map(|(name, given)| given.then_some(name));
            if let Some(name) = generating {
                return Err(format!("--input reads an input, so it rules out {name}"));
            }
        }

        match path {
            Some(path) => Ok(Args {
                path,
                seed,
                iters,
                regs,
                dump,
                input,
            }),
            None => Err("no output path".to_string()),
        }
    }
}

fn parse_u64(flag: &str, value: &str) -> Result<u64, String> {
    value
        .parse()
        .map_err(|_| format!("{flag} wants a non-negative integer, not `{value}`"))
}
