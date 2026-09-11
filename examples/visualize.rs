//! Write a visualization of a small allocation to the given path.
//!
//! ```text
//! cargo run --example visualize --all-features -- /tmp/regicide.html
//! cargo run --example visualize --all-features -- -s 42 -i 200 /tmp/other.html
//! cargo run --example visualize --all-features -- -r 8 /tmp/roomy.html
//! ```
//!
//! The function is always a `regicide::test::TestInput`, mutated `--iters`
//! times by a `mutatis::Session` seeded with `--seed`: the point of the page
//! is to go looking at allocations nobody wrote by hand, and one function
//! written out longhand here would only ever be the one function.
//! `regicide::test` is not public API; the `visualizer` feature this example
//! requires is what exposes it.
//!
//! Both flags default, so the bare invocation above is a particular page and
//! not a random one, and any page can be asked for again by repeating the two
//! numbers printed to stderr.

use regicide::{
    Context, Error, Input, InputFunction,
    test::{TestInput, TestMachine},
};
use std::{env, process};

const USAGE: &str = "\
usage: visualize [-s SEED] [-i ITERS] [-r REGS] <path.html>

  -s, --seed SEED    seed the `mutatis::Session` that mutates the input
                     (default 21)
  -i, --iters ITERS  mutate it this many times (default 100); 0 means the
                     unmutated default `TestInput`
  -r, --regs REGS    give every register bank this many registers, keeping
                     the machine's shape; 1 to 64, and a two-bank machine
                     ends up with twice as many (default: whatever the
                     mutations produced, which is at most four per bank)
  -h, --help         print this message";

/// The seed the page is built with when `--seed` was not given.
///
/// Chosen by trying the small ones: a mutated input is as likely to be a
/// single instruction as anything else, and this one comes out with two
/// blocks, three spill slots, moves, and twenty-eight distinct event kinds --
/// enough of the allocator's machinery that every pane has something to draw.
const DEFAULT_SEED: u64 = 21;

/// How many times the input is mutated when `--iters` was not given.
const DEFAULT_ITERS: u64 = 100;

fn main() {
    let args = match Args::parse(env::args().skip(1)) {
        Ok(args) => args,
        Err(message) => {
            eprintln!("{message}\n\n{USAGE}");
            process::exit(2);
        }
    };

    // Always seeded explicitly: `Session::new()` otherwise draws from a
    // process-global counter, and a page worth keeping has to be one that can
    // be asked for again.
    let seed = args.seed.unwrap_or(DEFAULT_SEED);
    let iters = args.iters.unwrap_or(DEFAULT_ITERS);
    let regs = match args.regs {
        Some(regs) => format!("{regs} regs per bank"),
        None => "generated registers".to_string(),
    };
    eprintln!("mutating the default TestInput: seed {seed}, {iters} iterations, {regs}");

    let mut input = TestInput::default();
    // Before the mutations rather than after, so the input is built against
    // the machine it will be allocated on. The count lives on the machine, so
    // each mutation's `fixup` re-applies it rather than undoing it.
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
    input.with_input(|input| emit(input, &args.path));
}

/// Allocate registers for `input` and write the page.
///
/// Generic, because `InputFunction` has GATs and is not object-safe; the
/// signature mirrors `regicide::run`'s own.
fn emit(input: &Input<'_, impl InputFunction>, path: &str) {
    let mut context = Context::new();
    let output = match regicide::run(&mut context, input) {
        Ok(output) => output,
        // The one failure a mutated input reaches often: `TestMachine` has at
        // most two banks of four registers, and nothing keeps a mutation from
        // asking for more at one point.
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

/// The command line.
struct Args {
    path: String,
    seed: Option<u64>,
    iters: Option<u64>,
    regs: Option<usize>,
}

impl Args {
    /// Parse it, by hand rather than by adding a crate for three flags.
    fn parse(args: impl Iterator<Item = String>) -> Result<Self, String> {
        let mut path = None;
        let mut seed = None;
        let mut iters = None;
        let mut regs = None;
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
                "-s" | "--seed" => seed = Some(number(&name, &value(&name)?)?),
                "-i" | "--iters" => iters = Some(number(&name, &value(&name)?)?),
                "-r" | "--regs" => {
                    // Range-checked here rather than left to
                    // `set_regs_per_bank`'s assertion: a number out of range
                    // is the user's typo, and a panic is a poor way to say so.
                    let n = number(&name, &value(&name)?)?;
                    let most = TestMachine::MAX_REGS_PER_BANK_TARGET;
                    // Through `try_from`, so that a number too large for a
                    // `usize` is this message rather than a panic.
                    let within = usize::try_from(n).is_ok_and(|n| (1..=most).contains(&n));
                    if !within {
                        return Err(format!("{name} wants 1 to {most} registers, not {n}"));
                    }
                    regs = Some(usize::try_from(n).unwrap());
                }
                _ if name.starts_with('-') => return Err(format!("unknown flag {name}")),
                _ if path.is_some() => return Err(format!("more than one path: {name}")),
                _ => path = Some(name),
            }
        }

        match path {
            Some(path) => Ok(Args {
                path,
                seed,
                iters,
                regs,
            }),
            None => Err("no output path".to_string()),
        }
    }
}

/// One flag's value as an integer.
fn number(flag: &str, value: &str) -> Result<u64, String> {
    value
        .parse()
        .map_err(|_| format!("{flag} wants a non-negative integer, not `{value}`"))
}
