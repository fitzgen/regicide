//! Write a visualization of a small allocation to the given path.
//!
//! ```text
//! cargo run --example visualize --all-features -- /tmp/regicide.html
//! cargo run --example visualize --all-features -- -s 42 -i 200 /tmp/other.html
//! ```
//!
//! With no `--seed`, the function is the hand-written one below. It is small,
//! but not the smallest possible: six values are live at once on a
//! six-register machine, one operand has to be read off the stack, and a
//! block parameter carries a value along an edge. So the page has spans,
//! bundles, a spill slot, and edits to show rather than a straight line of
//! trivially satisfied constraints.
//!
//! With one, the function is a `regicide::test::TestInput` mutated `--iters`
//! times, which is how to go looking at allocations nobody wrote by hand.
//! `regicide::test` is not public API; the `visualizer` feature this example
//! requires is what exposes it.

use regicide::{
    Block, BlockFrequency, Context, DefUse, Entity, Error, Input, InputBlock, InputFunction,
    InputInst, InputOptions, InputValue, Inst, Machine, MachineBuilder, Operand, OperandConstraint,
    Position, RegClass, RegUnit, RematCost, SpillSlotSize, Val,
};
use std::{env, process};

const USAGE: &str = "\
usage: visualize [-s SEED] [-i ITERS] <path.html>

  -s, --seed SEED    seed a `mutatis::Session` and visualize a mutated
                     `TestInput` instead of the hand-written function
  -i, --iters ITERS  mutate it this many times (default 100)
  -h, --help         print this message";

/// How many times a mutated input is mutated when only `--seed` was given.
const DEFAULT_ITERS: u64 = 100;

fn main() {
    let args = match Args::parse(env::args().skip(1)) {
        Ok(args) => args,
        Err(message) => {
            eprintln!("{message}\n\n{USAGE}");
            process::exit(2);
        }
    };

    // Either flag means a mutated input; the two functions never meet, so the
    // page is written by one generic sink.
    if args.seed.is_none() && args.iters.is_none() {
        let (machine, rc) = machine();
        let func = function(rc);
        let options = InputOptions::default();
        emit(
            &Input {
                options: &options,
                machine: &machine,
                func: &func,
            },
            &args.path,
        );
        return;
    }

    // Always seeded explicitly: `Session::new()` otherwise draws from a
    // process-global counter, and a page worth keeping has to be one that can
    // be asked for again.
    let seed = args.seed.unwrap_or(0);
    let iters = args.iters.unwrap_or(DEFAULT_ITERS);
    eprintln!("mutating the default TestInput: seed {seed}, {iters} iterations");

    let mut input = regicide::test::TestInput::default();
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
                 try another --seed"
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
}

impl Args {
    /// Parse it, by hand rather than by adding a crate for three flags.
    fn parse(args: impl Iterator<Item = String>) -> Result<Self, String> {
        let mut path = None;
        let mut seed = None;
        let mut iters = None;
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
                _ if name.starts_with('-') => return Err(format!("unknown flag {name}")),
                _ if path.is_some() => return Err(format!("more than one path: {name}")),
                _ => path = Some(name),
            }
        }

        match path {
            Some(path) => Ok(Args { path, seed, iters }),
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

/// A machine with one bank of six allocatable registers, plus one the
/// allocator does not own so that the page has something to say about
/// non-allocatable registers.
fn machine() -> (Machine, RegClass) {
    let mut builder = MachineBuilder::new();
    let bank = builder
        .declare_reg_bank(SpillSlotSize::new(8).unwrap())
        .unwrap();

    let mut unit = 0;
    let mut reg = || {
        let start = RegUnit::try_new(unit).unwrap();
        unit += 1;
        let end = RegUnit::try_new(unit).unwrap();
        (start, end)
    };

    let mut define = |builder: &mut MachineBuilder| {
        let (start, end) = reg();
        builder.define_reg(bank, start..end).unwrap()
    };
    let r0 = define(&mut builder);
    let r1 = define(&mut builder);
    let r2 = define(&mut builder);
    let r3 = define(&mut builder);
    let r4 = define(&mut builder);
    let r5 = define(&mut builder);
    builder.define_non_allocatable_reg(bank).unwrap();

    let rc = builder
        .define_reg_class(bank, 1.0, [r0, r1, r2, r3, r4, r5])
        .unwrap();
    (builder.finish().unwrap(), rc)
}

/// ```text
/// block0:
///   v0 = op              ; inst0
///   ..                   ; six values, live at once
///   v5 = op              ; inst5
///   v6 = op [v0], v1     ; inst6 -- v0 must be read off the stack
///   v7 = op v2, v3       ; inst7
///   v8 = op v4, v5       ; inst8
///   v9 = op v6, v7       ; inst9
///   v10 = op v8, v9      ; inst10
///   br block1(v10)       ; inst11
///
/// block1(v11):
///   v12 = op v11         ; inst12
///   ret v12              ; inst13
/// ```
fn function(rc: RegClass) -> ExampleFunction {
    let val = |i| Val::try_new(i).unwrap();
    let inst = |i| Inst::try_new(i).unwrap();
    let block = |i| Block::try_new(i).unwrap();

    let def = |v| Operand::new(Position::Late, DefUse::Def, OperandConstraint::Reg(rc), v);
    let use_ = |v| Operand::new(Position::Early, DefUse::Use, OperandConstraint::Reg(rc), v);
    // One operand that has to be read off the stack, which is what gives the
    // page a spill slot and a reload to show.
    let stack_use = |v| Operand::new(Position::Early, DefUse::Use, OperandConstraint::Stack, v);
    let op = |block, out: Option<usize>, ins: &[usize]| ExampleInst {
        block,
        operands: out
            .map(|out| def(val(out)))
            .into_iter()
            .chain(ins.iter().map(|&i| use_(val(i))))
            .collect(),
    };

    let mut insts: Vec<ExampleInst> = (0..6).map(|v| op(block(0), Some(v), &[])).collect();
    insts.extend([
        ExampleInst {
            block: block(0),
            operands: vec![def(val(6)), stack_use(val(0)), use_(val(1))],
        },
        op(block(0), Some(7), &[2, 3]),
        op(block(0), Some(8), &[4, 5]),
        op(block(0), Some(9), &[6, 7]),
        op(block(0), Some(10), &[8, 9]),
        // The terminator, whose successors and block arguments live on the
        // block rather than on the instruction.
        op(block(0), None, &[]),
        op(block(1), Some(12), &[11]),
        op(block(1), None, &[12]),
    ]);

    ExampleFunction {
        values: vec![rc; 13],
        insts,
        blocks: vec![
            ExampleBlock {
                params: vec![],
                insts: (0..12).map(inst).collect(),
                successors: vec![(block(1), vec![val(10)])],
                predecessors: vec![],
                idom: None,
            },
            ExampleBlock {
                params: vec![val(11)],
                insts: (12..14).map(inst).collect(),
                successors: vec![],
                predecessors: vec![block(0)],
                idom: Some(block(0)),
            },
        ],
    }
}

/// The function, as three flat tables indexed by entity.
pub struct ExampleFunction {
    /// Each value's natural register class.
    values: Vec<RegClass>,

    /// Each block, in index order.
    blocks: Vec<ExampleBlock>,

    /// Each instruction, in index order. A block's instructions are one
    /// contiguous run, which the allocator requires.
    insts: Vec<ExampleInst>,
}

struct ExampleBlock {
    params: Vec<Val>,
    insts: Vec<Inst>,
    successors: Vec<(Block, Vec<Val>)>,
    predecessors: Vec<Block>,
    idom: Option<Block>,
}

struct ExampleInst {
    block: Block,
    operands: Vec<Operand>,
}

/// A block, paired with the function it lives in, since the traits hand out
/// borrows rather than indices.
#[derive(Clone, Copy)]
pub struct ExampleBlockRef<'a> {
    func: &'a ExampleFunction,
    block: Block,
}

/// An instruction, paired with its function.
#[derive(Clone, Copy)]
pub struct ExampleInstRef<'a> {
    func: &'a ExampleFunction,
    inst: Inst,
}

/// A value, paired with its function.
#[derive(Clone, Copy)]
pub struct ExampleValueRef<'a> {
    func: &'a ExampleFunction,
    val: Val,
}

// The iterators are boxed to keep the example short. A real embedder names
// concrete types here, so that iterating a block's instructions does not
// allocate.
type Iter<'a, T> = Box<dyn Iterator<Item = T> + 'a>;
type DoubleEndedIter<'a, T> = Box<dyn DoubleEndedIterator<Item = T> + 'a>;

impl InputFunction for ExampleFunction {
    type InputBlock<'a> = ExampleBlockRef<'a>;
    type InputInst<'a> = ExampleInstRef<'a>;
    type InputValue<'a> = ExampleValueRef<'a>;

    fn len_values(&self) -> usize {
        self.values.len()
    }

    type ValuesIter<'a> = Iter<'a, (Val, ExampleValueRef<'a>)>;

    fn values(&self) -> Self::ValuesIter<'_> {
        Box::new(
            (0..self.values.len())
                .map(Val::try_new)
                .map(move |val| (val.unwrap(), self.value(val.unwrap()))),
        )
    }

    fn value(&self, val: Val) -> Self::InputValue<'_> {
        ExampleValueRef { func: self, val }
    }

    fn len_insts(&self) -> usize {
        self.insts.len()
    }

    fn inst(&self, inst: Inst) -> Self::InputInst<'_> {
        ExampleInstRef { func: self, inst }
    }

    fn entry_block(&self) -> Block {
        Block::try_new(0).unwrap()
    }

    fn len_blocks(&self) -> usize {
        self.blocks.len()
    }

    fn block(&self, block: Block) -> Self::InputBlock<'_> {
        ExampleBlockRef { func: self, block }
    }

    type BlocksIter<'a> = Iter<'a, (Block, ExampleBlockRef<'a>)>;

    fn blocks(&self) -> Self::BlocksIter<'_> {
        Box::new((0..self.blocks.len()).map(move |i| {
            let block = Block::try_new(i).unwrap();
            (block, self.block(block))
        }))
    }
}

impl<'a> ExampleBlockRef<'a> {
    fn data(&self) -> &'a ExampleBlock {
        &self.func.blocks[self.block.index()]
    }
}

impl<'a> InputBlock<'a> for ExampleBlockRef<'a> {
    type InputInst<'b>
        = ExampleInstRef<'b>
    where
        Self: 'b;

    fn block(&self) -> Block {
        self.block
    }

    fn frequency(&self) -> BlockFrequency {
        BlockFrequency::NORMAL
    }

    fn len_insts(&self, _block: Block) -> usize {
        self.data().insts.len()
    }

    type InstsIter<'b>
        = DoubleEndedIter<'b, (Inst, ExampleInstRef<'b>)>
    where
        Self: 'b;

    fn insts(&self) -> Self::InstsIter<'_> {
        let func = self.func;
        Box::new(
            self.data()
                .insts
                .iter()
                .copied()
                .map(move |inst| (inst, func.inst(inst))),
        )
    }

    fn len_params(&self) -> usize {
        self.data().params.len()
    }

    type ParamsIter<'b>
        = std::iter::Copied<std::slice::Iter<'b, Val>>
    where
        Self: 'b;

    fn params(&self) -> Self::ParamsIter<'_> {
        self.data().params.iter().copied()
    }

    fn immediate_dominator(&self) -> Option<Block> {
        self.data().idom
    }

    fn dominates(&self, other: Block) -> bool {
        // Walking the immediate-dominator chain is fine at this size; a real
        // embedder answers this from its dominator tree in constant time.
        let mut at = Some(other);
        while let Some(block) = at {
            if block == self.block {
                return true;
            }
            at = self.func.blocks[block.index()].idom;
        }
        false
    }

    fn len_successors(&self) -> usize {
        self.data().successors.len()
    }

    type SuccessorsIter<'b>
        = Iter<'b, Block>
    where
        Self: 'b;

    fn successors(&self) -> Self::SuccessorsIter<'_> {
        Box::new(self.data().successors.iter().map(|(block, _)| *block))
    }

    fn len_predecessors(&self) -> usize {
        self.data().predecessors.len()
    }

    type PredecessorsIter<'b>
        = std::iter::Copied<std::slice::Iter<'b, Block>>
    where
        Self: 'b;

    fn predecessors(&self) -> Self::PredecessorsIter<'_> {
        self.data().predecessors.iter().copied()
    }

    fn len_successor_block_args(&self, i: usize) -> usize {
        self.data().successors[i].1.len()
    }

    type SuccessorBlockArgsIter<'b>
        = std::iter::Copied<std::slice::Iter<'b, Val>>
    where
        Self: 'b;

    fn successor_block_args(&self, successor: usize) -> Self::SuccessorBlockArgsIter<'_> {
        self.data().successors[successor].1.iter().copied()
    }
}

impl<'a> InputInst<'a> for ExampleInstRef<'a> {
    fn inst(&self) -> Inst {
        self.inst
    }

    fn operands_len(&self) -> usize {
        self.func.insts[self.inst.index()].operands.len()
    }

    type OperandsIter<'b>
        = std::iter::Copied<std::slice::Iter<'b, Operand>>
    where
        Self: 'b;

    fn operands(&self) -> Self::OperandsIter<'_> {
        self.func.insts[self.inst.index()].operands.iter().copied()
    }

    fn operand(&self, i: usize) -> Operand {
        self.func.insts[self.inst.index()].operands[i]
    }

    fn block(&self) -> Block {
        self.func.insts[self.inst.index()].block
    }
}

impl<'a> InputValue<'a> for ExampleValueRef<'a> {
    fn val(&self) -> Val {
        self.val
    }

    fn remat_cost(&self) -> Option<RematCost> {
        None
    }

    fn reg_class(&self) -> RegClass {
        self.func.values[self.val.index()]
    }
}
