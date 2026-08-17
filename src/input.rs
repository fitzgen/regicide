use core::{cell::RefCell, fmt};

use crate::{
    Allocation, Machine, Output, Reg,
    dfs::Dfs,
    entity::{Block, EntityRepr, Inst, PrimaryMap, Val},
    error::IResult,
    output::OutputInner,
};

/// The input to register allocation.
pub struct Input<'a, F>
where
    F: InputFunction,
{
    /// Register allocation options.
    pub options: &'a InputOptions,

    /// The description of the machine whose registers we are allocating.
    pub machine: &'a Machine,

    /// The function to allocate registers for.
    pub func: &'a F,
}

/// Register allocation options.
#[derive(Clone, Debug)]
pub struct InputOptions {
    /// Should the register allocator check that the given input is valid?
    ///
    /// Checks that the function is valid SSA, defs dominate uses, single def
    /// per value, block arguments and params match, etc...
    ///
    /// If this option is enabled and you pass invalid input to register
    /// allocation, an error is returned.  If this is disabled and you pass
    /// invalid input to register allocation, you might get panics or silently
    /// incorrect results.
    ///
    /// This option is enabled by default when `cfg!(debug_assertions)`.
    pub validate_input: bool,
}

impl Default for InputOptions {
    fn default() -> Self {
        Self::new()
    }
}

impl InputOptions {
    /// Default register allocation options.
    pub const fn new() -> Self {
        Self {
            validate_input: cfg!(debug_assertions),
        }
    }
}

/// TODO FITZGEN
#[derive(Clone, Debug, Hash)]
#[cfg_attr(any(test, fuzz), derive(mutatis::Mutate))]
pub struct Operand<E = u32>
where
    E: EntityRepr,
{
    /// TODO FITZGEN
    pub pos: Position,
    /// TODO FITZGEN
    pub kind: DefUse,
    /// TODO FITZGEN
    pub val: Val<E>,
}

/// TODO FITZGEN
#[derive(Clone, Debug, Hash)]
#[cfg_attr(any(test, fuzz), derive(mutatis::Mutate))]
#[repr(u8)]
pub enum Position {
    /// TODO FITZGEN
    Early = 0,
    /// TODO FITZGEN
    Late = 1,
}

/// TODO FITZGEN
#[derive(Clone, Debug, Hash)]
#[cfg_attr(any(test, fuzz), derive(mutatis::Mutate))]
#[repr(u8)]
pub enum DefUse {
    /// TODO FITZGEN
    Def = 0,
    /// TODO FITZGEN
    Use = 1,
}

/// A function that needs register allocation.
pub trait InputFunction {
    /// The associated input block type.
    type InputBlock<'a>: InputBlock<'a, InputInst<'a> = Self::InputInst<'a>>
    where
        Self: 'a;

    /// The associated input instruction type.
    type InputInst<'a>: InputInst<'a>
    where
        Self: 'a;

    /// The number of values defined in this function.
    fn len_values(&self) -> usize;

    /// The iterator type returned by [`InputFunction::values`].
    type ValuesIter<'a>: Iterator<Item = Val>
    where
        Self: 'a;

    /// An iterator over the values defined in this function.
    fn values(&self) -> Self::ValuesIter<'_>;

    /// Get the cost of rematerializing the given value, if possible.
    ///
    /// TODO: expand this
    fn remat_cost(&self, val: Val) -> Option<RematCost>;

    /// The function's entry block.
    fn entry_block(&self) -> Block;

    /// The number of basic blocks defined in this function.
    fn len_blocks(&self) -> usize;

    /// The number of instructions defined in this function.
    fn len_insts(&self) -> usize;

    /// Get the given input block.
    fn block(&self, block: Block) -> Self::InputBlock<'_>;

    /// The iterator type returned by [`Function::blocks`].
    type BlocksIter<'a>: Iterator<Item = (Block, Self::InputBlock<'a>)>
    where
        Self: 'a;

    /// Get an iterator over all blocks in this function.
    ///
    /// TODO: rpo?
    fn blocks(&self) -> Self::BlocksIter<'_>;

    /// Get a `Display` implementation that prints this `InputFunction`.
    fn display(&self) -> DisplayInputFunction<'_, Self> {
        DisplayInputFunction(self)
    }
}

/// A block in an [`InputFunction`].
pub trait InputBlock<'a> {
    /// The associated input instruction type.
    type InputInst<'b>: InputInst<'b>
    where
        Self: 'b;

    /// The number of instructions in the given block.
    fn len_insts(&self, block: Block) -> usize;

    /// The iterator type returned by [`InputBlock::insts`].
    ///
    /// This is double-ended because backwards analyses, such as liveness, walk
    /// a block's instructions in reverse.
    type InstsIter<'b>: DoubleEndedIterator<Item = (Inst, Self::InputInst<'b>)>
    where
        Self: 'b;

    /// Get an iterator over all instructions within a block.
    ///
    /// Instructions within a block must be numbered contiguously, in the order
    /// that they are yielded here: each instruction's index must be exactly one
    /// more than the index of the instruction before it. An instruction's index
    /// therefore gives its position within its block, and one instruction comes
    /// before another exactly when its index is smaller.
    ///
    /// A given instruction must only appear within one block. Together with the
    /// above, this means that the blocks carve the instruction index space into
    /// disjoint runs.
    ///
    /// A block must always have at least one instruction: its terminator.
    fn insts(&self) -> Self::InstsIter<'_>;

    /// The number of parameters that this block takes.
    ///
    /// Every control-flow edge into this block must pass exactly this many
    /// block arguments, or the input is invalid. See
    /// [`InputBlock::len_successor_block_args`], which is the other half of
    /// this contract.
    fn len_params(&self) -> usize;

    /// The iterator type returned by [`InputBlock::params`].
    type ParamsIter<'b>: Iterator<Item = Val>
    where
        Self: 'b;

    /// Get this block's parameters.
    ///
    /// A parameter is defined upon entry to its block, and therefore its
    /// definition dominates every instruction in the block.
    fn params(&self) -> Self::ParamsIter<'_>;

    /// Get the given block's immediate dominator, or `None` if this is the
    /// function entry block (i.e. the root of the dominator tree).
    ///
    /// This is also `None` for blocks that are not reachable from the entry
    /// block, which are not part of the dominator tree at all.
    fn immediate_dominator(&self) -> Option<Block>;

    /// Does this block dominate the `other` block?
    ///
    /// That is, must every control-flow path from the function entry to `other`
    /// go through this block?
    ///
    /// This is reflexive: a block always dominates itself.
    ///
    /// Dominance is ill-defined for blocks that are not reachable from the entry
    /// block, and the result is unspecified when either block is unreachable.
    fn dominates(&self, other: Block) -> bool;

    /// How many successors does this block have in the control-flow graph?
    fn len_successors(&self) -> usize;

    /// The iterator type returned by [`InputBlock::successors`].
    type SuccessorsIter<'b>: Iterator<Item = Block>
    where
        Self: 'b;

    /// Get an iterator over the successors of this block.
    fn successors(&self) -> Self::SuccessorsIter<'_>;

    /// How many predecessors does this block have in the control-flow graph?
    fn len_predecessors(&self) -> usize;

    /// The iterator type returned by [`InputBlock::predecessors`].
    type PredecessorsIter<'b>: Iterator<Item = Block>
    where
        Self: 'b;

    /// Get an iterator over the predecessors of this block.
    ///
    /// This yields one entry per incoming control-flow edge, just as
    /// [`InputBlock::successors`] yields one per outgoing edge, so a block that
    /// branches to the same target twice appears twice in that target's
    /// predecessors.
    ///
    /// These must be the exact reverse of the successor edges: for every block
    /// `a` and every time that `a.successors()` yields `b`, `b.predecessors()`
    /// must yield `a`, and vice versa. Otherwise the input is invalid.
    fn predecessors(&self) -> Self::PredecessorsIter<'_>;

    /// The number of block arguments in the `i`th successor edge.
    ///
    /// The `i`th successor block must have exactly this many block parameters,
    /// or the input is invalid. That is, this must always equal
    /// `self.successors().nth(i).len_params()`.
    fn len_successor_block_args(&self, i: usize) -> usize;

    /// The iterator type returned by [`InputBlock::successor_block_args`].
    type SuccessorBlockArgsIter<'b>: Iterator<Item = Val>
    where
        Self: 'b;

    /// Get the block arguments passed to this block's `i`th successor.
    fn successor_block_args(&self, successor: usize) -> Self::SuccessorBlockArgsIter<'_>;

    // TODO: ...
}

pub struct RegSet {
    // TODO FITZGEN: representation?
}

/// An instruction in a [`InputBlock`].
pub trait InputInst<'a> {
    /// TODO FITZGEN
    fn operands_len(&self) -> usize;

    /// TODO FITZGEN
    type OperandsIter<'b>: Iterator<Item = Operand>
    where
        Self: 'b;

    /// TODO FITZGEN
    fn operands(&self) -> Self::OperandsIter<'_>;

    /// TODO FITZGEN
    fn operand(&self, i: usize) -> Operand;

    /// TODO FITZGEN
    fn clobbers(&self) -> RegSet;
}

/// The cost of rematerializing a value, rather than shuffling it between
/// registers or reloading it from a spill slot.
pub enum RematCost {
    /// Always rematerialize this value on demand.
    ///
    /// Eagerly split its live range bundle to minimal ranges. It should never
    /// be shuffled between registers or spilled.
    AlwaysRemat = 0,

    /// When its operands are already available, rematerializing this value is
    /// cheaper than keeping it alive in a register and moving it around.
    CheaperThanMove = 1,

    /// When its operands are already available, rematerializing this value is
    /// cheaper than reloading it from a spill slot, but not cheaper than
    /// shuffling it between registers.
    CheaperThanReload = 2,
}

/// A trait for formatting something, optionally with the result of register
/// allocation.
pub(crate) trait FmtWithOutput<E>
where
    E: EntityRepr,
{
    /// Format `self` into `f`, optionally adding extra information from
    /// `output` if present.
    fn fmt_with_output(
        &self,
        f: &mut fmt::Formatter<'_>,
        output: &mut OutputInner<E>,
    ) -> IResult<()>;
}

/// Adapt a `FmtWithOutput` into a `Display` that formats with a particular
/// output, rather than with an empty scratch output.
pub(crate) struct DisplayWithOutput<'a, T, E>
where
    E: EntityRepr,
{
    value: T,
    output: RefCell<&'a mut OutputInner<E>>,
}

impl<'a, T, E> DisplayWithOutput<'a, T, E>
where
    E: EntityRepr,
{
    /// Format `value` with `output`.
    pub(crate) fn new(value: T, output: &'a mut OutputInner<E>) -> Self {
        Self {
            value,
            output: RefCell::new(output),
        }
    }
}

impl<T, E> fmt::Display for DisplayWithOutput<'_, T, E>
where
    T: FmtWithOutput<E>,
    E: EntityRepr,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut output = self.output.borrow_mut();
        match self.value.fmt_with_output(f, &mut output) {
            Ok(()) => Ok(()),
            Err(()) => {
                let _ = output.take_error();
                Err(fmt::Error)
            }
        }
    }
}

impl<F> fmt::Display for Input<'_, F>
where
    F: InputFunction,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut output = OutputInner::<u32>::new();
        match self.fmt_with_output(f, &mut output) {
            Ok(()) => Ok(()),
            Err(()) => {
                let _ = fmt::Debug::fmt(&output.take_error(), f);
                Err(fmt::Error)
            }
        }
    }
}

impl<E, F> FmtWithOutput<E> for Input<'_, F>
where
    E: EntityRepr,
    F: InputFunction,
{
    fn fmt_with_output(
        &self,
        f: &mut fmt::Formatter<'_>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        output.result(writeln!(f, "Options: {:#?}", self.options))?;
        output.result(writeln!(f, "Machine: {:#?}", self.machine))?;

        DisplayInputFunction(self.func).fmt_with_output(f, output)
    }
}

/// TODO FITZGEN
pub struct DisplayInputFunction<'a, F>(&'a F)
where
    F: ?Sized;

impl<F> fmt::Display for DisplayInputFunction<'_, F>
where
    F: InputFunction,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut output = OutputInner::<u32>::new();
        match self.fmt_with_output(f, &mut output) {
            Ok(()) => Ok(()),
            Err(()) => {
                let _ = fmt::Debug::fmt(&output.take_error(), f);
                Err(fmt::Error)
            }
        }
    }
}

impl<E, F> FmtWithOutput<E> for DisplayInputFunction<'_, F>
where
    E: EntityRepr,
    F: InputFunction,
{
    fn fmt_with_output(
        &self,
        f: &mut fmt::Formatter<'_>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        output.result(writeln!(f, "Function {{"))?;
        {
            let entry = self.0.entry_block();
            for (block, input_block) in self.0.blocks() {
                output.result(write!(f, "  "))?;
                if block == entry {
                    output.result(write!(f, "entry "))?;
                }
                output.result(write!(f, "{block:?}"))?;
                fmt_val_list(f, output, input_block.params())?;
                output.result(writeln!(f, ":"))?;
                DisplayInputBlock(input_block).fmt_with_output(f, output)?;
                output.result(writeln!(f))?;
            }
        }
        output.result(writeln!(f, "}}"))
    }
}

/// TODO FITZGEN
pub struct DisplayInputBlock<B>(B);

impl<'a, E, B> FmtWithOutput<E> for DisplayInputBlock<B>
where
    E: EntityRepr,
    B: InputBlock<'a>,
{
    fn fmt_with_output(
        &self,
        f: &mut fmt::Formatter<'_>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        for (inst, input_inst) in self.0.insts() {
            output.result(writeln!(f, "    {inst:?}"))?;
            for arg in input_inst.operands() {
                output.result(write!(f, "      "))?;
                match arg.pos {
                    Position::Early => output.result(write!(f, "early "))?,
                    Position::Late => output.result(write!(f, "late "))?,
                }
                match arg.kind {
                    DefUse::Def => output.result(write!(f, "def "))?,
                    DefUse::Use => output.result(write!(f, "use "))?,
                }
                output.result(writeln!(f, "{:?}", arg.val))?;
            }
        }
        if self.0.len_successors() == 0 {
            output.result(writeln!(f, "    --> returns"))?;
        } else {
            for (i, block) in self.0.successors().enumerate() {
                output.result(write!(f, "    --> {block:?}"))?;
                fmt_val_list(f, output, self.0.successor_block_args(i))?;
                output.result(writeln!(f))?;
            }
        }
        Ok(())
    }
}

/// Format a parenthesized, comma-separated list of values, or nothing at all
/// when the list is empty.
fn fmt_val_list<E>(
    f: &mut fmt::Formatter<'_>,
    output: &mut OutputInner<E>,
    vals: impl Iterator<Item = Val>,
) -> IResult<()>
where
    E: EntityRepr,
{
    let mut vals = vals.peekable();
    if vals.peek().is_none() {
        return Ok(());
    }
    output.result(write!(f, "("))?;
    for (i, val) in vals.enumerate() {
        if i > 0 {
            output.result(write!(f, ", "))?;
        }
        output.result(write!(f, "{val:?}"))?;
    }
    output.result(write!(f, ")"))
}
