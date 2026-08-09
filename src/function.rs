use crate::entity::{Block, EntityRepr, Inst, Val};

/// TODO FITZGEN
pub struct Operand<E = u32>
where
    E: EntityRepr,
{
    val: Val<E>,
}

/// A function: the input to register allocation.
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

    /// Get the cost of rematerializing the given value, if possible.
    ///
    /// TODO: expand this
    fn remat_cost(&self, val: Val) -> Option<RematCost>;

    /// The number of basic blocks defined in this function.
    fn len_blocks(&self) -> usize;

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
    type InstsIter<'b>: Iterator<Item = (Inst, Self::InputInst<'b>)>
    where
        Self: 'b;

    /// Get an iterator over all instructions within a block.
    fn insts(&self) -> Self::InstsIter<'_>;

    /// Get the given block's immediate dominator, or `None` if this is the
    /// function entry block (i.e. the root of the dominator tree).
    fn immediate_dominator(&self) -> Option<Block>;

    /// Does this block dominate the `other` block?
    fn dominates(&self, other: Block) -> bool;

    /// How many successors does this block have in the control-flow graph?
    fn len_successors(&self) -> usize;

    /// The iterator type returned by [`InputBlock::successors`].
    type SuccessorsIter<'b>: Iterator<Item = Block>
    where
        Self: 'b;

    /// Get an iterator over the successors of this block.
    fn successors(&self) -> Self::SuccessorsIter<'_>;

    /// The number of block arguments in the `i`th successor edge.
    ///
    /// The `i`th block must have exactly this many block parameters, or the
    /// input is invalid.
    fn len_successor_block_args(&self, i: usize) -> usize;

    /// The iterator type returned by [`InputBlock::successor_block_args`].
    type SuccessorBlockArgsIter<'b>: Iterator<Item = Val>
    where
        Self: 'b;

    /// Get the block arguments passed to this block's `i`th successor.
    fn successor_block_args(&self, successor: usize) -> Self::SuccessorBlockArgsIter<'_>;

    // TODO: ...
}

/// An instruction in a [`InputBlock`].
pub trait InputInst<'a> {}

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
