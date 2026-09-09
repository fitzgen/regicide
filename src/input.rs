use core::{cell::RefCell, fmt, marker::PhantomData};

use crate::{
    Machine, RegClass, RegSet,
    context::ContextInner,
    entity::{Block, Entity as _, EntityRepr, Inst, Val},
    error::IResult,
    live_ranges::MAX_OPERANDS_PER_INST,
    machine::RegBank,
    output::OutputInner,
    packed_float::PackedPositiveFloat,
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
#[derive(Clone, Debug, Hash)]
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

    /// How much effort should the register allocator put into identifying and
    /// eliminating redundant moves?
    pub move_elimination_level: MoveEliminationLevel,
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
            move_elimination_level: MoveEliminationLevel::Global,
        }
    }
}

/// The level of redundant-move elimination to perform.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum MoveEliminationLevel {
    /// Do not spend time identifying and eliminating redundant moves.
    None,

    /// Perform a single pass of redundant-move elimination, which can only
    /// remove redundant moves locally within a basic block.
    Local,

    /// Remove redundant moves in a global fixed point loop.
    #[default]
    Global,
}

/// The constraints describing where an operand may be located.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum OperandConstraint {
    /// This operand may be placed in any location: register or stack.
    Any,

    /// The register class describing the set of registers that this operand's
    /// value may be placed in.
    ///
    /// If an instruction requires an operand in one particular, fixed register,
    /// then create a singleton [`RegClass`] containing only that register and
    /// use it here.
    Reg(RegClass),

    /// This operand must be placed on the stack.
    Stack,

    /// This operand must be in the same location as the `i`th operand of this
    /// operand's associated instruction.
    ///
    /// The operand named by a `Reuse` must not itself have a `Reuse`
    /// constraint.
    Reuse(usize),
}

const TAG_ANY: u64 = 0;
const TAG_REG: u64 = 1;
const TAG_STACK: u64 = 2;
const TAG_REUSE: u64 = 3;

impl OperandConstraint {
    fn to_bits(self) -> (u64, u64) {
        match self {
            Self::Any => (TAG_ANY, 0),
            Self::Reg(class) => (TAG_REG, u64::try_from(class.index()).unwrap()),
            Self::Stack => (TAG_STACK, 0),
            Self::Reuse(i) => (TAG_REUSE, u64::try_from(i).unwrap()),
        }
    }

    fn from_bits(tag: u64, payload: u64) -> Self {
        match tag {
            TAG_ANY => {
                debug_assert_eq!(payload, 0);
                Self::Any
            }
            TAG_REG => {
                let index = usize::try_from(payload).unwrap();
                Self::Reg(RegClass::try_new(index).unwrap())
            }
            TAG_STACK => {
                debug_assert_eq!(payload, 0);
                Self::Stack
            }
            TAG_REUSE => Self::Reuse(usize::try_from(payload).unwrap()),
            _ => unreachable!("not an operand constraint tag: {tag}"),
        }
    }

    /// The constraint that this instruction's `i`th operand imposes.
    fn resolve(i: usize, sibling: impl Fn(usize) -> OperandConstraint) -> Self {
        match sibling(i) {
            Self::Reuse(_) => {
                panic!("a reuse constraint may not point at another reuse constraint")
            }
            constraint => constraint,
        }
    }

    /// This constraint with any `Reuse` replaced by the constraint on the
    /// operand that `Reuse` names.
    pub(crate) fn resolved(self, sibling: impl Fn(usize) -> OperandConstraint) -> Self {
        match self {
            Self::Reuse(i) => Self::resolve(i, sibling),
            constraint => constraint,
        }
    }

    /// Does this constraint, which must already be resolved, demand one
    /// particular register?
    ///
    /// That is, does it name a class with exactly one member?
    pub(crate) fn is_fixed(self, machine: &Machine) -> bool {
        debug_assert!(!matches!(self, Self::Reuse(_)), "must already be resolved");
        match self {
            Self::Reg(class) => class.is_singleton(machine),
            _ => false,
        }
    }

    /// The weakest constraint that satisfies both `self` and `other`, or `None`
    /// when nothing satisfies both.
    ///
    /// `self_sibling` gives the constraint on the `i`th operand of the instruction
    /// that `self` belongs to; `other_sibling` does the same for `other`.
    ///
    /// This is commutative: merging in either order gives the same answer.
    pub(crate) fn merge(
        &self,
        other: &Self,
        machine: &Machine,
        self_sibling: impl Fn(usize) -> OperandConstraint,
        other_sibling: impl Fn(usize) -> OperandConstraint,
    ) -> Option<Self> {
        match (self, other) {
            (Self::Any, other) | (other, Self::Any) => Some(*other),

            (Self::Reg(lhs), Self::Reg(rhs)) => lhs.intersect(machine, *rhs).map(Self::Reg),

            (Self::Reg(_), Self::Stack) | (Self::Stack, Self::Reg(_)) => None,

            (Self::Reg(rc), Self::Reuse(i)) => match Self::resolve(*i, other_sibling) {
                Self::Reg(target) if *rc == target => Some(Self::Reuse(*i)),
                _ => None,
            },
            (Self::Reuse(i), Self::Reg(rc)) => match Self::resolve(*i, self_sibling) {
                Self::Reg(target) if *rc == target => Some(Self::Reuse(*i)),
                _ => None,
            },

            (Self::Stack, Self::Stack) => Some(Self::Stack),

            (Self::Stack, Self::Reuse(i)) => match Self::resolve(*i, other_sibling) {
                Self::Stack => Some(Self::Reuse(*i)),
                _ => None,
            },
            (Self::Reuse(i), Self::Stack) => match Self::resolve(*i, self_sibling) {
                Self::Stack => Some(Self::Reuse(*i)),
                _ => None,
            },

            (Self::Reuse(lhs), Self::Reuse(rhs)) => {
                if lhs == rhs {
                    Some(Self::Reuse(*lhs))
                } else {
                    None
                }
            }
        }
    }
}

/// An instruction operand and its register constraints.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Operand<E = u32>
where
    E: EntityRepr,
{
    /// Bit-packed as follows:
    ///
    /// ```text
    ///  63  ...  52 51  ...   36 35   34 33       32      31    ...     0
    /// +-----------+------------+-------+--------+-------+---------------+
    /// | unused:12 | payload:16 | tag:2 | kind:1 | pos:1 |    val:32     |
    /// +-----------+------------+-------+--------+-------+---------------+
    /// ```
    bits: u64,

    _repr: PhantomData<fn() -> E>,
}

const VAL_BITS: u32 = 32;
const VAL_SHIFT: u32 = 0;
const VAL_MAX: u64 = (1 << VAL_BITS) - 1;

const POS_BITS: u32 = 1;
const POS_SHIFT: u32 = VAL_SHIFT + VAL_BITS;

const KIND_BITS: u32 = 1;
const KIND_SHIFT: u32 = POS_SHIFT + POS_BITS;

const TAG_BITS: u32 = 2;
const TAG_SHIFT: u32 = KIND_SHIFT + KIND_BITS;
const TAG_MAX: u64 = (1 << TAG_BITS) - 1;

const PAYLOAD_BITS: u32 = 16;
const PAYLOAD_SHIFT: u32 = TAG_SHIFT + TAG_BITS;
const PAYLOAD_MAX: u64 = (1 << PAYLOAD_BITS) - 1;

const TOTAL_BITS: u32 = PAYLOAD_SHIFT + PAYLOAD_BITS;

const _OPERAND_FITS_IN_U64: () = assert!(TOTAL_BITS <= u64::BITS);
const _OPERAND_HOLDS_FULL_VAL: () = assert!(u32::BITS == VAL_BITS);

const _: () = assert!((TAG_ANY & TAG_MAX) == TAG_ANY);
const _: () = assert!((TAG_REG & TAG_MAX) == TAG_REG);
const _: () = assert!((TAG_STACK & TAG_MAX) == TAG_STACK);
const _: () = assert!((TAG_REUSE & TAG_MAX) == TAG_REUSE);
const _: () = assert!(RegClass::MAX_INCLUDING_DERIVED as u64 <= PAYLOAD_MAX + 1);
const _: () = assert!(MAX_OPERANDS_PER_INST as u64 <= PAYLOAD_MAX + 1);

impl<E> fmt::Debug for Operand<E>
where
    E: EntityRepr,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Operand")
            .field("pos", &self.pos())
            .field("kind", &self.kind())
            .field("constraint", &self.constraint())
            .field("val", &self.val())
            .finish()
    }
}

impl<E> Operand<E>
where
    E: EntityRepr,
{
    /// Create an operand.
    ///
    /// # Panics
    ///
    /// Panics when `constraint` is `Reuse(i)` and `i` is too large to be a
    /// valid operand index.
    #[inline]
    pub fn new(pos: Position, kind: DefUse, constraint: OperandConstraint, val: Val<E>) -> Self {
        let (tag, payload) = constraint.to_bits();
        assert!(payload <= PAYLOAD_MAX);

        let val = u64::try_from(val.index()).unwrap();
        debug_assert!(val <= VAL_MAX);

        Self {
            bits: (val << VAL_SHIFT)
                | ((pos as u64) << POS_SHIFT)
                | ((kind as u64) << KIND_SHIFT)
                | (tag << TAG_SHIFT)
                | (payload << PAYLOAD_SHIFT),
            _repr: PhantomData,
        }
    }

    /// The position of its value's definition or use within this operand's
    /// associated instruction.
    #[inline]
    pub fn pos(self) -> Position {
        if (self.bits >> POS_SHIFT) & 1 == Position::Early as u64 {
            Position::Early
        } else {
            Position::Late
        }
    }

    /// Whether this operand defines or uses its value.
    #[inline]
    pub fn kind(self) -> DefUse {
        if (self.bits >> KIND_SHIFT) & 1 == DefUse::Def as u64 {
            DefUse::Def
        } else {
            DefUse::Use
        }
    }

    /// The constraints on this operand's placement.
    #[inline]
    pub fn constraint(self) -> OperandConstraint {
        OperandConstraint::from_bits(
            (self.bits >> TAG_SHIFT) & TAG_MAX,
            (self.bits >> PAYLOAD_SHIFT) & PAYLOAD_MAX,
        )
    }

    /// The value that is defined or used by this operand.
    #[inline]
    pub fn val(self) -> Val<E> {
        let index = usize::try_from((self.bits >> VAL_SHIFT) & VAL_MAX).unwrap();
        Val::try_new(index).unwrap()
    }

    #[cfg(any(test, fuzz))]
    pub(crate) fn set_val(&mut self, val: Val<E>) {
        *self = Self::new(self.pos(), self.kind(), self.constraint(), val);
    }

    #[inline]
    #[allow(dead_code, reason = "will probably need it")]
    pub(crate) fn to_bits(self) -> u64 {
        self.bits
    }

    #[inline]
    #[allow(dead_code, reason = "will probably need it")]
    pub(crate) fn from_bits(bits: u64) -> Self {
        let operand = Self {
            bits,
            _repr: PhantomData,
        };
        if cfg!(debug_assertions) {
            assert_eq!(
                bits >> TOTAL_BITS,
                0,
                "an `Operand`'s unused bits must be clear",
            );
            // Round-tripping every field is what checks that the tag and
            // payload agree and that the value index is representable here.
            debug_assert_eq!(
                Self::new(
                    operand.pos(),
                    operand.kind(),
                    operand.constraint(),
                    operand.val(),
                )
                .bits,
                bits,
            );
        }
        operand
    }
}

/// The position of an operand's definition or use of its value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(any(test, fuzz), derive(mutatis::Mutate))]
#[repr(u8)]
pub enum Position {
    /// The operand is accessed early, just after entering the instruction.
    Early = 0,
    /// The operand is accessed late, just before exiting the instruction.
    Late = 1,
}

impl Position {
    /// Is this `Position::Early`?
    pub fn is_early(self) -> bool {
        matches!(self, Self::Early)
    }

    /// Is this `Position::Late`?
    pub fn is_late(self) -> bool {
        matches!(self, Self::Late)
    }
}

/// A definition or use of an associated value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(any(test, fuzz), derive(mutatis::Mutate))]
#[repr(u8)]
pub enum DefUse {
    /// A definition.
    Def = 0,
    /// A use.
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

    /// The associated input value type.
    type InputValue<'a>: InputValue<'a>
    where
        Self: 'a;

    /// The number of values defined in this function.
    fn len_values(&self) -> usize;

    /// The iterator type returned by [`InputFunction::values`].
    type ValuesIter<'a>: Iterator<Item = (Val, Self::InputValue<'a>)>
    where
        Self: 'a;

    /// An iterator over the values defined in this function.
    fn values(&self) -> Self::ValuesIter<'_>;

    /// Get the given input value.
    fn value(&self, val: Val) -> Self::InputValue<'_>;

    /// The number of instructions defined in this function.
    fn len_insts(&self) -> usize;

    /// Get the given input instruction.
    fn inst(&self, inst: Inst) -> Self::InputInst<'_>;

    /// The function's entry block.
    fn entry_block(&self) -> Block;

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

    /// Get a `Display` implementation that prints this `InputFunction`.
    fn display(&self) -> DisplayInputFunction<'_, Self> {
        DisplayInputFunction(self)
    }
}

/// The estimated frequency that a block is executed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BlockFrequency(PackedBlockFrequency);

const BLOCK_FREQUENCY_BITS: u32 = 16;
type PackedBlockFrequency = PackedPositiveFloat<u16, BLOCK_FREQUENCY_BITS>;

impl Default for BlockFrequency {
    fn default() -> Self {
        Self::NORMAL
    }
}

impl BlockFrequency {
    /// Construct a new frequency.
    ///
    /// # Panics
    ///
    /// Panics when the given frequency value does not have a positive sign.
    pub const fn new(frequency: f32) -> Self {
        assert!(frequency.is_sign_positive());
        Self(PackedBlockFrequency::new(frequency))
    }

    /// This frequency's value.
    pub(crate) const fn as_f32(self) -> f32 {
        self.0.as_f32()
    }

    /// The canonical "cold" block frequency.
    pub const COLD: Self = BlockFrequency::new(f32::EPSILON);

    /// The default block frequency that is neither "cold" nor "hot".
    pub const NORMAL: Self = BlockFrequency::new(1.0);

    /// The canonical "hot" block frequency.
    pub const HOT: Self = BlockFrequency::new(100.0);

    /// Is this frequency at or below the canonical [`BlockFrequency::COLD`]?
    pub const fn is_cold(self) -> bool {
        // The packed bits compare in the same order as the values they encode,
        // and trait comparison is not available in a `const fn`.
        self.0.bits() <= Self::COLD.0.bits()
    }
}

/// A block in an [`InputFunction`].
pub trait InputBlock<'a> {
    /// The associated input instruction type.
    type InputInst<'b>: InputInst<'b>
    where
        Self: 'b;

    /// Get this block's `Block`.
    fn block(&self) -> Block;

    /// Get the estimated frequency that this block is executed.
    fn frequency(&self) -> BlockFrequency;

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
    ///
    /// A block must have no more than `u16::MAX` successors.
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
}

/// A value defined in an [`InputFunction`].
pub trait InputValue<'a> {
    /// Get this value's `Val`.
    fn val(&self) -> Val;

    /// Get the cost of rematerializing this value, if possible.
    fn remat_cost(&self) -> Option<RematCost>;

    /// Get the register class that this value naturally belongs within.
    fn reg_class(&self) -> RegClass;
}

/// Machine queries about a value.
impl<E> Val<E>
where
    E: EntityRepr,
{
    /// The register bank this value naturally belongs to.
    pub(crate) fn reg_bank(self, input: &Input<'_, impl InputFunction>) -> RegBank {
        self.reg_class(input).bank(input.machine)
    }

    /// The register class this value naturally belongs within.
    pub(crate) fn reg_class(self, input: &Input<'_, impl InputFunction>) -> RegClass {
        input.func.value(self.with_repr32()).reg_class()
    }

    /// How many registers this value occupies.
    pub(crate) fn num_regs(self, input: &Input<'_, impl InputFunction>) -> usize {
        self.reg_class(input).group_size(input.machine).unwrap_or(1)
    }
}

/// An instruction in a [`InputBlock`].
pub trait InputInst<'a> {
    /// Get this instruction's `Inst`.
    fn inst(&self) -> Inst;

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

    /// Get the block that this instruction lies within.
    fn block(&self) -> Block;
}

/// The cost of rematerializing a value, rather than shuffling it between
/// registers or reloading it from a spill slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RematCost {
    /// Always rematerialize this value on demand; that is cheaper than keeping
    /// it in a register.
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
pub(crate) trait FmtWithContext<E>
where
    E: EntityRepr,
{
    /// Format `self` into `f`, optionally adding extra information from
    /// `context` if present.
    fn fmt_with_context(
        &self,
        f: &mut fmt::Formatter<'_>,
        context: &mut ContextInner<E>,
    ) -> IResult<()>;
}

/// Adapt a `FmtWithContext` into a `Display` that formats with a particular
/// context, rather than with an empty scratch context.
pub(crate) struct DisplayWithContext<'a, T, E>
where
    E: EntityRepr,
{
    value: T,
    context: RefCell<&'a mut ContextInner<E>>,
}

impl<'a, T, E> DisplayWithContext<'a, T, E>
where
    E: EntityRepr,
{
    /// Format `value` with `context`.
    pub(crate) fn new(value: T, context: &'a mut ContextInner<E>) -> Self {
        Self {
            value,
            context: RefCell::new(context),
        }
    }
}

impl<T, E> fmt::Display for DisplayWithContext<'_, T, E>
where
    T: FmtWithContext<E>,
    E: EntityRepr,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut context = self.context.borrow_mut();
        match self.value.fmt_with_context(f, &mut context) {
            Ok(()) => Ok(()),
            Err(()) => {
                let _ = context.output.take_error();
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
        let mut context = ContextInner::<u32>::new();
        match self.fmt_with_context(f, &mut context) {
            Ok(()) => Ok(()),
            Err(()) => {
                let _ = fmt::Debug::fmt(&context.output.take_error(), f);
                Err(fmt::Error)
            }
        }
    }
}

impl<E, F> FmtWithContext<E> for Input<'_, F>
where
    E: EntityRepr,
    F: InputFunction,
{
    fn fmt_with_context(
        &self,
        f: &mut fmt::Formatter<'_>,
        context: &mut ContextInner<E>,
    ) -> IResult<()> {
        context
            .output
            .result(writeln!(f, "Options: {:#?}", self.options))?;
        context
            .output
            .result(writeln!(f, "Machine: {:#?}", self.machine))?;

        DisplayInputFunction(self.func).fmt_with_context(f, context)
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
        let mut context = ContextInner::<u32>::new();
        match self.fmt_with_context(f, &mut context) {
            Ok(()) => Ok(()),
            Err(()) => {
                let _ = fmt::Debug::fmt(&context.output.take_error(), f);
                Err(fmt::Error)
            }
        }
    }
}

impl<E, F> FmtWithContext<E> for DisplayInputFunction<'_, F>
where
    E: EntityRepr,
    F: InputFunction,
{
    fn fmt_with_context(
        &self,
        f: &mut fmt::Formatter<'_>,
        context: &mut ContextInner<E>,
    ) -> IResult<()> {
        context.output.result(writeln!(f, "Function {{"))?;
        {
            let entry = self.0.entry_block();
            for (block, input_block) in self.0.blocks() {
                context.output.result(write!(f, "  "))?;
                if block == entry {
                    context.output.result(write!(f, "entry "))?;
                }
                context.output.result(write!(f, "{block:?}"))?;
                fmt_val_list(f, &mut context.output, input_block.params())?;
                context.output.result(writeln!(f, ":"))?;
                DisplayInputBlock(input_block).fmt_with_context(f, context)?;
                context.output.result(writeln!(f))?;
            }
        }
        context.output.result(writeln!(f, "}}"))
    }
}

/// TODO FITZGEN
pub struct DisplayInputBlock<B>(B);

impl<'a, E, B> FmtWithContext<E> for DisplayInputBlock<B>
where
    E: EntityRepr,
    B: InputBlock<'a>,
{
    fn fmt_with_context(
        &self,
        f: &mut fmt::Formatter<'_>,
        context: &mut ContextInner<E>,
    ) -> IResult<()> {
        for (inst, input_inst) in self.0.insts() {
            context.output.result(writeln!(f, "    {inst:?}"))?;
            for arg in input_inst.operands() {
                context.output.result(write!(f, "      "))?;
                match arg.pos() {
                    Position::Early => context.output.result(write!(f, "early "))?,
                    Position::Late => context.output.result(write!(f, "late "))?,
                }
                match arg.kind() {
                    DefUse::Def => context.output.result(write!(f, "def "))?,
                    DefUse::Use => context.output.result(write!(f, "use "))?,
                }
                context.output.result(write!(f, "{:?} ", arg.val()))?;
                match arg.constraint() {
                    OperandConstraint::Any => context.output.result(write!(f, "any"))?,
                    OperandConstraint::Reg(class) => {
                        context.output.result(write!(f, "in {class:?}"))?
                    }
                    OperandConstraint::Stack => context.output.result(write!(f, "on stack"))?,
                    OperandConstraint::Reuse(i) => {
                        context.output.result(write!(f, "reusing operand {i}"))?
                    }
                }
                context.output.result(writeln!(f))?;
            }
        }
        if self.0.len_successors() == 0 {
            context.output.result(writeln!(f, "    --> returns"))?;
        } else {
            for (i, block) in self.0.successors().enumerate() {
                context.output.result(write!(f, "    --> {block:?}"))?;
                fmt_val_list(f, &mut context.output, self.0.successor_block_args(i))?;
                context.output.result(writeln!(f))?;
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

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;

    #[test]
    fn input_is_send_sync() {
        fn _with_send_sync_input_func<F: InputFunction + Send + Sync>() {
            fn assert_send<T: Send>() {}
            fn assert_sync<T: Sync>() {}

            assert_send::<Input<'_, F>>();
            assert_sync::<Input<'_, F>>();
        }
    }

    #[test]
    fn canonical_block_frequencies_stay_ordered() {
        assert!(BlockFrequency::COLD < BlockFrequency::NORMAL);
        assert!(BlockFrequency::NORMAL < BlockFrequency::HOT);

        // `COLD` is the smallest of them, so it is the one at risk of being
        // truncated away to zero. It is a power of two, so it has no mantissa
        // bits to lose and survives exactly.
        assert_eq!(BlockFrequency::COLD.as_f32(), f32::EPSILON);
        assert!(BlockFrequency::COLD.as_f32() > 0.0);

        // These two are also exact, having short mantissas.
        assert_eq!(BlockFrequency::NORMAL.as_f32(), 1.0);
        assert_eq!(BlockFrequency::HOT.as_f32(), 100.0);

        assert_eq!(BlockFrequency::default(), BlockFrequency::NORMAL);
    }

    #[test]
    fn cold_is_every_frequency_at_or_below_cold() {
        assert!(BlockFrequency::COLD.is_cold());

        // An embedder is free to report a frequency below `COLD`, and it means
        // the same thing.
        assert!(BlockFrequency::new(0.0).is_cold());
        assert!(BlockFrequency::new(f32::EPSILON / 2.0).is_cold());

        assert!(!BlockFrequency::NORMAL.is_cold());
        assert!(!BlockFrequency::HOT.is_cold());
        assert!(!BlockFrequency::default().is_cold());
    }

    fn every_operand<E>() -> impl Iterator<Item = Operand<E>>
    where
        E: EntityRepr,
    {
        let constraints = [
            OperandConstraint::Any,
            OperandConstraint::Reg(RegClass::try_new(0).unwrap()),
            OperandConstraint::Reg(RegClass::try_new(RegClass::MAX_INCLUDING_DERIVED - 1).unwrap()),
            OperandConstraint::Stack,
            OperandConstraint::Reuse(0),
            OperandConstraint::Reuse(MAX_OPERANDS_PER_INST - 1),
        ];
        let vals = [0, 1, Val::<E>::MAX_REPRESENTABLE.index()];

        [Position::Early, Position::Late]
            .into_iter()
            .flat_map(move |pos| {
                [DefUse::Def, DefUse::Use]
                    .into_iter()
                    .flat_map(move |kind| {
                        constraints.into_iter().flat_map(move |constraint| {
                            vals.into_iter().map(move |val| {
                                Operand::new(pos, kind, constraint, Val::try_new(val).unwrap())
                            })
                        })
                    })
            })
    }

    #[test]
    fn an_operand_is_eight_bytes() {
        assert_eq!(core::mem::size_of::<Operand<u8>>(), 8);
        assert_eq!(core::mem::size_of::<Operand<u16>>(), 8);
        assert_eq!(core::mem::size_of::<Operand<u32>>(), 8);
    }

    fn operand_packing_round_trips<E>()
    where
        E: EntityRepr,
    {
        for operand in every_operand::<E>() {
            let (pos, kind, constraint, val) = (
                operand.pos(),
                operand.kind(),
                operand.constraint(),
                operand.val(),
            );

            // Every field reads back as it was written, without disturbing any
            // of the others.
            assert_eq!(
                Operand::<E>::new(pos, kind, constraint, val),
                operand,
                "{operand:?}",
            );

            // The unused high bits stay clear, which is what leaves room to add
            // a field later.
            assert_eq!(operand.to_bits() >> TOTAL_BITS, 0, "{operand:?}");
            assert_eq!(Operand::<E>::from_bits(operand.to_bits()), operand);

            // `set_val` is the one mutator, and it changes only the value.
            let mut replaced = operand;
            replaced.set_val(Val::try_new(0).unwrap());
            assert_eq!(replaced.val(), Val::try_new(0).unwrap());
            assert_eq!(replaced.pos(), pos);
            assert_eq!(replaced.kind(), kind);
            assert_eq!(replaced.constraint(), constraint);
        }
    }

    #[test]
    fn operand_packing_round_trips_at_every_repr() {
        operand_packing_round_trips::<u8>();
        operand_packing_round_trips::<u16>();
        operand_packing_round_trips::<u32>();
    }

    /// `Operand` derives `PartialEq` and `Hash` on its raw bits, which is a lie
    /// unless the encoding is canonical: the variants with nothing to say must
    /// leave the payload at zero rather than at whatever was there before.
    #[test]
    fn constraints_without_a_payload_encode_canonically() {
        let val = Val::<u32>::try_new(3).unwrap();
        for constraint in [OperandConstraint::Any, OperandConstraint::Stack] {
            let operand = Operand::new(Position::Early, DefUse::Def, constraint, val);
            assert_eq!((operand.to_bits() >> PAYLOAD_SHIFT) & PAYLOAD_MAX, 0);

            // Reached by way of a constraint that does have a payload, so the
            // payload bits would survive if `new` did not overwrite them.
            let mut other = Operand::new(
                Position::Early,
                DefUse::Def,
                OperandConstraint::Reuse(9),
                val,
            );
            other = Operand::new(other.pos(), other.kind(), constraint, other.val());
            assert_eq!(other, operand);
        }
    }

    /// A machine with two classes that cross, so that `merge` has an
    /// intersection to find and a pair with none.
    fn merge_test_machine() -> (Machine, RegClass, RegClass, RegClass) {
        let mut builder = crate::MachineBuilder::new();
        let bank = builder
            .declare_reg_bank(crate::SpillSlotSize::new(8).unwrap())
            .unwrap();
        let r: Vec<crate::Reg> = (0..3)
            .map(|i| {
                let unit = |i| crate::RegUnit::try_new(i).unwrap();
                builder.define_reg(bank, unit(i)..unit(i + 1)).unwrap()
            })
            .collect();

        let low = builder.define_reg_class(bank, 1.0, [r[0], r[1]]).unwrap();
        let high = builder.define_reg_class(bank, 1.0, [r[1], r[2]]).unwrap();
        let disjoint = builder.define_reg_class(bank, 1.0, [r[0]]).unwrap();
        let machine = builder.finish().unwrap();

        // `low` and `high` share `r[1]`; `disjoint` and `high` share nothing.
        assert!(low.intersect(&machine, high).is_some());
        assert_eq!(disjoint.intersect(&machine, high), None);

        (machine, low, high, disjoint)
    }

    #[test]
    fn merge_intersects_register_classes() {
        let (machine, low, high, disjoint) = merge_test_machine();
        let no_siblings = |_: usize| -> OperandConstraint {
            unreachable!("these constraints have no `Reuse` to resolve")
        };

        let both = low.intersect(&machine, high).unwrap();
        assert_eq!(
            OperandConstraint::Reg(low).merge(
                &OperandConstraint::Reg(high),
                &machine,
                &no_siblings,
                &no_siblings
            ),
            Some(OperandConstraint::Reg(both)),
        );

        // Nowhere left to put the operand.
        assert_eq!(
            OperandConstraint::Reg(disjoint).merge(
                &OperandConstraint::Reg(high),
                &machine,
                &no_siblings,
                &no_siblings
            ),
            None,
        );

        // A register and the stack are different places.
        assert_eq!(
            OperandConstraint::Reg(low).merge(
                &OperandConstraint::Stack,
                &machine,
                &no_siblings,
                &no_siblings
            ),
            None,
        );
        assert_eq!(
            OperandConstraint::Stack.merge(
                &OperandConstraint::Stack,
                &machine,
                &no_siblings,
                &no_siblings
            ),
            Some(OperandConstraint::Stack),
        );
    }

    /// Merging with a `Reuse` keeps the `Reuse`, so that the requirement to be
    /// in the same place as another operand is never silently dropped.
    #[test]
    fn merge_keeps_reuse_constraints() {
        let (machine, low, high, disjoint) = merge_test_machine();

        // Operand 0 wants `low`, operand 1 wants the stack, operand 2 wants
        // `high`.
        let siblings = |i: usize| -> OperandConstraint {
            match i {
                0 => OperandConstraint::Reg(low),
                1 => OperandConstraint::Stack,
                _ => OperandConstraint::Reg(high),
            }
        };

        // Pinning to operand 0 cannot also promise `disjoint`: operand 0's class
        // is `low`, which is wider, so the allocator could satisfy the reuse by
        // picking a register outside `disjoint`. `Reuse(0)` has nowhere to record
        // the extra narrowing, so there is no merged constraint to give.
        assert_eq!(
            OperandConstraint::Reg(disjoint).merge(
                &OperandConstraint::Reuse(0),
                &machine,
                &siblings,
                &siblings,
            ),
            None,
        );

        // But `low` narrows operand 0 not at all, so the reuse survives.
        assert_eq!(
            OperandConstraint::Reg(low).merge(
                &OperandConstraint::Reuse(0),
                &machine,
                &siblings,
                &siblings,
            ),
            Some(OperandConstraint::Reuse(0)),
        );
        assert_eq!(
            OperandConstraint::Reuse(0).merge(
                &OperandConstraint::Reg(low),
                &machine,
                &siblings,
                &siblings,
            ),
            Some(OperandConstraint::Reuse(0)),
        );

        // A register constraint and an operand pinned to the stack cannot both
        // hold, and vice versa.
        assert_eq!(
            OperandConstraint::Reg(low).merge(
                &OperandConstraint::Reuse(1),
                &machine,
                &siblings,
                &siblings
            ),
            None,
        );
        assert_eq!(
            OperandConstraint::Stack.merge(
                &OperandConstraint::Reuse(1),
                &machine,
                &siblings,
                &siblings
            ),
            Some(OperandConstraint::Reuse(1)),
        );
        assert_eq!(
            OperandConstraint::Stack.merge(
                &OperandConstraint::Reuse(0),
                &machine,
                &siblings,
                &siblings
            ),
            None,
        );

        // "Same place as operand 0" and "same place as operand 2" is a
        // requirement between two *other* operands, which one constraint cannot
        // express.
        assert_eq!(
            OperandConstraint::Reuse(0).merge(
                &OperandConstraint::Reuse(2),
                &machine,
                &siblings,
                &siblings
            ),
            None,
        );
        assert_eq!(
            OperandConstraint::Reuse(0).merge(
                &OperandConstraint::Reuse(0),
                &machine,
                &siblings,
                &siblings
            ),
            Some(OperandConstraint::Reuse(0)),
        );
    }

    /// The algebra `merge`'s callers rely on: it is commutative, idempotent, and
    /// `Any` is its identity.
    #[test]
    fn merge_is_a_commutative_idempotent_meet() {
        let (machine, low, high, disjoint) = merge_test_machine();
        let siblings = |i: usize| -> OperandConstraint {
            match i {
                0 => OperandConstraint::Reg(low),
                1 => OperandConstraint::Stack,
                _ => OperandConstraint::Reg(high),
            }
        };

        let constraints = [
            OperandConstraint::Any,
            OperandConstraint::Reg(low),
            OperandConstraint::Reg(high),
            OperandConstraint::Reg(disjoint),
            OperandConstraint::Stack,
            OperandConstraint::Reuse(0),
            OperandConstraint::Reuse(1),
            OperandConstraint::Reuse(2),
        ];

        for a in constraints {
            assert_eq!(
                a.merge(&a, &machine, &siblings, &siblings),
                Some(a),
                "{a:?}"
            );
            assert_eq!(
                OperandConstraint::Any.merge(&a, &machine, &siblings, &siblings),
                Some(a),
                "{a:?}",
            );
            assert_eq!(
                a.merge(&OperandConstraint::Any, &machine, &siblings, &siblings),
                Some(a),
                "{a:?}",
            );

            for b in constraints {
                assert_eq!(
                    a.merge(&b, &machine, &siblings, &siblings),
                    b.merge(&a, &machine, &siblings, &siblings),
                    "merging {a:?} and {b:?} must not depend on the order",
                );
            }
        }
    }
}
