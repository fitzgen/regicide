use crate::{
    entity::{Block, Inst, Val},
    machine::{Reg, RegBank, RegClass, RegGroup},
};
use core::fmt;

/// An internal error, potentially recoverable by switching to a larger entity
/// representation.
#[derive(Debug)]
pub(crate) enum InternalError {
    /// The entity representation was too small to represent the problem's full
    /// index space. Switch to a larger entity representation.
    EntityReprTooSmall,

    /// An error that needs to be surfaced to the user.
    Error(Error),
}

impl From<fmt::Error> for InternalError {
    fn from(e: fmt::Error) -> Self {
        Error::from(e).into()
    }
}

impl From<Error> for InternalError {
    fn from(e: Error) -> Self {
        Self::Error(e)
    }
}

/// An error encountered during register allocation.
#[derive(Clone)]
pub enum Error {
    /// An invalid Static Single Assignment (`SSA`) use was encountered, such as a
    /// value being used before it is defined.
    InvalidSsa {
        /// The [`Val`] that is invalid in `SSA` form.
        val: Val,
        /// The [`Inst`] where the invalid `SSA` value is used.
        inst: Inst,
    },

    /// A value was defined more than once, which `SSA` form forbids.
    MultiplyDefinedValue {
        /// The [`Val`] with more than one definition.
        val: Val,
    },

    /// A value was never defined.
    UndefinedValue {
        /// The [`Val`] without a definition.
        val: Val,
    },

    /// A reference to a value outside of the function's value index space.
    ValOutOfBounds {
        /// The out-of-bounds [`Val`].
        val: Val,
    },

    /// A value that occupies more than one register was given a
    /// rematerialization cost.
    RematOfRegGroup {
        /// The [`Val`] that cannot be rematerialized.
        val: Val,
    },

    /// A value that is not computed from nothing was given a rematerialization
    /// cost.
    RematOfDerivedValue {
        /// The [`Val`] that cannot be rematerialized.
        val: Val,
        /// The [`Inst`] that defines it, or `None` when it is a block
        /// parameter, whose definition is the argument its predecessors pass.
        def: Option<Inst>,
    },

    /// A reference to a block outside of the function's block index space.
    BlockOutOfBounds {
        /// The out-of-bounds [`Block`].
        block: Block,
    },

    /// A reference to an instruction outside of the function's instruction
    /// index space.
    InstOutOfBounds {
        /// The out-of-bounds [`Inst`].
        inst: Inst,
    },

    /// A block is not reachable from the function's entry block.
    UnreachableBlock {
        /// The unreachable [`Block`].
        block: Block,
    },

    /// A control-flow edge passes a different number of block arguments than
    /// its target block has parameters.
    BlockArgCountMismatch {
        /// The [`Block`] the edge leaves.
        block: Block,
        /// The index of the successor edge within `block`.
        successor: usize,
        /// The number of parameters that the target block has.
        expected: usize,
        /// The number of arguments that the edge passes.
        actual: usize,
    },

    /// A control-flow edge passes a block argument whose register class differs
    /// from that of the parameter it feeds.
    ///
    /// The two are distinct values that coalescing places in a single location,
    /// so there is nothing that satisfies both when their classes disagree.
    BlockArgRegClassMismatch {
        /// The [`Block`] the edge leaves.
        block: Block,
        /// The index of the successor edge within `block`.
        successor: usize,
        /// The position of the offending argument along the edge.
        index: usize,
    },

    /// A block's instructions are not numbered contiguously.
    NonContiguousInsts {
        /// The [`Block`] whose instructions are misnumbered.
        block: Block,
        /// The first [`Inst`] in that block that does not immediately follow the
        /// instruction before it.
        inst: Inst,
    },

    /// An instruction appears in more than one block.
    InstInMultipleBlocks {
        /// An [`Inst`] that appears in more than one block.
        inst: Inst,
    },

    /// An instruction that the function declares does not appear in any block.
    InstInNoBlock {
        /// An [`Inst`] within the function's instruction index space that no
        /// block contains.
        inst: Inst,
    },

    /// An instruction reports that it lies within a block other than the one
    /// whose instructions contain it.
    InvalidInstBlock {
        /// The [`Inst`] that reported the wrong block.
        inst: Inst,

        /// The [`Block`] that the instruction claims to lie within.
        block: Block,
    },

    /// Looking an instruction up by index gave a different instruction than
    /// iterating over its block did.
    InconsistentInst {
        /// The [`Inst`] whose two access paths disagree.
        inst: Inst,
    },

    /// Looking a value up by index gave a different value than iterating over
    /// the function's values did.
    InconsistentVal {
        /// The [`Val`] whose two access paths disagree.
        val: Val,
    },

    /// A block's predecessors, as reported by the input, are not the exact
    /// reverse of the input's successor edges.
    InvalidPredecessors {
        /// A [`Block`] on the wrong end of an edge that one direction reports
        /// and the other does not.
        block: Block,
    },

    /// A block's immediate dominator, as reported by the input, is not
    /// its immediate dominator in the input's control-flow graph.
    InvalidImmediateDominator {
        /// The [`Block`] whose immediate dominator is wrong.
        block: Block,
    },

    /// The input's dominance relation disagrees with its control-flow graph
    /// about whether one block dominates another.
    InvalidDominance {
        /// The dominating [`Block`], according to the input.
        a: Block,
        /// The dominated [`Block`], according to the input.
        b: Block,
    },

    /// An [`InputFunction`][crate::InputFunction] reported a length that
    /// disagrees with the corresponding iterator.
    InconsistentLen {
        /// The name of the method that reported the wrong length.
        method: &'static str,
        /// The [`Block`] whose length was wrong, or `None` when the length
        /// describes the whole function rather than any one block.
        block: Option<Block>,
    },

    /// A basic block is missing a terminator instruction at its end.
    BlockWithoutTerminator {
        /// The [`Block`] missing a terminator.
        block: Block,
    },

    /// A terminator instruction was found in the middle of a basic block.
    TerminatorInMiddleOfBlock {
        /// The [`Block`] containing the invalid instruction.
        block: Block,
        /// The [`Inst`] terminator instruction that is in the middle of the block.
        inst: Inst,
    },

    /// An invalid branch instruction was encountered.
    InvalidBranch {
        /// The invalid [`Inst`] branch instruction.
        inst: Inst,
    },

    /// The machine description exceeds one of its capacity limits.
    MachineCapacityExceeded {
        /// What there were too many of.
        what: &'static str,
        /// The most of them that a machine may have.
        max: usize,
    },

    /// A machine description named a register bank that was never declared.
    UnknownRegBank {
        /// The undeclared [`RegBank`].
        bank: RegBank,
    },

    /// A register's range of register units is empty or backwards, or reaches
    /// beyond the unit index space.
    BadRegUnitRange {
        /// The [`Reg`] with the bad range.
        reg: Reg,
    },

    /// Two registers in the same register bank cover overlapping register units.
    ///
    /// Registers may only overlap across banks. This is the invariant that lets
    /// interference within a bank be a register-identity test rather than a unit
    /// overlap test.
    OverlappingRegsInBank {
        /// The [`RegBank`] they are both in.
        bank: RegBank,
        /// One of the two overlapping [`Reg`]s.
        a: Reg,
        /// The other.
        b: Reg,
    },

    /// A register was used by a register group or class belonging to a different
    /// bank than the register itself.
    RegInWrongBank {
        /// The [`Reg`] in the wrong bank.
        reg: Reg,
        /// The [`RegBank`] it needed to be in.
        expected: RegBank,
    },

    /// A register group was used by a register class belonging to a different
    /// bank than the group itself.
    RegGroupInWrongBank {
        /// The [`RegGroup`] in the wrong bank.
        group: RegGroup,
        /// The [`RegBank`] it needed to be in.
        expected: RegBank,
    },

    /// A register group has too few or too many registers in it.
    BadRegGroupSize {
        /// The [`RegGroup`] that is the wrong size.
        group: RegGroup,
        /// How many registers it has.
        len: usize,
    },

    /// A register class of register groups mixes groups of different sizes.
    MixedRegGroupSizes {
        /// The [`RegClass`] with the mismatched groups.
        class: RegClass,
    },

    /// A register class mixes registers the allocator owns with registers it
    /// does not.
    ///
    /// A class is wholly one or wholly the other: see
    /// [`MachineBuilder::define_non_allocatable_reg`][crate::MachineBuilder::define_non_allocatable_reg].
    MixedRegClassAllocatability {
        /// The [`RegClass`] holding both kinds.
        class: RegClass,

        /// The first member that disagrees with the class's first member.
        reg: Reg,
    },

    /// A register class of registers the allocator does not own has more than
    /// one member.
    ///
    /// Such a class names the one register an operand reads, and the allocator
    /// chooses nothing within it: see
    /// [`MachineBuilder::define_non_allocatable_reg`][crate::MachineBuilder::define_non_allocatable_reg].
    NonAllocatableRegClassIsNotASingleton {
        /// The [`RegClass`] with too many members.
        class: RegClass,

        /// How many registers, or register groups, it holds.
        len: usize,
    },

    /// A register class lists the same register more than once.
    DuplicateRegClassMember {
        /// The [`RegClass`] with the repeat.
        class: RegClass,
        /// The repeated [`Reg`].
        reg: Reg,
    },

    /// A register group lists the same register more than once.
    DuplicateRegGroupMember {
        /// The [`RegGroup`] with the repeat.
        group: RegGroup,
        /// The repeated [`Reg`].
        reg: Reg,
    },

    /// A register class has no members.
    ///
    /// A class is the set of registers an operand may be assigned to, so an
    /// empty one could never be satisfied.
    EmptyRegClass {
        /// The empty [`RegClass`].
        class: RegClass,
    },

    /// A register bank has no register that could serve as the scratch register
    /// for resolving a stack-to-stack move.
    NoStackToStackRegs {
        /// The [`RegBank`] with no scratch register.
        bank: RegBank,
    },

    /// Too many live registers were requested at a single program point.
    TooManyLiveRegs,

    /// An instruction has more operands than [`MAX_OPERANDS_PER_INST`], the
    /// most this allocator supports.
    ///
    /// [`MAX_OPERANDS_PER_INST`]: crate::MAX_OPERANDS_PER_INST
    TooManyOperands {
        /// The [`Inst`] instruction with too many operands.
        inst: Inst,
    },

    /// An operand's `Reuse` constraint does not name an operand that it can
    /// reuse.
    ///
    /// A `Reuse` must be a late definition naming an early, non-stack use of
    /// the same instruction, and no two may name the same target.
    InvalidReuse {
        /// The instruction with the offending operand.
        inst: Inst,

        /// The index of the operand whose `Reuse` constraint is invalid.
        operand: usize,
    },

    /// Two operands tied together by a `Reuse` constraint have values of
    /// differing register classes.
    ///
    /// A reuse makes the allocator give both operands one location, so there is
    /// nothing that satisfies both when their classes disagree.
    ReuseRegClassMismatch {
        /// The instruction with the offending operand.
        inst: Inst,

        /// The index of the operand carrying the `Reuse` constraint.
        operand: usize,
    },

    /// An operand's `Reg` constraint names a register class that the machine
    /// does not define.
    InvalidRegClass {
        /// The instruction with the offending operand.
        inst: Inst,

        /// The index of the operand whose register class is not defined.
        operand: usize,
    },

    /// A value's register class is one that the machine does not define.
    InvalidValRegClass {
        /// The [`Val`] whose register class is not defined.
        val: Val,
    },

    /// An operand's `Reg` constraint names a register class that is not
    /// contained in its value's register class, so the constraint admits at
    /// least one register that the operand's value may not live in.
    IncompatibleRegClass {
        /// The instruction with the offending operand.
        inst: Inst,

        /// The index of the operand whose class cannot hold its value.
        operand: usize,
    },

    /// A value's register class holds a register the allocator does not own.
    NonAllocatableRegInValClass {
        /// The value whose class is too wide.
        val: Val,
    },

    /// An operand names no value but is not a use pinned to registers the
    /// allocator does not own.
    OperandWithoutValIsNotAFixedUse {
        /// The instruction with the offending operand.
        inst: Inst,

        /// The index of that operand.
        operand: usize,
    },

    /// An operand's `Reg` constraint names a register class in which the
    /// allocator owns nothing, but the operand also names a value.
    ///
    /// The other half of [`Self::OperandWithoutValIsNotAFixedUse`]: such a
    /// class is how an operand names a register the allocator does not own,
    /// and naming one means naming no value.
    OperandWithValInNonAllocatableRegClass {
        /// The instruction with the offending operand.
        inst: Inst,

        /// The index of that operand.
        operand: usize,
    },

    /// A `Reuse` constraint targets an operand that names no value.
    ReuseOfOperandWithoutVal {
        /// The instruction with the offending operand.
        inst: Inst,

        /// The index of the `Reuse` operand.
        operand: usize,
    },

    /// Two of an instruction's fixed operands want the same register (or
    /// register unit) at the same time.
    ///
    /// A fixed operand, one whose constraint resolves to a class holding a
    /// single register or register group, does not choose a register but names
    /// one, which the allocator holds for it. A read holds its register from
    /// the gap before the instruction through the half the read happens in; a
    /// definition holds it from its own half through the gap after. So an early
    /// read and a late definition may name one register, but an early
    /// definition and a read may not. Operands that want a register at the same
    /// time are legal only as reads of the same value under the same
    /// constraint.
    ConflictingFixedOperands {
        /// The instruction with the offending operands.
        inst: Inst,

        /// The index of the later of the two operands.
        operand: usize,

        /// The index of the earlier operand it conflicts with.
        conflicts_with: usize,
    },

    /// The function has an instruction index above the largest one supported.
    TooManyInsts {
        /// The first [`Inst`] found whose index is out of range.
        inst: Inst,
    },

    /// A formatting error.
    FmtError(fmt::Error),
}

impl From<fmt::Error> for Error {
    fn from(e: fmt::Error) -> Self {
        Self::FmtError(e)
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidSsa { val, inst } => {
                write!(
                    f,
                    "invalid SSA: {val:?} is used at {inst:?}, which its definition does \
                     not dominate"
                )
            }
            Self::MultiplyDefinedValue { val } => {
                write!(f, "invalid SSA: {val:?} is defined more than once")
            }
            Self::UndefinedValue { val } => write!(f, "{val:?} is never defined"),
            Self::RematOfRegGroup { val } => write!(
                f,
                "{val:?} has a rematerialization cost, but occupies more than one register"
            ),
            Self::RematOfDerivedValue {
                val,
                def: Some(def),
            } => write!(
                f,
                "{val:?} has a rematerialization cost, but {def:?} computes it from values it \
                 reads"
            ),
            Self::RematOfDerivedValue { val, def: None } => write!(
                f,
                "{val:?} has a rematerialization cost, but is a block parameter and so no \
                 instruction computes it"
            ),
            Self::ValOutOfBounds { val } => {
                write!(f, "{val:?} is outside the function's value index space")
            }
            Self::BlockOutOfBounds { block } => {
                write!(f, "{block:?} is outside the function's block index space")
            }
            Self::InstOutOfBounds { inst } => write!(
                f,
                "{inst:?} is outside the function's instruction index space"
            ),
            Self::UnreachableBlock { block } => {
                write!(f, "{block:?} is not reachable from the entry block")
            }
            Self::BlockArgCountMismatch {
                block,
                successor,
                expected,
                actual,
            } => write!(
                f,
                "{block:?}'s successor edge {successor} passes {actual} block arguments, \
                 but its target block has {expected} parameters"
            ),
            Self::BlockArgRegClassMismatch {
                block,
                successor,
                index,
            } => write!(
                f,
                "block argument {index} of {block:?}'s successor edge {successor} is in a \
                 different register class than the parameter it feeds"
            ),
            Self::NonContiguousInsts { block, inst } => write!(
                f,
                "{inst:?} does not immediately follow the instruction before it in {block:?}"
            ),
            Self::InstInMultipleBlocks { inst } => {
                write!(f, "{inst:?} appears in more than one block")
            }
            Self::InstInNoBlock { inst } => {
                write!(f, "{inst:?} does not appear in any block")
            }
            Self::InvalidInstBlock { inst, block } => write!(
                f,
                "{inst:?} reports that it lies within {block:?}, which is not the block \
                 whose instructions contain it"
            ),
            Self::InconsistentInst { inst } => write!(
                f,
                "`InputFunction::inst` disagrees with `InputBlock::insts` about {inst:?}"
            ),
            Self::InconsistentVal { val } => write!(
                f,
                "`InputFunction::value` disagrees with `InputFunction::values` about {val:?}"
            ),
            Self::InvalidPredecessors { block } => write!(
                f,
                "{block:?}'s predecessors are not the reverse of the successor edges"
            ),
            Self::InvalidImmediateDominator { block } => {
                write!(f, "{block:?}'s immediate dominator is wrong")
            }
            Self::InvalidDominance { a, b } => write!(
                f,
                "the input's dominance relation is wrong about whether {a:?} dominates {b:?}"
            ),
            Self::InconsistentLen { method, block } => match block {
                Some(block) => write!(
                    f,
                    "`{method}` disagrees with the corresponding iterator for {block:?}"
                ),
                None => write!(f, "`{method}` disagrees with the corresponding iterator"),
            },
            Self::BlockWithoutTerminator { block } => {
                write!(f, "{block:?} is missing a terminator")
            }
            Self::TerminatorInMiddleOfBlock { block, inst } => {
                write!(f, "terminator {inst:?} found in middle of {block:?}")
            }
            Self::InvalidBranch { inst } => {
                write!(f, "invalid branch instruction {inst:?}")
            }
            Self::MachineCapacityExceeded { what, max } => {
                write!(f, "a machine may have at most {max} {what}")
            }
            Self::UnknownRegBank { bank } => write!(f, "{bank:?} was never declared"),
            Self::BadRegUnitRange { reg } => {
                write!(f, "{reg:?}'s range of register units is not valid")
            }
            Self::OverlappingRegsInBank { bank, a, b } => write!(
                f,
                "{a:?} and {b:?} are both in {bank:?} but cover overlapping register units"
            ),
            Self::RegInWrongBank { reg, expected } => {
                write!(f, "{reg:?} is not in {expected:?}")
            }
            Self::RegGroupInWrongBank { group, expected } => {
                write!(f, "{group:?} is not in {expected:?}")
            }
            Self::BadRegGroupSize { group, len } => {
                write!(f, "{group:?} has {len} registers in it")
            }
            Self::MixedRegGroupSizes { class } => {
                write!(f, "{class:?}'s register groups are not all the same size")
            }
            Self::MixedRegClassAllocatability { class, reg } => write!(
                f,
                "{class:?} holds both registers the allocator owns and registers it does not; \
                 {reg:?} is the first member to disagree with the class's first member"
            ),
            Self::NonAllocatableRegClassIsNotASingleton { class, len } => write!(
                f,
                "{class:?} holds registers the allocator does not own, so it must have exactly \
                 one member, but it has {len}"
            ),
            Self::DuplicateRegClassMember { class, reg } => {
                write!(f, "{class:?} lists {reg:?} more than once")
            }
            Self::DuplicateRegGroupMember { group, reg } => {
                write!(f, "{group:?} lists {reg:?} more than once")
            }
            Self::EmptyRegClass { class } => write!(f, "{class:?} has no members"),
            Self::NoStackToStackRegs { bank } => write!(
                f,
                "{bank:?} has no register available for resolving stack-to-stack moves"
            ),
            Self::TooManyLiveRegs => write!(f, "too many live registers at a single point"),
            Self::TooManyOperands { inst } => {
                write!(f, "too many operands at instruction {inst:?}")
            }
            Self::InvalidReuse { inst, operand } => write!(
                f,
                "operand {operand} of {inst:?} reuses an operand that it may not reuse"
            ),
            Self::ReuseRegClassMismatch { inst, operand } => write!(
                f,
                "operand {operand} of {inst:?} reuses an operand whose value is in a different \
                 register class"
            ),
            Self::InvalidRegClass { inst, operand } => write!(
                f,
                "operand {operand} of {inst:?} names a register class that this machine does not \
                 define"
            ),
            Self::InvalidValRegClass { val } => write!(
                f,
                "{val:?} is in a register class that this machine does not define"
            ),
            Self::IncompatibleRegClass { inst, operand } => write!(
                f,
                "operand {operand} of {inst:?} names a register class that is not contained in \
                 its value's register class"
            ),
            Self::NonAllocatableRegInValClass { val } => write!(
                f,
                "{val:?} is in a register class that holds a register the allocator does not \
                 own, so it could be defined in one"
            ),
            Self::OperandWithoutValIsNotAFixedUse { inst, operand } => write!(
                f,
                "operand {operand} of {inst:?} names no value, so it must be a use constrained \
                 to a register class holding nothing but registers the allocator does not own"
            ),
            Self::OperandWithValInNonAllocatableRegClass { inst, operand } => write!(
                f,
                "operand {operand} of {inst:?} is constrained to a register class holding \
                 nothing but registers the allocator does not own, so it must name no value"
            ),
            Self::ReuseOfOperandWithoutVal { inst, operand } => write!(
                f,
                "operand {operand} of {inst:?} reuses an operand that names no value"
            ),
            Self::ConflictingFixedOperands {
                inst,
                operand,
                conflicts_with,
            } => write!(
                f,
                "operands {conflicts_with} and {operand} of {inst:?} both name the same \
                 register at the same time"
            ),
            Self::TooManyInsts { inst } => {
                write!(
                    f,
                    "too many instructions: {inst:?}'s index exceeds the maximum of {}",
                    crate::live_ranges::MAX_INST_INDEX - 1
                )
            }
            Self::FmtError(e) => fmt::Debug::fmt(e, f),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

impl core::error::Error for Error {}

/// A result of either `Ok(T)` or `Err(regicide::Error)`.
pub type Result<T, E = Error> = ::core::result::Result<T, E>;

/// A result type to use internally.
///
/// Its zero-sized error type makes it smaller and faster than
/// `crate::Result<T>`, but its ergonomics are worse, since we rely on a
/// side-channel (an internal field on `Context`) to report the actual error to
/// the user. We always convert from `InternalResult<T>` to `crate::Result<T>`
/// before returning to the user. See `OutputInner::error` and
/// `OutputInner::take_error` for details.
pub(crate) type IResult<T> = Result<T, ()>;
