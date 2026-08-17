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

    /// A reference to a block outside of the function's block index space.
    BlockOutOfBounds {
        /// The out-of-bounds [`Block`].
        block: Block,
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
        /// The [`Block`] whose length was wrong.
        block: Block,
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

    /// A register's range of register units is backwards, or reaches beyond the
    /// unit index space.
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

    /// An instruction has more operands than supported.
    TooManyOperands {
        /// The [`Inst`] instruction with too many operands.
        inst: Inst,
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
            Self::ValOutOfBounds { val } => {
                write!(f, "{val:?} is outside the function's value index space")
            }
            Self::BlockOutOfBounds { block } => {
                write!(f, "{block:?} is outside the function's block index space")
            }
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
            Self::NonContiguousInsts { block, inst } => write!(
                f,
                "{inst:?} does not immediately follow the instruction before it in {block:?}"
            ),
            Self::InstInMultipleBlocks { inst } => {
                write!(f, "{inst:?} appears in more than one block")
            }
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
            Self::InconsistentLen { method, block } => write!(
                f,
                "`{method}` disagrees with the corresponding iterator for {block:?}"
            ),
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
            Self::TooManyInsts { inst } => {
                write!(
                    f,
                    "too many instructions: {inst:?}'s index exceeds the maximum of {}",
                    crate::live_ranges::MAX_INST_INDEX
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
