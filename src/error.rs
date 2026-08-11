use crate::entity::{Block, Inst, Val};
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

    /// Too many live registers were requested at a single program point.
    TooManyLiveRegs,

    /// An instruction has more operands than supported.
    TooManyOperands {
        /// The [`Inst`] instruction with too many operands.
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
                write!(f, "invalid SSA: {val:?} is used at {inst:?}")
            }
            Self::BlockWithoutTerminator { block } => {
                write!(f, "{block:?} is missing a terminator")
            }
            Self::TerminatorInMiddleOfBlock { block, inst } => {
                write!(f, "terminator {inst:?} found in middle of {block:?}")
            }
            Self::InvalidBranch { inst } => {
                write!(f, "invalid branch instruction {inst:?}")
            }
            Self::TooManyLiveRegs => write!(f, "too many live registers at a single point"),
            Self::TooManyOperands { inst } => {
                write!(f, "too many operands at instruction {inst:?}")
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
