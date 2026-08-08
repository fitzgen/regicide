use crate::entity::{Block, Inst, Val};
use core::fmt;

#[allow(dead_code)] // TODO FITZGEN
pub(crate) enum InternalError {
    EntityReprTooSmall,
    Error(Error),
}

/// TODO FITZGEN
#[derive(Clone)]
pub enum Error {
    /// TODO FITZGEN
    EntityReprTooSmall,

    /// TODO FITZGEN
    InvalidSsa {
        /// TODO FITZGEN
        val: Val,
        /// TODO FITZGEN
        inst: Inst,
    },

    /// TODO FITZGEN
    BlockWithoutTerminator {
        /// TODO FITZGEN
        block: Block,
    },

    /// TODO FITZGEN
    TerminatorInMiddleOfBlock {
        /// TODO FITZGEN
        block: Block,
        /// TODO FITZGEN
        inst: Inst,
    },

    /// TODO FITZGEN
    InvalidBranch {
        /// TODO FITZGEN
        inst: Inst,
    },

    /// TODO FITZGEN
    TooManyLiveRegs,

    /// TODO FITZGEN
    TooManyOperands {
        /// TODO FITZGEN
        inst: Inst,
    },
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EntityReprTooSmall => write!(f, "EntityReprTooSmall"),
            Self::InvalidSsa { val, inst } => f
                .debug_struct("InvalidSsa")
                .field("val", val)
                .field("inst", inst)
                .finish(),
            Self::BlockWithoutTerminator { block } => f
                .debug_struct("BlockWithoutTerminator")
                .field("block", block)
                .finish(),
            Self::TerminatorInMiddleOfBlock { block, inst } => f
                .debug_struct("TerminatorInMiddleOfBlock")
                .field("block", block)
                .field("inst", inst)
                .finish(),
            Self::InvalidBranch { inst } => {
                f.debug_struct("InvalidBranch").field("inst", inst).finish()
            }
            Self::TooManyLiveRegs => write!(f, "TooManyLiveRegs"),
            Self::TooManyOperands { inst } => f
                .debug_struct("TooManyOperands")
                .field("inst", inst)
                .finish(),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

impl core::error::Error for Error {}

/// TODO FITZGEN
pub type Result<T, E = Error> = ::core::result::Result<T, E>;

/// A result type to use internally.
///
/// Its zero-sized error type makes it smaller and faster than
/// `crate::Result<T>`, but its ergonomics are worse, since we rely on a
/// side-channel (an internal field on `Context`) to report the actual error to
/// the user. We always convert from `InternalResult<T>` to `crate::Result<T>`
/// before returning to the user.
pub(crate) type IResult<T> = Result<T, ()>;
