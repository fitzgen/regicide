use crate::context::ContextInner;
use crate::entity::{Block, EntityRepr, Reg, SpillSlot, Val};
use crate::error::{IResult, InternalError};
use crate::function::Function;
use crate::timing::Timing;
use alloc::vec::Vec;

/// TODO FITZGEN
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Allocation<E = u32>
where
    E: EntityRepr,
{
    /// TODO FITZGEN
    Reg(Reg<E>),
    /// TODO FITZGEN
    Stack(SpillSlot<E>),
}

/// TODO FITZGEN
pub enum Move<E = u32>
where
    E: EntityRepr,
{
    /// TODO FITZGEN
    RegReg {
        /// TODO FITZGEN
        from: Reg<E>,
        /// TODO FITZGEN
        to: Reg<E>,
    },

    /// TODO FITZGEN
    Spill {
        /// TODO FITZGEN
        from: Reg<E>,
        /// TODO FITZGEN
        to: SpillSlot<E>,
    },

    /// TODO FITZGEN
    Reload {
        /// TODO FITZGEN
        from: SpillSlot<E>,
        /// TODO FITZGEN
        to: Reg<E>,
    },
}

/// TODO FITZGEN
pub struct Remat<E = u32>
where
    E: EntityRepr,
{
    /// TODO FITZGEN
    pub val: Val<E>,

    /// TODO FITZGEN
    pub srcs: [Reg<E>; 2],

    /// TODO FITZGEN
    pub dest: Reg<E>,
}

/// TODO FITZGEN
pub struct CriticalEdgeMove<E = u32>
where
    E: EntityRepr,
{
    /// TODO FITZGEN
    pub target: Block<E>,

    /// TODO FITZGEN
    pub move_: Move<E>,
}

/// TODO FITZGEN
pub enum Edit<E = u32>
where
    E: EntityRepr,
{
    /// TODO FITZGEN
    Move(Move<E>),

    /// TODO FITZGEN
    Remat(Remat<E>),

    /// TODO FITZGEN
    CriticalEdgeMove(CriticalEdgeMove<E>),
}

/// TODO FITZGEN
pub struct Output {
    pub(crate) which: Option<WhichOutput>,
    pub(crate) output8: OutputInner<u8>,
    pub(crate) output16: OutputInner<u16>,
    pub(crate) output32: OutputInner<u32>,
}

#[allow(dead_code)] // TODO FITZGEN
pub(crate) enum WhichOutput {
    Output8,
    Output16,
    Output32,
}

impl Default for Output {
    fn default() -> Self {
        Self::new()
    }
}

impl Output {
    /// TODO FITZGEN
    pub const fn new() -> Self {
        Self {
            which: None,
            output8: OutputInner::new(),
            output16: OutputInner::new(),
            output32: OutputInner::new(),
        }
    }

    /// TODO FITZGEN
    pub fn reset(&mut self) {
        let Self {
            which,
            output8,
            output16,
            output32,
        } = self;
        *which = None;
        output8.reset();
        output16.reset();
        output32.reset();
    }

    /// TODO FITZGEN
    pub fn is_reset(&self) -> bool {
        let Self {
            which,
            output8,
            output16,
            output32,
        } = self;
        which.is_none() && output8.is_reset() && output16.is_reset() && output32.is_reset()
    }

    /// TODO FITZGEN
    pub fn block_insts_and_edits(&self, func: &impl Function, block: Block) -> OutputIter<'_> {
        let _ = (func, block);
        OutputIter { output: self }
    }
}

/// TODO FITZGEN
pub struct OutputIter<'a> {
    #[allow(dead_code)] // TODO FITZGEN
    output: &'a Output,
    // TODO: ...
}

pub(crate) struct OutputInner<E: EntityRepr> {
    error: Option<InternalError>,
    edits: Vec<Edit<E>>,
}

impl<E: EntityRepr> OutputInner<E> {
    const fn new() -> Self {
        Self {
            error: None,
            edits: Vec::new(),
        }
    }

    fn reset(&mut self) {
        let Self { error, edits } = self;
        *error = None;
        edits.clear();
    }

    pub fn is_reset(&self) -> bool {
        let Self { error, edits } = self;
        error.is_none() && edits.is_empty()
    }

    pub fn construct(
        &mut self,
        context: &mut ContextInner<E>,
        func: &impl Function,
    ) -> IResult<()> {
        let _timing = Timing::new("output");
        let _ = (self, context, func);
        todo!()
    }

    #[allow(dead_code)] // TODO FITZGEN
    pub fn error<T>(&mut self, error: impl Into<InternalError>) -> IResult<T> {
        debug_assert!(self.error.is_none());
        self.error = Some(error.into());
        Err(())
    }

    pub fn take_error(&mut self) -> InternalError {
        self.error.take().unwrap()
    }
}
