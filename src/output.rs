use crate::context::ContextInner;
use crate::entity::{Block, Entity, EntityRepr, Reg, SpillSlot, Val};
use crate::error::{IResult, InternalError};
use crate::input::InputFunction;
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
    #[cfg(feature = "entity-repr-8")]
    pub(crate) output8: OutputInner<u8>,
    #[cfg(feature = "entity-repr-16")]
    pub(crate) output16: OutputInner<u16>,
    pub(crate) output32: OutputInner<u32>,
}

#[allow(dead_code)] // TODO FITZGEN
pub(crate) enum WhichOutput {
    #[cfg(feature = "entity-repr-8")]
    Output8,
    #[cfg(feature = "entity-repr-16")]
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
            #[cfg(feature = "entity-repr-8")]
            output8: OutputInner::new(),
            #[cfg(feature = "entity-repr-16")]
            output16: OutputInner::new(),
            output32: OutputInner::new(),
        }
    }

    /// TODO FITZGEN
    pub fn reset(&mut self) {
        let Self {
            which,
            #[cfg(feature = "entity-repr-8")]
            output8,
            #[cfg(feature = "entity-repr-16")]
            output16,
            output32,
        } = self;
        *which = None;
        #[cfg(feature = "entity-repr-8")]
        output8.reset();
        #[cfg(feature = "entity-repr-16")]
        output16.reset();
        output32.reset();
    }

    /// TODO FITZGEN
    pub fn is_reset(&self) -> bool {
        let Self {
            which,
            #[cfg(feature = "entity-repr-8")]
            output8,
            #[cfg(feature = "entity-repr-8")]
            output16,
            output32,
        } = self;

        #[cfg(feature = "entity-repr-8")]
        if !output8.is_reset() {
            return false;
        }

        #[cfg(feature = "entity-repr-16")]
        if !output16.is_reset() {
            return false;
        }

        which.is_none() && output32.is_reset()
    }

    /// TODO FITZGEN
    pub fn block_insts_and_edits(&self, func: &impl InputFunction, block: Block) -> OutputIter<'_> {
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
    pub const fn new() -> Self {
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
        func: &impl InputFunction,
    ) -> IResult<()> {
        let _timing = Timing::new("output");
        let _ = (self, context, func);
        todo!()
    }

    #[inline]
    pub fn entity<Ent>(&mut self, index: usize) -> IResult<Ent>
    where
        Ent: Entity,
    {
        match Ent::try_new(index) {
            Some(e) => Ok(e),
            None => self.error(InternalError::EntityReprTooSmall),
        }
    }

    #[inline]
    pub fn with_repr<R, Ent>(&mut self, entity: Ent) -> IResult<Ent::Family<R>>
    where
        Ent: Entity,
        R: EntityRepr,
    {
        match entity.with_repr::<R>() {
            Some(e) => Ok(e),
            None => self.error(InternalError::EntityReprTooSmall),
        }
    }

    #[inline]
    pub fn result<T, Err>(&mut self, result: Result<T, Err>) -> IResult<T>
    where
        Err: Into<InternalError>,
    {
        match result {
            Ok(x) => Ok(x),
            Err(e) => self.error(e),
        }
    }

    #[inline]
    pub fn error<T>(&mut self, error: impl Into<InternalError>) -> IResult<T> {
        debug_assert!(self.error.is_none());
        self.error = Some(error.into());
        Err(())
    }

    pub fn take_error(&mut self) -> InternalError {
        self.error.take().unwrap()
    }
}
