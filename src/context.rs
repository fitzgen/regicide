use crate::EntityRepr;

/// TODO FITZGEN
pub struct Context {
    pub(crate) context8: ContextInner<u8>,
    pub(crate) context16: ContextInner<u16>,
    pub(crate) context32: ContextInner<u32>,
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

impl Context {
    /// TODO FITZGEN
    pub const fn new() -> Self {
        Self {
            context8: ContextInner::new(),
            context16: ContextInner::new(),
            context32: ContextInner::new(),
        }
    }

    /// TODO FITZGEN
    pub fn reset(&mut self) {
        let Self {
            context8,
            context16,
            context32,
        } = self;
        context8.reset();
        context16.reset();
        context32.reset();
    }

    /// TODO FITZGEN
    pub fn is_reset(&self) -> bool {
        let Self {
            context8,
            context16,
            context32,
        } = self;
        context8.is_reset() && context16.is_reset() && context32.is_reset()
    }
}

pub(crate) struct ContextInner<E: EntityRepr> {
    _todo: core::marker::PhantomData<E>,
}

impl<E: EntityRepr> ContextInner<E> {
    const fn new() -> Self {
        Self {
            _todo: core::marker::PhantomData,
        }
    }

    pub(crate) fn reset(&mut self) {
        let Self { _todo } = self;
    }

    pub(crate) fn is_reset(&self) -> bool {
        let Self { _todo } = self;
        true
    }
}
