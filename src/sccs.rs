//! Strongly-connected components.

use crate::{entity::EntityRepr, error::IResult, function::Function};
use core::marker::PhantomData;

pub struct StronglyConnectedComponents<E>
where
    E: EntityRepr,
{
    _todo: PhantomData<E>,
}

impl<E> StronglyConnectedComponents<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        StronglyConnectedComponents { _todo: PhantomData }
    }

    pub fn reset(&mut self) {
        let Self { _todo } = self;
    }

    pub fn is_reset(&self) -> bool {
        let Self { _todo } = self;
        true
    }

    pub fn construct(&mut self, func: &impl Function) -> IResult<()> {
        // TODO
        let _ = func;
        Ok(())
    }
}
