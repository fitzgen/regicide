//! The region tree.
//!
//! A region is a set of basic blocks whose contained live ranges are allocated
//! together. We never allocate across regions.
//!
//! To make this effictive, we create regions for each loop in the control-flow
//! graph, and for the function's top level.

use core::marker::PhantomData;

use crate::context::ContextInner;
use crate::entity::EntityRepr;
use crate::error::IResult;
use crate::input::InputFunction;
use crate::timing::Timing;

pub struct RegionTree<E>
where
    E: EntityRepr,
{
    _todo: PhantomData<E>,
}
impl<E> RegionTree<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        RegionTree { _todo: PhantomData }
    }

    pub fn reset(&mut self) {
        let Self { _todo } = self;
    }

    pub fn is_reset(&self) -> bool {
        let Self { _todo } = self;
        true
    }

    pub fn construct(&mut self, func: &impl InputFunction) -> IResult<()> {
        let _timing = Timing::new("region tree");
        // TODO
        let _ = func;
        Ok(())
    }
}
