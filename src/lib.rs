//! TODO FITZGEN

#![deny(missing_docs)]
#![no_std]
#![allow(unused)] // TODO FITZGEN

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

mod context;
mod entity;
mod error;
mod function;
mod live_ranges;
mod output;
mod partial_allocation;
mod region_allocation;
mod region_tree;
mod union_find;

pub use context::Context;
pub use entity::{Block, Entity, EntityRepr, Reg, SpillSlot, Val};
pub use error::{Error, Result};
pub use function::Function;
pub use output::{CriticalEdgeMove, Edit, Move, Output, Remat};

use context::ContextInner;
use error::{IResult, InternalError};
use output::{OutputInner, WhichOutput};

/// TODO FITZGEN
pub fn run(context: &mut Context, output: &mut Output, func: &impl Function) -> Result<()> {
    assert!(context.is_reset());
    assert!(output.is_reset());

    output.which = Some(WhichOutput::Output8);
    match run_inner(&mut context.context8, &mut output.output8, func) {
        Ok(()) => return Ok(()),
        Err(()) => match output.output8.take_error() {
            InternalError::EntityReprTooSmall => {}
            InternalError::Error(e) => return Err(e),
        },
    }

    output.which = Some(WhichOutput::Output16);
    match run_inner(&mut context.context16, &mut output.output16, func) {
        Ok(()) => return Ok(()),
        Err(()) => match output.output16.take_error() {
            InternalError::EntityReprTooSmall => {}
            InternalError::Error(e) => return Err(e),
        },
    }

    output.which = Some(WhichOutput::Output32);
    match run_inner(&mut context.context32, &mut output.output32, func) {
        Ok(()) => Ok(()),
        Err(()) => match output.output32.take_error() {
            InternalError::EntityReprTooSmall => unreachable!(),
            InternalError::Error(e) => return Err(e),
        },
    }
}

fn run_inner<E>(
    context: &mut ContextInner<E>,
    output: &mut OutputInner<E>,
    func: &impl Function,
) -> IResult<()>
where
    E: EntityRepr,
{
    assert!(context.is_reset());
    assert!(output.is_reset());
    region_tree::construct_region_tree(context, func)?;
    live_ranges::construct_live_ranges(context, func)?;
    partial_allocation::partial_allocation(context, func)?;
    region_allocation::region_allocation(context, func)?;
    output.construct(context, func)?;
    Ok(())
}
