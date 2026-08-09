//! `regicide` is a register allocator.
//!
//! TODO FITZGEN

#![deny(missing_docs)]
#![no_std]
#![allow(unused)] // TODO FITZGEN

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

// TODO: stats/counts instrumentation

#[doc(hidden)]
#[macro_export]
macro_rules! trace {
    ($($tt:tt)*) => {
        if cfg!(any(feature = "trace-log", debug_assertions)) {
            ::log::trace!($($tt)*);
        }
    };
}

mod btree;
mod context;
mod counts;
mod entity;
mod error;
mod function;
mod live_ranges;
mod liveness;
mod move_elimination;
mod output;
mod parallel_moves;
mod partial_allocation;
mod region_allocation;
mod region_tree;
mod sccs;
mod spill_slots;
mod timing;
mod union_find;

#[cfg(feature = "checker")]
pub mod checker;
#[cfg(test)]
pub mod test;

pub use context::Context;
pub use entity::{Block, Entity, EntityRepr, PrimaryMap, PrimaryMapKeys, Reg, SpillSlot, Val};
pub use error::{Error, Result};
pub use function::{Function, Operand, RematCost};
pub use output::{Allocation, CriticalEdgeMove, Edit, Move, Output, Remat};

use context::ContextInner;
use error::{IResult, InternalError};
use output::{OutputInner, WhichOutput};

/// TODO FITZGEN
pub fn run(context: &mut Context, output: &mut Output, func: &impl Function) -> Result<()> {
    assert!(context.is_reset());
    assert!(output.is_reset());

    if func.len_values() <= 1 << 7 {
        output.which = Some(WhichOutput::Output8);
        match run_inner(&mut context.context8, &mut output.output8, func) {
            Ok(()) => return Ok(()),
            Err(()) => match output.output8.take_error() {
                InternalError::EntityReprTooSmall => {}
                InternalError::Error(e) => return Err(e),
            },
        }
    }

    if func.len_values() <= 1 << 15 {
        output.which = Some(WhichOutput::Output16);
        match run_inner(&mut context.context16, &mut output.output16, func) {
            Ok(()) => return Ok(()),
            Err(()) => match output.output16.take_error() {
                InternalError::EntityReprTooSmall => {}
                InternalError::Error(e) => return Err(e),
            },
        }
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

    context.region_tree.construct(func)?;
    context.liveness.construct(func)?;
    context
        .live_ranges
        .construct(func, &context.region_tree, &context.liveness)?;

    partial_allocation::partial_allocate(context, func)?;
    region_allocation::region_allocate(context, func)?;
    spill_slots::allocate_spill_slots(context, func)?;
    move_elimination::eliminate_moves(context, func)?;

    output.construct(context, func)?;

    trace!("counts = {:#?}", context.counts);
    Ok(())
}
