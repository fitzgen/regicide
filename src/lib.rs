//! `regicide` is a register allocator.
//!
//! TODO FITZGEN

#![deny(missing_docs)]
#![no_std]
#![allow(unused)] // TODO FITZGEN

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

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
mod dfs;
mod dominators;
mod entity;
mod error;
mod input;
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
mod validation;

#[cfg(any(test, feature = "checker"))]
pub mod checker;
#[cfg(any(test, fuzz))]
pub mod test;

pub use context::Context;
pub use entity::{Block, Entity, EntityRepr, PrimaryMap, PrimaryMapKeys, Reg, SpillSlot, Val};
pub use error::{Error, Result};
use input::DisplayWithOutput;
pub use input::{Input, InputBlock, InputFunction, InputInst, InputMachine, Operand, RematCost};
pub use output::{Allocation, CriticalEdgeMove, Edit, Move, Output, Remat};

use context::ContextInner;
use error::{IResult, InternalError};
use output::{OutputInner, WhichOutput};

/// TODO FITZGEN
pub fn run(
    context: &mut Context,
    output: &mut Output,
    input: &Input<impl InputFunction>,
) -> Result<()> {
    assert!(context.is_reset());
    assert!(output.is_reset());

    #[cfg(feature = "entity-repr-8")]
    if input.func.len_values() <= 1 << 7 {
        output.which = Some(WhichOutput::Output8);
        match run_inner(&mut context.context8, &mut output.output8, input) {
            Ok(()) => return Ok(()),
            Err(()) => match output.output8.take_error() {
                InternalError::EntityReprTooSmall => {}
                InternalError::Error(e) => return Err(e),
            },
        }
    }

    #[cfg(feature = "entity-repr-16")]
    if input.func.len_values() <= 1 << 15 {
        output.which = Some(WhichOutput::Output16);
        match run_inner(&mut context.context16, &mut output.output16, input) {
            Ok(()) => return Ok(()),
            Err(()) => match output.output16.take_error() {
                InternalError::EntityReprTooSmall => {}
                InternalError::Error(e) => return Err(e),
            },
        }
    }

    output.which = Some(WhichOutput::Output32);
    match run_inner(&mut context.context32, &mut output.output32, input) {
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
    input: &Input<impl InputFunction>,
) -> IResult<()>
where
    E: EntityRepr,
{
    assert!(context.is_reset());
    assert!(output.is_reset());

    trace!(
        "====== register allocation input ======\n\
         {input}\n\
         ======================================="
    );

    if input.options.validate_input {
        validation::validate(input.func, output)?;
    }

    context
        .sccs
        .construct(input.func, &mut context.counts, &mut context.dfs, output)?;
    context
        .region_tree
        .construct(input.func, &mut context.counts, &context.sccs, output)?;
    context
        .liveness
        .construct(input.func, &mut context.counts, &mut context.dfs, output)?;
    context
        .live_ranges
        .construct(input.func, &context.region_tree, &context.liveness)?;

    partial_allocation::partial_allocate(context, input.func)?;
    region_allocation::region_allocate(context, input.func)?;
    spill_slots::allocate_spill_slots(context, input.func)?;
    move_elimination::eliminate_moves(context, input.func)?;

    output.construct(context, input.func)?;

    trace!(
        "====== register allocation output ======\n\
         {}\n\
         ========================================",
        DisplayWithOutput::new(input.func.display(), output),
    );
    trace!("counts = {:#?}", context.counts);
    Ok(())
}
