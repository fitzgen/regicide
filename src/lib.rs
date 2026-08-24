//! `regicide` is a register allocator.
//!
//! TODO FITZGEN

#![deny(missing_docs)]
#![no_std]

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

#[macro_use]
mod entity;

mod btree;
mod coalescing;
mod context;
mod counts;
mod dfs;
mod dominators;
mod error;
mod input;
mod live_ranges;
mod liveness;
mod machine;
mod move_elimination;
mod output;
mod packed_float;
mod parallel_moves;
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
pub use entity::{Block, Entity, EntityRepr, Inst, SpillSlot, Val};
pub use error::{Error, Result};
pub use input::{
    DefUse, Input, InputBlock, InputFunction, InputInst, InputValue, Operand, OperandConstraint,
    Position, RematCost,
};
pub use machine::{Machine, MachineBuilder, Reg, RegBank, RegClass, RegGroup, RegSet, RegUnit};
pub use output::{Allocation, CriticalEdgeMove, Edit, Move, Output, Remat};

use context::ContextInner;
use error::{IResult, InternalError};
use input::DisplayWithOutput;
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
    if entity_repr_can_likely_fit::<u8>(input) {
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
    if entity_repr_can_likely_fit::<u16>(input) {
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

/// Is `E` likely wide enough to describe this allocation problem?
#[cfg(any(feature = "entity-repr-8", feature = "entity-repr-16"))]
fn entity_repr_can_likely_fit<E>(input: &Input<impl InputFunction>) -> bool
where
    E: EntityRepr,
{
    input.func.len_values() <= Val::<E>::MAX_REPRESENTABLE.index() + 1
        && input.func.len_insts() <= max_representable_inst_index::<E>()
        && input.machine.num_registers() <= Reg::<E>::MAX_REPRESENTABLE.index() + 1
}

#[cfg(any(feature = "entity-repr-8", feature = "entity-repr-16"))]
fn max_representable_inst_index<E>() -> usize
where
    E: EntityRepr,
{
    core::cmp::min(
        entity::Inst::<E>::MAX_REPRESENTABLE.index(),
        live_ranges::LivePoint::<E>::MAX_INST_INDEX,
    )
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
        validation::validate(input, output)?;
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
        .construct(input, &mut context.counts, &mut context.liveness, output)?;

    coalescing::coalesce(context, input, output)?;
    region_allocation::region_allocate(context, input)?;
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
