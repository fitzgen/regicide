//! `regicide` is a register allocator.
//!
//! TODO FITZGEN

#![deny(missing_docs)]
#![no_std]

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

// `alloc` has no hash map, and `src/move_generation.rs` needs one.
#[cfg(not(any(feature = "std", feature = "hashbrown")))]
compile_error!(
    "regicide needs a hash map: enable either the `std` feature or the `hashbrown` feature"
);

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
mod move_generation;
mod output;
mod packed_float;
mod parallel_moves;
mod region_allocation;
mod region_tree;
mod rpo;
mod sccs;
mod spill_placement;
mod spill_slot_allocation;
mod timing;
mod union_find;
mod validation;

#[cfg(any(test, feature = "checker"))]
pub mod checker;
#[cfg(any(test, fuzz))]
pub mod test;

pub use context::Context;
pub use entity::{Block, Entity, EntityRepr, Inst, Val};
pub use error::{Error, Result};
pub use input::{
    DefUse, Input, InputBlock, InputFunction, InputInst, InputValue, Operand, OperandConstraint,
    Position, RematCost,
};
pub use machine::{Machine, MachineBuilder, Reg, RegBank, RegClass, RegGroup, RegSet, RegUnit};
pub use output::{
    Allocation, CriticalEdgeEdit, EdgeEdit, Edit, InstOrEdit, Move, Output, OutputIter,
    RegAllocation, Remat, ScalarAllocation, StackAllocation,
};
pub use spill_slot_allocation::{SpillSlot, SpillSlotGroup, SpillSlotSize};

use context::{ContextInner, WhichContext};
use error::{IResult, InternalError};
use input::DisplayWithContext;

mod hash_map {
    #[cfg(not(feature = "std"))]
    pub use hashbrown::{HashMap, hash_map::Entry};
    #[cfg(feature = "std")]
    pub use std::collections::{HashMap, hash_map::Entry};

    use rustc_hash::FxBuildHasher;

    pub type FxHashMap<K, V> = HashMap<K, V, FxBuildHasher>;
}

/// TODO FITZGEN
pub fn run<'a>(context: &'a mut Context, input: &Input<impl InputFunction>) -> Result<Output<'a>> {
    run_dispatch(context, input)?;
    Ok(Output::new(context))
}

/// Solve `input` under the narrowest entity representation it fits in.
fn run_dispatch(context: &mut Context, input: &Input<impl InputFunction>) -> Result<()> {
    assert!(context.is_reset());

    #[cfg(feature = "entity-repr-8")]
    if entity_repr_can_likely_fit::<u8>(input) {
        context.which = Some(WhichContext::Context8);
        match run_inner(&mut context.context8, input) {
            Ok(()) => return Ok(()),
            Err(()) => match context.context8.output.take_error() {
                InternalError::EntityReprTooSmall => {}
                InternalError::Error(e) => return Err(e),
            },
        }
    }

    #[cfg(feature = "entity-repr-16")]
    if entity_repr_can_likely_fit::<u16>(input) {
        context.which = Some(WhichContext::Context16);
        match run_inner(&mut context.context16, input) {
            Ok(()) => return Ok(()),
            Err(()) => match context.context16.output.take_error() {
                InternalError::EntityReprTooSmall => {}
                InternalError::Error(e) => return Err(e),
            },
        }
    }

    context.which = Some(WhichContext::Context32);
    match run_inner(&mut context.context32, input) {
        Ok(()) => Ok(()),
        Err(()) => match context.context32.output.take_error() {
            InternalError::EntityReprTooSmall => unreachable!(),
            InternalError::Error(e) => Err(e),
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

fn run_inner<E>(context: &mut ContextInner<E>, input: &Input<impl InputFunction>) -> IResult<()>
where
    E: EntityRepr,
{
    assert!(context.is_reset());

    trace!(
        "====== register allocation input ======\n\
         {input}\n\
         ======================================="
    );

    {
        let ContextInner {
            counts,
            rpo,
            region_tree,
            liveness,
            live_ranges,
            dfs,
            output,
            ..
        } = &mut *context;

        if input.options.validate_input {
            validation::validate(input, output)?;
        }

        rpo.construct(input.func, dfs, output)?;
        region_tree.construct(input.func, counts, dfs, output)?;
        liveness.construct(input.func, counts, rpo, output)?;
        live_ranges.construct(input, counts, liveness, output)?;
    }

    coalescing::coalesce(context, input)?;
    region_allocation::region_allocate(context, input)?;
    spill_slot_allocation::allocate_spill_slots(context, input)?;
    spill_placement::place_spills(context, input)?;
    move_generation::generate_moves(context, input)?;
    move_elimination::eliminate_moves(context, input)?;

    {
        let ContextInner {
            rpo,
            live_ranges,
            spill_slots,
            output,
            ..
        } = &mut *context;
        output.construct(input.func, rpo, live_ranges, spill_slots)?;
    }

    trace!(
        "====== register allocation output ======\n\
         {}\n\
         ========================================",
        DisplayWithContext::new(input.func.display(), context),
    );
    trace!("counts = {:#?}", context.counts);
    Ok(())
}
