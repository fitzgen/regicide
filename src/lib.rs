#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![cfg_attr(docsrs, feature(doc_cfg))]
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
#[macro_use]
mod events;

mod coalescing;
mod context;
mod counts;
mod dead_move_elimination;
mod demanded_moves;
mod dfs;
mod dominators;
mod error;
mod input;
mod interval_sets;
mod live_ranges;
mod liveness;
mod machine;
mod move_generation;
mod output;
mod packed_float;
mod parallel_moves;
mod redundant_move_elimination;
mod region_allocation;
mod region_tree;
mod rpo;
mod sorted_vec;
mod spill_placement;
mod spill_slot_allocation;
mod spilled_live_ranges;
mod timing;
mod union_find;
mod validation;
#[cfg(feature = "visualizer")]
mod visualizer;

#[cfg(any(test, feature = "checker"))]
pub mod checker;
#[cfg(feature = "deserialize")]
pub mod deserialize;
#[cfg(feature = "serialize")]
pub mod serialize;

#[cfg(any(test, feature = "test-utils"))]
#[doc(hidden)]
pub mod test;

pub use context::Context;
pub use entity::{Block, Entity, EntityRepr, Inst, Val};
pub use error::{Error, Result};
pub use input::{
    BlockFrequency, DefUse, DisplayFuncWithContext, DisplayInputBlock, DisplayInputFunction,
    DisplayWithContext, Input, InputBlock, InputFunction, InputInst, InputOptions, InputValue,
    MoveEliminationLevel, Operand, OperandConstraint, Position, RematCost,
};
pub use live_ranges::MAX_OPERANDS_PER_INST;
pub use machine::{Machine, MachineBuilder, Reg, RegBank, RegClass, RegGroup, RegSet, RegUnit};
pub use output::{
    Allocation, CriticalEdgeEdit, EdgeEdit, Edit, InstOrEdit, Move, Output, OutputIter,
    RegAllocation, Remat, ScalarAllocation, StackAllocation,
};
pub use spill_slot_allocation::{SpillSlot, SpillSlotGroup, SpillSlotSize};

use context::{ContextInner, WhichContext};
use error::{IResult, InternalError};

mod hash_map {
    #[cfg(feature = "std")]
    pub use std::collections::{HashMap, hash_map::Entry};

    #[cfg(not(feature = "std"))]
    pub use hashbrown::{HashMap, hash_map::Entry};

    #[cfg(not(any(feature = "std", feature = "hashbrown")))]
    compile_error!(
        "regicide needs a hash map: enable either the `std` cargo feature or \
         the `hashbrown` cargo feature"
    );

    use rustc_hash::FxBuildHasher;

    pub type FxHashMap<K, V> = HashMap<K, V, FxBuildHasher>;
}

mod hash_set {
    #[cfg(feature = "std")]
    pub use std::collections::HashSet;

    #[cfg(not(feature = "std"))]
    pub use hashbrown::HashSet;

    use rustc_hash::FxBuildHasher;

    pub type FxHashSet<T> = HashSet<T, FxBuildHasher>;
}

#[cfg(any(feature = "serialize", feature = "deserialize"))]
const ENCODING_FORMAT_VERSION: u32 = 3;

/// TODO FITZGEN
pub fn run<'a>(context: &'a mut Context, input: &Input<impl InputFunction>) -> Result<Output<'a>> {
    run_dispatch(context, input)?;
    Ok(Output::new(context))
}

/// Solve `input` under `u32`.
///
/// The narrow representations still exist, and `Output` still reads a context
/// holding one, but neither is tried. They were meant to buy locality, and
/// they do not buy enough of it: a `LivePoint` packs into
/// `EntityRepr::Wide`, which maxes out at `u32`, so `LivePoint<u16>` is the
/// same four bytes as `LivePoint<u32>`. `u8` does halve a point, but a
/// narrower entity also means a fallible conversion at every boundary with
/// the `u32`-indexed input, and the attempt is abandoned outright when some
/// entity derived during allocation -- a span, a use, a bundle -- outgrows
/// the representation, which the up-front check cannot predict.
fn run_dispatch(context: &mut Context, input: &Input<impl InputFunction>) -> Result<()> {
    assert!(context.is_reset());

    context.which = Some(WhichContext::Context32);
    match run_inner(&mut context.context32, input) {
        Ok(()) => Ok(()),
        Err(()) => match context.context32.output.take_error() {
            InternalError::EntityReprTooSmall => unreachable!(),
            InternalError::Error(e) => Err(e),
        },
    }
}

/// The largest instruction index `E` can describe.
///
/// Both the `Inst<E>` entity and the `LivePoint<E>` packing have to hold an
/// index, and which of the two binds depends on `E`, so this takes the
/// smaller. `run_dispatch` allocates under `u32` alone now, but the narrow
/// representations are still usable, and `live_ranges`'s tests pin down that
/// the one-past-the-end point every block exit needs stays representable in
/// each of them.
#[cfg(test)]
fn max_representable_inst_index<E>() -> usize
where
    E: EntityRepr,
{
    core::cmp::min(
        entity::Inst::<E>::MAX_REPRESENTABLE.index(),
        live_ranges::LivePoint::<E>::MAX_INST_INDEX,
    )
}

/// Drop the edits that redundant- and dead-move elimination proved unnecessary,
/// and apply demanded-move hoisting's changes.
///
/// No pass removes its own. All three number their indices against the edit
/// list as move generation left it, as do the `index` fields of every event they
/// log and of `Event::MoveEmitted`, so the removal happens once, here, after all
/// of them have run.
fn remove_eliminated_edits<E>(context: &mut ContextInner<E>)
where
    E: EntityRepr,
{
    let redundant = &context.redundant_move_elimination.eliminated;
    let dead = &mut context.dead_move_elimination;
    let hoisted = &context.demanded_moves;

    // Each list is sorted and duplicate free, and they are disjoint because
    // each later pass skips every index an earlier one took, so the merge is
    // strictly increasing as `remove_and_insert_edits` requires.
    dead.to_remove.clear();
    dead.to_remove
        .reserve(redundant.len() + dead.eliminated.len() + hoisted.eliminated.len());
    dead.to_remove.extend(redundant.iter().copied());
    dead.to_remove.extend(dead.eliminated.iter().copied());
    dead.to_remove.extend(hoisted.eliminated.iter().copied());
    dead.to_remove.sort_unstable();
    debug_assert!(
        dead.to_remove.windows(2).all(|w| w[0] < w[1]),
        "the passes' eliminated-edit lists must each be sorted and be \
         disjoint from one another",
    );

    context
        .move_generation
        .remove_and_insert_edits(&dead.to_remove, &hoisted.inserted);
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

    if input.options.validate_input {
        validation::validate(input, &mut context.output)?;
    }

    context
        .rpo
        .construct(input.func, &mut context.dfs, &mut context.output)?;
    context.region_tree.construct(
        input.func,
        &mut context.counts,
        &mut context.dfs,
        &mut context.output,
    )?;
    context.liveness.construct(
        input.func,
        &mut context.counts,
        &context.rpo,
        &mut context.output,
    )?;
    context.live_ranges.construct(
        input,
        &mut context.counts,
        &mut context.events,
        &mut context.liveness,
        &mut context.output,
    )?;

    coalescing::coalesce(context, input)?;
    region_allocation::region_allocate(context, input)?;
    spill_placement::place_spills(context, input)?;
    spill_slot_allocation::allocate_spill_slots(context, input)?;
    move_generation::generate_moves(context, input)?;

    context.output.construct(
        input.func,
        input.machine,
        &context.rpo,
        &context.live_ranges,
        &context.spill_slots,
    )?;

    context.redundant_move_elimination.recorded.enabled = demanded_moves::wants_recording(input);
    redundant_move_elimination::eliminate_redundant_moves(context, input)?;
    dead_move_elimination::eliminate_dead_moves(context, input)?;
    demanded_moves::hoist_demanded_moves(context, input)?;

    remove_eliminated_edits(context);

    trace!(
        "====== register allocation output ======\n\
         {}\n\
         ========================================",
        DisplayWithContext::new(input.func.display(), context),
    );
    trace!("counts = {:#?}", context.counts);
    Ok(())
}
