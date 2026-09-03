//! Spill slot allocation.
//!
//! At this point, we've already decided which bundles get spilled to the
//! stack. We haven't decided which stack slot a value gets spilled to or how
//! many total spill slots we need. That is this pass's job.
//!
//! # The algorithm
//!
//! We color the interference graph of the spilled values directly, with the
//! classic SSA coloring of Hack, Grund, and Goos:
//!
//! * Visit the blocks in reverse post-order, and within a block visit program
//!   points in program order. Because a value's definition dominates every
//!   point where it is live, and because dominators come first in reverse
//!   post-order, this visits every value's definition before any point where
//!   that value is live.
//!
//! * At a value's definition, give it some slot of its size class that is not
//!   occupied by a value that is already live, and only create a new slot when
//!   every existing one of that size is taken. Never revisit that choice.
//!
//! That is all. There is no interference graph in memory: the set of values
//! live at the current point *is* the neighborhood of the value being colored,
//! because in a strict SSA program two values interfere exactly when one's
//! definition dominates the other's and the dominated definition's point has
//! both values live. So the set of occupied slots we carry along the walk is
//! precisely the set of colors we must avoid, and greedily avoiding them is a
//! complete coloring.
//!
//! Note that *which* free slot we pick does not matter, only that we prefer any
//! free slot over a fresh one: we create a slot only at a point where every
//! existing slot of that size is live, so each creation coincides with a new
//! record high in simultaneously live values, and the total therefore lands on
//! the maximum however we break ties. We keep a free list per size class and
//! pop the most recently freed slot off it, which is deterministic and costs
//! `O(1)` where scanning for the lowest-numbered free slot would cost `O(n)`.
//!
//! To follow the walk we need, per block, the points at which each spilled
//! value's live range ends. A backwards pass over the block's operands
//! collects them — mirroring the backwards pass in [`crate::liveness`], and
//! sharing its `for_each_operand_rev` so the two cannot disagree about where a
//! live range ends — and then the forward pass drains them in order. Live
//! ranges are half-open, so a value whose range ends at point `p` has already
//! released its slot by the time a value defined at `p` asks for one.
//!
//! # Why this algorithm, here
//!
//! The interference graph of a strict SSA program is chordal, and a dominance
//! order is a perfect elimination order for it, so greedy coloring in that
//! order uses exactly `ω` colors — the size of the largest clique, which is the
//! maximum number of simultaneously live values. In other words the coloring is
//! *optimal*: no assignment uses fewer slots. For us that means the smallest
//! possible stack frame, which is worth having, and it comes with no
//! backtracking, no iteration to a fixed point, and no heuristics to tune. We
//! assert the optimality at the end of the pass (`max_live` versus the number
//! of slots created per size class), so a bug in the walk shows up as a failed
//! assertion rather than as quietly larger frames.
//!
//! The reason we cannot allocate *registers* this way — and the reason this
//! module looks nothing like [`crate::region_allocation`] — is that the theorem
//! only speaks to the chromatic number. It says how many colors suffice; it
//! says nothing about *which* color a value may take. Real register allocation
//! is full of constraints on which color: an operand pinned to a particular
//! register, register classes that overlap and alias, register groups, a
//! caller-saved register clobbered by a call. And the resource is finite, so
//! when `ω > k` something must be evicted, split, or spilled, and splitting
//! destroys the SSA form the theorem needs. None of that is true of stack
//! slots. Slots are interchangeable within a size class, there is no `k` to
//! exceed, and creating another slot never fails. What is a hard problem for
//! registers is the textbook easy case for slots, so we solve it exactly.
//!
//! # The size class is a size, not a bank
//!
//! Registers are grouped into banks, and a value can only live in a register of
//! its own bank. Stack slots have no such rule: a slot is just bytes in the
//! frame, so all that a value asks of one is that it be wide enough. Two banks
//! whose registers are the same width therefore draw upon a single pool of
//! slots, and a function that spills an integer and a float with disjoint live
//! ranges spends one slot on them rather than two.
//!
//! Sizes are powers of two ([`crate::MachineBuilder::declare_reg_bank`] rejects
//! anything else), so a size class is an index
//! [`RegBank::log2_size`][crate::machine::RegBank::log2_size] into a fixed
//! array of [`RegBank::NUM_SIZES`] entries, and needs no map.
//!
//! References:
//!
//! * Sebastian Hack, Daniel Grund, and Gerhard Goos, "Register Allocation for
//!   Programs in SSA-Form", CC 2006.
//!   <https://doi.org/10.1007/11688839_20>
//!
//! * Sebastian Hack and Gerhard Goos, "Optimal register allocation for SSA-form
//!   programs in polynomial time", Information Processing Letters 98(4), 2006.
//!   <https://doi.org/10.1016/j.ipl.2006.01.008>
//!
//! * Sebastian Hack, "Register Allocation for Programs in SSA Form", PhD
//!   thesis, Universität Karlsruhe, 2007.
//!   <https://doi.org/10.5445/KSP/1000007166>
//!
//! * Fernando Magno Quintão Pereira and Jens Palsberg, "Register Allocation via
//!   Coloring of Chordal Graphs", APLAS 2005.
//!   <https://doi.org/10.1007/11575467_21>
//!
//! * Philip Brisk, Foad Dabiri, Jamie Macbeth, and Majid Sarrafzadeh,
//!   "Polynomial-Time Graph Coloring Register Allocation", IWLS 2005. (Proves
//!   the weaker result that strict SSA interference graphs are perfect.)
//!
//! # What this pass does not do
//!
//! It assigns slot *indices*, not stack frame offsets: laying the frame out is
//! a downstream concern, and later phases may still add slots of their own
//! (see [`crate::parallel_moves`]).
//!
//! It also assigns a slot to a value's *whole* live range, including the
//! stretches where region allocation kept the value in a register. That is a
//! deliberate over-approximation, and it buys two things: all of a value's
//! split pieces share one slot, so a stack-to-stack move is never needed; and a
//! value that was reloaded but not modified still has the current value sitting
//! in its slot, so re-spilling it later needs no store at all.

use crate::{
    Block, Entity as _, Val,
    context::ContextInner,
    counts::Counts,
    entity::{EntityRepr, EntitySet, PrimaryMap, SecondaryMap},
    error::IResult,
    input::{DefUse, Input, InputBlock as _, InputFunction, Position},
    live_ranges::{LivePoint, LiveRanges},
    liveness::{Liveness, for_each_operand_rev},
    machine::RegBank,
    output::OutputInner,
    region_allocation::RegionAllocation,
    rpo::Rpo,
    timing::Timing,
};
use alloc::vec::Vec;

define_entities! {
    /// A slot in the stack frame that a spilled value lives in.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct SpillSlot = "stack";
}

/// Run the spill slot allocation pass.
pub(crate) fn allocate_spill_slots<E>(
    context: &mut ContextInner<E>,
    input: &Input<'_, impl InputFunction>,
    output: &mut OutputInner<E>,
) -> IResult<()>
where
    E: EntityRepr,
{
    let _timing = Timing::new("allocate spill slots");

    let ContextInner {
        counts,
        rpo,
        region_tree: _,
        liveness,
        live_ranges,
        dfs: _,
        coalescing: _,
        region_allocation,
        spill_slots,
    } = context;

    spill_slots.allocate(
        input,
        counts,
        rpo,
        liveness,
        live_ranges,
        region_allocation,
        output,
    )
}

/// What happens to a spilled value at a program point during a block's walk.
///
/// The derived ordering puts `Kill` before `Def` at the same point: a value
/// whose range ends at `p` has released its slot before a value defined at `p`
/// looks for one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Event {
    /// The value's live range ends here, so its slot becomes free.
    Kill,

    /// The value is defined here, so it needs a slot.
    Def,
}

/// The stack slots we created, and which spilled value lives in which.
pub struct SpillSlots<E>
where
    E: EntityRepr,
{
    /// Every slot we have created, and the base-two logarithm of the size of
    /// the values it holds.
    slots: PrimaryMap<SpillSlot<E>, u8>,

    /// The slot each spilled value lives in, or `None` for values that were
    /// never spilled.
    val_slot: SecondaryMap<Val<E>, Option<SpillSlot<E>>>,

    /// The values that need a slot, gathered from region allocation's stack
    /// bundles.
    spilled: EntitySet<Val<E>>,

    /// The largest number of spilled values of each size that are ever
    /// simultaneously live, indexed by the base-two logarithm of that size.
    ///
    /// Because the coloring is optimal, this is also exactly how many slots we
    /// create for that size, and is asserted by `check_optimality`.
    max_live: [u32; RegBank::NUM_SIZES],

    /// How many spilled values of each size are live at the walk's current
    /// point, indexed by the base-two logarithm of that size.
    live_count: [u32; RegBank::NUM_SIZES],

    /// The slots that are occupied at the walk's current point.
    in_use: EntitySet<SpillSlot<E>>,

    /// The slots that are *not* occupied at the walk's current point, bucketed
    /// by the base-two logarithm of their size.
    ///
    /// This is the complement of `in_use`, kept in a form we can pop a slot off
    /// in constant time.
    free_slots: [Vec<SpillSlot<E>>; RegBank::NUM_SIZES],

    /// The current block's events, in ascending program order once sorted.
    events: Vec<(LivePoint<E>, Event, Val<E>)>,

    /// The spilled values live at the walk's current point.
    live: EntitySet<Val<E>>,
}

impl<E> SpillSlots<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        SpillSlots {
            slots: PrimaryMap::new(),
            val_slot: SecondaryMap::new(None),
            spilled: EntitySet::new(),
            max_live: [0; RegBank::NUM_SIZES],
            live_count: [0; RegBank::NUM_SIZES],
            in_use: EntitySet::new(),
            free_slots: [const { Vec::new() }; RegBank::NUM_SIZES],
            events: Vec::new(),
            live: EntitySet::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            slots,
            val_slot,
            spilled,
            max_live,
            live_count,
            in_use,
            free_slots,
            events,
            live,
        } = self;
        slots.reset();
        val_slot.reset();
        spilled.reset();
        *max_live = [0; RegBank::NUM_SIZES];
        debug_assert!(live_count.iter().all(|&n| n == 0));
        debug_assert!(in_use.is_empty());
        debug_assert!(free_slots.iter().all(|free| free.is_empty()));
        debug_assert!(events.is_empty());
        debug_assert!(live.is_empty());
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            slots,
            val_slot,
            spilled,
            max_live,
            live_count,
            in_use,
            free_slots,
            events,
            live,
        } = self;
        slots.is_reset()
            && val_slot.is_reset()
            && spilled.is_reset()
            && max_live.iter().all(|&n| n == 0)
            && live_count.iter().all(|&n| n == 0)
            && in_use.is_empty()
            && free_slots.iter().all(|free| free.is_empty())
            && events.is_empty()
            && live.is_empty()
    }

    /// How many stack slots did we create?
    #[allow(dead_code, reason = "consumed by the phases that are still to come")]
    pub fn len_slots(&self) -> usize {
        self.slots.len()
    }

    /// Allocate every spilled value a stack slot.
    fn allocate(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        rpo: &Rpo<E>,
        liveness: &Liveness<E>,
        live_ranges: &LiveRanges<E>,
        region_allocation: &RegionAllocation<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        debug_assert!(self.is_reset());
        self.collect_spilled_values(counts, live_ranges, region_allocation);
        self.color(input, counts, rpo, liveness, output)
    }

    /// Gather the values that need a stack slot: everything covered by a bundle
    /// that region allocation could not keep in a register.
    fn collect_spilled_values(
        &mut self,
        counts: &mut Counts,
        live_ranges: &LiveRanges<E>,
        region_allocation: &RegionAllocation<E>,
    ) {
        for bundle in region_allocation.stack_bundles().iter().copied() {
            for span in bundle.spans(live_ranges) {
                if self.spilled.insert(span.val(live_ranges)) {
                    counts.spilled_values.inc();
                }
            }
        }
        trace!(
            "spill slots: {} values need a stack slot",
            self.spilled.len()
        );
    }

    /// Color `self.spilled`: walk the blocks in reverse post-order, greedily
    /// giving each spilled value a slot of its size that is free where the
    /// value is defined.
    fn color(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        rpo: &Rpo<E>,
        liveness: &Liveness<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        if self.spilled.is_empty() {
            return Ok(());
        }

        for block in rpo.iter() {
            self.allocate_block(input, counts, liveness, block, output)?;
        }

        self.check_every_spilled_value_has_a_slot();
        self.check_optimality();

        counts.spill_slots += self.slots.len();
        Ok(())
    }

    /// Color every spilled value defined within `block`.
    fn allocate_block(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        liveness: &Liveness<E>,
        block: Block<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        trace!("spill slots: coloring {block:?}");
        debug_assert!(self.in_use.is_empty());
        debug_assert!(self.free_slots.iter().all(|free| free.is_empty()));
        debug_assert!(self.live_count.iter().all(|&n| n == 0));
        debug_assert!(self.events.is_empty());
        debug_assert!(self.live.is_empty());

        self.enter_block(input, counts, liveness, block, output)?;
        self.collect_events(input, liveness, block, output)?;

        self.events.sort_unstable();
        let mut events = core::mem::take(&mut self.events);
        for (point, event, val) in events.drain(..) {
            match event {
                Event::Kill => self.free(input, val),
                Event::Def => {
                    let _ = point;
                    self.assign(input, counts, val, output)?;
                }
            }
        }
        self.events = events;

        self.in_use.reset();
        for free in &mut self.free_slots {
            free.clear();
        }
        self.live_count = [0; RegBank::NUM_SIZES];
        Ok(())
    }

    /// Set up `in_use` for a walk of `block`, from the values live on entry to
    /// it.
    ///
    /// A live-in value whose definition is in some other block already has a
    /// slot, because that block dominates this one and so came earlier in
    /// reverse post-order; it just marks its slot occupied. A live-in value
    /// with no slot yet can only be one of this block's own parameters, which
    /// are defined on the incoming edges, so this is where we color them.
    fn enter_block(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        liveness: &Liveness<E>,
        block: Block<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        // First color the live-in values that already have spill slot
        // assignments. We want to make sure they retain their same slot.
        for val in block.live_in(liveness) {
            if !self.spilled.contains(val) {
                continue;
            }
            if let Some(slot) = self.val_slot[val] {
                self.occupy(input, slot, val);
            }
        }

        // All other slots are free in this block. Rebuild the free lists
        // accordingly.
        debug_assert!(self.free_slots.iter().all(|free| free.is_empty()));
        for (slot, &log2_size) in self.slots.iter() {
            if !self.in_use.contains(slot) {
                self.free_slots[usize::from(log2_size)].push(slot);
            }
        }

        // Color the live-in values that did not already have slots assigned,
        // which therefore must be this block's live block parameters.
        for val in block.live_in(liveness) {
            if !self.spilled.contains(val) || self.val_slot[val].is_some() {
                continue;
            }
            debug_assert!(
                input
                    .func
                    .block(block.with_repr32())
                    .params()
                    .any(|param| param.with_repr::<E>() == Some(val)),
                "{val:?} is live on entry to {block:?} without a slot, so it must be one of \
                 {block:?}'s parameters",
            );
            self.assign(input, counts, val, output)?;
        }

        Ok(())
    }

    /// Walk `block` backwards, recording where each spilled value is defined
    /// and where its live range ends.
    fn collect_events(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        liveness: &Liveness<E>,
        block: Block<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        // Everything live at the block's exit outlives the block, so it never
        // gets a kill here.
        for val in block.live_out(liveness) {
            if self.spilled.contains(val) {
                self.live.insert(val);
            }
        }

        let input_block = input.func.block(block.with_repr32());
        let spilled = &self.spilled;
        let live = &mut self.live;

        let mut events = core::mem::take(&mut self.events);
        let result = for_each_operand_rev(&input_block, output, |_output, point, _i, kind, val| {
            if !spilled.contains(val) {
                return Ok(());
            }
            match kind {
                // A definition of a value that is live afterwards: its range
                // ends at a use or block exit we have already seen.
                DefUse::Def if live.remove(val) => events.push((point, Event::Def, val)),

                // A dead definition: nothing reads the value, so its range is
                // just the rest of the instruction that defines it.
                //
                // It is tempting to omit this case but we cannot: an
                // instruction that *must* write to the stack, for example,
                // needs to have a destination for that write, even if nothing
                // else in the program uses that result, and the instruction was
                // just used for other side effects. In this scenario, we cannot
                // reuse an existing stack slot either, because doing so would
                // clobber that existing stack slot's value. So, just as we do
                // in live span construction, we treat it as live across its
                // single defining instruction and then otherwise process it
                // like we do other values.
                DefUse::Def => {
                    let end = LivePoint::new(point.inst(), Position::Late).next_point();
                    events.push((point, Event::Def, val));
                    events.push((end, Event::Kill, val));
                }

                // The last use of the value within this block, since we are
                // walking backwards and had not seen it live yet.
                DefUse::Use if live.insert(val) => {
                    events.push((point.next_point(), Event::Kill, val))
                }

                DefUse::Use => {}
            }
            Ok(())
        });
        self.events = events;

        result?;

        // Whatever is still live is live on entry to the block, and was already
        // accounted for by `enter_block`.
        self.live.reset();

        Ok(())
    }

    /// Give `val` a free slot of its size, creating a new slot when every
    /// existing one of that size is occupied.
    fn assign(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        val: Val<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        debug_assert!(self.spilled.contains(val));
        debug_assert!(
            self.val_slot[val].is_none(),
            "{val:?} has a single definition in SSA, so we color it exactly once",
        );

        let log2_size = val.log2_size(input);
        let slot = match self.free_slots[usize::from(log2_size)].pop() {
            Some(slot) => slot,
            None => self.slots.push(output, log2_size)?,
        };

        self.val_slot[val] = Some(slot);
        self.occupy(input, slot, val);
        counts.spill_slot_assignments.inc();
        trace!(
            "spill slots: assigned {val:?} to {slot:?} ({} bytes)",
            1 << log2_size
        );
        Ok(())
    }

    /// Mark `slot` occupied by `val`, which is live at the walk's current
    /// point.
    fn occupy(&mut self, input: &Input<'_, impl InputFunction>, slot: SpillSlot<E>, val: Val<E>) {
        let inserted = self.in_use.insert(slot);
        debug_assert!(
            inserted,
            "{slot:?} is already occupied, so {val:?} may not have it too",
        );

        let log2_size = usize::from(val.log2_size(input));
        debug_assert_eq!(usize::from(self.slots[slot]), log2_size);

        self.live_count[log2_size] += 1;
        self.max_live[log2_size] =
            core::cmp::max(self.max_live[log2_size], self.live_count[log2_size]);
    }

    /// Release the slot that `val` occupies: its live range has ended.
    fn free(&mut self, input: &Input<'_, impl InputFunction>, val: Val<E>) {
        let slot = self.val_slot[val].expect("only a value with an assigned slot can be killed");
        let removed = self.in_use.remove(slot);
        debug_assert!(removed, "{val:?} held {slot:?}, so it was occupied");

        let log2_size = usize::from(val.log2_size(input));
        debug_assert_eq!(usize::from(self.slots[slot]), log2_size);

        self.free_slots[log2_size].push(slot);
        self.live_count[log2_size] -= 1;
    }

    fn check_every_spilled_value_has_a_slot(&self) {
        if !cfg!(debug_assertions) {
            return;
        }
        for val in self.spilled.iter() {
            debug_assert!(
                self.val_slot[val].is_some(),
                "{val:?} needs a stack slot but never got one; is it defined in an unreachable \
                 block?",
            );
        }
    }

    /// Check that we created no more slots than the largest number of
    /// simultaneously live spilled values requires, which is the whole point of
    /// coloring in dominance order.
    fn check_optimality(&self) {
        if !cfg!(debug_assertions) {
            return;
        }
        let mut per_size = [0u32; RegBank::NUM_SIZES];
        for log2_size in self.slots.values() {
            per_size[usize::from(*log2_size)] += 1;
        }
        for (log2_size, count) in per_size.iter().copied().enumerate() {
            debug_assert_eq!(
                count,
                self.max_live[log2_size],
                "created {count} slots of {} bytes but at most {} values of that size are ever \
                 simultaneously live; the coloring should be optimal",
                1 << log2_size,
                self.max_live[log2_size],
            );
        }
    }
}

impl<E> Default for SpillSlots<E>
where
    E: EntityRepr,
{
    fn default() -> Self {
        Self::new()
    }
}

/// Spill slot queries about a value.
impl<E> Val<E>
where
    E: EntityRepr,
{
    /// The stack slot this value lives in, or `None` if it was never spilled.
    #[allow(dead_code, reason = "consumed by the phases that are still to come")]
    pub(crate) fn spill_slot(self, spill_slots: &SpillSlots<E>) -> Option<SpillSlot<E>> {
        spill_slots.val_slot[self]
    }
}

impl<E> SpillSlot<E>
where
    E: EntityRepr,
{
    /// The base-two logarithm of the byte size of the values this slot holds.
    #[allow(dead_code, reason = "consumed by the phases that are still to come")]
    pub(crate) fn log2_size(self, spill_slots: &SpillSlots<E>) -> u8 {
        spill_slots.slots[self]
    }

    /// The byte size of this slot.
    #[allow(dead_code, reason = "consumed by the phases that are still to come")]
    pub(crate) fn size(self, spill_slots: &SpillSlots<E>) -> u16 {
        1 << self.log2_size(spill_slots)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        RegClass,
        context::{Context, ContextInner},
        input::OperandConstraint,
        test::{TestInput, TestMachine},
    };
    use mutatis::check::{Check, CheckResult};
    use std::{
        collections::{BTreeMap, BTreeSet},
        format,
        string::String,
        vec::Vec,
    };

    /// Run every phase up through spill slot allocation.
    ///
    /// Returns `None` when register allocation itself gave up on this input,
    /// e.g. because the function needs more registers at once than the machine
    /// has; there are no spill slots to check in that case.
    fn allocate(test_input: &TestInput) -> Result<Option<Context>, String> {
        let mut context = Context::new();
        let mut output = OutputInner::<u32>::new();
        assert!(context.is_reset());

        let result = test_input.with_input(|input| -> IResult<()> {
            let context = &mut context.context32;
            let func = input.func;
            context.rpo.construct(func, &mut context.dfs, &mut output)?;
            context.region_tree.construct(
                func,
                &mut context.counts,
                &mut context.dfs,
                &mut output,
            )?;
            context
                .liveness
                .construct(func, &mut context.counts, &context.rpo, &mut output)?;
            context.live_ranges.construct(
                input,
                &mut context.counts,
                &mut context.liveness,
                &mut output,
            )?;
            crate::coalescing::coalesce(context, input, &mut output)?;
            crate::region_allocation::region_allocate(context, input, &mut output)?;
            allocate_spill_slots(context, input, &mut output)
        });

        if result.is_err() {
            return match output.take_error() {
                // Not every function can be allocated on every machine, and
                // that is not this pass's problem.
                crate::error::InternalError::Error(crate::Error::TooManyLiveRegs) => Ok(None),
                error => Err(format!("allocation failed: {error:?}")),
            };
        }

        Ok(Some(context))
    }

    /// Run the analyses that spill slot allocation depends on: reverse
    /// post-order, the region tree, liveness, and live ranges.
    fn analyze(
        context: &mut ContextInner<u32>,
        input: &Input<'_, crate::test::TestFunction>,
        output: &mut OutputInner<u32>,
    ) -> Result<(), String> {
        let func = input.func;
        let result = context
            .rpo
            .construct(func, &mut context.dfs, output)
            .and_then(|()| {
                context
                    .region_tree
                    .construct(func, &mut context.counts, &mut context.dfs, output)
            })
            .and_then(|()| {
                context
                    .liveness
                    .construct(func, &mut context.counts, &context.rpo, output)
            })
            .and_then(|()| {
                context.live_ranges.construct(
                    input,
                    &mut context.counts,
                    &mut context.liveness,
                    output,
                )
            });
        result.map_err(|()| format!("analysis failed: {:?}", output.take_error()))
    }

    /// Each spilled value's live range, as a list of half-open intervals.
    ///
    /// Read back out of the live spans that the rest of the allocator works
    /// with, rather than by repeating the walk under test, so that a bug in the
    /// walk cannot hide itself here.
    fn live_ranges_of(
        context: &ContextInner<u32>,
    ) -> BTreeMap<Val<u32>, Vec<(LivePoint<u32>, LivePoint<u32>)>> {
        let live_ranges = &context.live_ranges;
        let spill_slots = &context.spill_slots;

        let mut ranges: BTreeMap<Val<u32>, Vec<_>> = BTreeMap::new();
        for span in live_ranges.spans() {
            let val = span.val(live_ranges);
            if spill_slots.spilled.contains(val) {
                ranges
                    .entry(val)
                    .or_default()
                    .push((span.start(live_ranges), span.end(live_ranges)));
            }
        }
        ranges
    }

    fn ranges_overlap(
        a: &[(LivePoint<u32>, LivePoint<u32>)],
        b: &[(LivePoint<u32>, LivePoint<u32>)],
    ) -> bool {
        a.iter().any(|&(a_start, a_end)| {
            b.iter()
                .any(|&(b_start, b_end)| LivePoint::spans_overlap(a_start, a_end, b_start, b_end))
        })
    }

    /// Color `test_input`, spilling every `stride`th value that has a live
    /// range, and check the properties the coloring is supposed to have.
    fn check_coloring(test_input: &TestInput, stride: usize) -> Result<(), String> {
        let mut context = Context::new();
        let mut output = OutputInner::<u32>::new();

        test_input.with_input(|input| -> Result<(), String> {
            let context = &mut context.context32;
            analyze(context, input, &mut output)?;

            // Choose which values to spill. Only values that have a live range
            // are eligible: a value that is neither defined nor used anywhere
            // has nothing to keep in a slot.
            //
            // Driving the coloring from a set we pick, rather than from the set
            // that register allocation happens to produce, lets us cover far
            // more interference shapes than the constraints in a random test
            // function would ever spill.
            let mut vals: Vec<Val<u32>> = context
                .live_ranges
                .spans()
                .map(|span| span.val(&context.live_ranges))
                .collect();
            vals.sort_unstable();
            vals.dedup();
            for (i, val) in vals.iter().copied().enumerate() {
                if i % stride == 0 {
                    context.spill_slots.spilled.insert(val);
                }
            }
            let spilled: BTreeSet<Val<u32>> = vals
                .iter()
                .copied()
                .enumerate()
                .filter(|(i, _)| i % stride == 0)
                .map(|(_, val)| val)
                .collect();

            context
                .spill_slots
                .color(
                    input,
                    &mut context.counts,
                    &context.rpo,
                    &context.liveness,
                    &mut output,
                )
                .map_err(|()| format!("coloring failed: {:?}", output.take_error()))?;

            let spill_slots = &context.spill_slots;

            // Property 1: a value has a slot exactly when we asked for it to be
            // spilled.
            let actual: BTreeSet<Val<u32>> = vals
                .iter()
                .copied()
                .filter(|val| val.spill_slot(spill_slots).is_some())
                .collect();
            if actual != spilled {
                return Err(format!(
                    "the values with a spill slot are {actual:?} but the values we spilled are \
                     {spilled:?}"
                ));
            }

            let ranges = live_ranges_of(context);
            let log2_size_of = |val: Val<u32>| val.reg_bank(input).log2_size(input.machine);

            for (&a, a_ranges) in &ranges {
                for (&b, b_ranges) in &ranges {
                    if a >= b {
                        continue;
                    }
                    let (Some(a_slot), Some(b_slot)) =
                        (a.spill_slot(spill_slots), b.spill_slot(spill_slots))
                    else {
                        continue;
                    };
                    if a_slot != b_slot {
                        continue;
                    }

                    // Property 2: values that share a slot are never live at
                    // the same time, so neither can clobber the other.
                    if ranges_overlap(a_ranges, b_ranges) {
                        return Err(format!(
                            "{a:?} and {b:?} both live in {a_slot:?} but their live ranges \
                             {a_ranges:?} and {b_ranges:?} overlap"
                        ));
                    }

                    // Property 3: values that share a slot are the same size.
                    // Note that they need *not* be in the same bank: pooling
                    // slots across banks of equal size is the whole point.
                    if log2_size_of(a) != log2_size_of(b) {
                        return Err(format!(
                            "{a:?} and {b:?} both live in {a_slot:?} but they are {} and {} \
                             bytes wide",
                            1 << log2_size_of(a),
                            1 << log2_size_of(b),
                        ));
                    }
                }
            }

            // Property 4: the allocation is optimal. For each size, we created
            // exactly as many slots as the largest number of spilled values of
            // that size that are ever simultaneously live. No allocation can do
            // better, because those values all need distinct slots at that
            // point.
            let mut created: BTreeMap<u16, usize> = BTreeMap::new();
            for (slot, _) in spill_slots.slots.iter() {
                *created.entry(slot.size(spill_slots)).or_default() += 1;
            }

            // A maximum clique of an interval graph is always found at some
            // interval's start point, so those are the only points we need to
            // look at.
            let mut needed: BTreeMap<u16, usize> = BTreeMap::new();
            let points: Vec<LivePoint<u32>> =
                ranges.values().flatten().map(|&(start, _)| start).collect();
            for point in points {
                let mut live_here: BTreeMap<u16, usize> = BTreeMap::new();
                for (&val, val_ranges) in &ranges {
                    if val_ranges
                        .iter()
                        .any(|&(start, end)| start <= point && point < end)
                    {
                        *live_here.entry(1 << log2_size_of(val)).or_default() += 1;
                    }
                }
                for (size, count) in live_here {
                    let entry = needed.entry(size).or_default();
                    *entry = (*entry).max(count);
                }
            }

            if created != needed {
                return Err(format!(
                    "created {created:?} slots per size, but the maximum number of \
                     simultaneously live spilled values per size is {needed:?}"
                ));
            }

            Ok(())
        })
    }

    /// Running the whole pipeline, up to and including this pass, never panics
    /// and never trips a debug assertion.
    ///
    /// This is the only test that drives every phase in sequence, so it is
    /// where a broken invariant in an earlier phase surfaces. It checks nothing
    /// about the result; `spill_slot_properties` does that.
    #[test]
    fn the_whole_pipeline_runs() -> CheckResult<TestInput> {
        Check::new()
            .iters(10_000)
            .run(|test_input: &TestInput| -> Result<(), String> {
                allocate(test_input)?;
                Ok(())
            })
    }

    #[test]
    fn spill_slot_properties() -> CheckResult<TestInput> {
        Check::new()
            .iters(10_000)
            .run(|test_input: &TestInput| -> Result<(), String> {
                // Spill everything, which maximizes the pressure on the
                // coloring, and then every other value, which interleaves
                // spilled and unspilled values.
                for stride in [1, 2] {
                    check_coloring(test_input, stride)?;
                }
                Ok(())
            })
    }

    /// A value whose only use must be on the stack gets a stack slot, and it is
    /// the only slot we create.
    #[test]
    fn a_single_stack_use_gets_the_first_slot() {
        let test_input = TestInput::with_use_constraints(&[OperandConstraint::Stack]);
        let context = allocate(&test_input).unwrap().unwrap();
        let spill_slots = &context.context32.spill_slots;

        assert_eq!(spill_slots.len_slots(), 1);

        let val = Val::<u32>::try_new(0).unwrap();
        let slot = val.spill_slot(spill_slots).unwrap();
        assert_eq!(slot.index(), 0);
    }

    /// Nothing spills when every use can be satisfied in a register, and then
    /// we create no slots at all.
    #[test]
    fn no_slots_when_nothing_spills() {
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();
        let test_input = TestInput::with_use_constraints(&[OperandConstraint::Reg(class)]);
        let context = allocate(&test_input).unwrap().unwrap();
        let spill_slots = &context.context32.spill_slots;

        assert_eq!(spill_slots.len_slots(), 0);
        assert!(spill_slots.spilled.is_empty());
        assert_eq!(
            Val::<u32>::try_new(0).unwrap().spill_slot(spill_slots),
            None
        );
    }
}
