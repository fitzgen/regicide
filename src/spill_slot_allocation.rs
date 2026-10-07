//! Spill slot allocation.
//!
//! At this point, we've already decided which bundles get spilled to the
//! stack. We haven't decided which stack slot a value gets spilled to or how
//! many total spill slots we need. That is this pass's job.
//!
//! We color the interference graph of the spilled values directly, with the
//! classic SSA coloring algorithm of Hack, Grund, and Goos:
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
//! Which free slot a value gets does not matter to the coloring, but it does to
//! the code: a block parameter in a different slot than its argument costs a
//! stack-to-stack move on that edge. So before the walk, we union parameters
//! with their arguments into *slot classes* wherever their reservations do not
//! overlap, taking the heaviest edges first since one union can rule out a
//! later one. The walk then gives each value its class's slot when that is
//! free, and otherwise a slot no other class has been promised there.
//!
//! Why use this allocation algorithm here? Why not reuse the region allocation
//! algorithm? Hack et al showed that the above algorithm is optimal: there is
//! no coloring that uses fewer colors (spill slots). This gives us optimally
//! sized stack frames and avoids stack-to-stack moves. To flip the question on
//! its head: why don't we use this algorithm for region allocation? Because
//! things like a fixed number of colors (registers) and pre-coloring (fixed
//! register constraints) break the algorithm and force a return to either
//! NP-completeness or suboptimality. Spill slot allocation just happens to
//! perfectly fit into the shape that this algorithm requires.
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

use crate::{
    Block, Entity as _, Val,
    context::ContextInner,
    counts::Counts,
    entity::{EntityRange, EntityRepr, EntitySet, PrimaryMap, SecondaryMap},
    error::IResult,
    events::EventsLog,
    input::{DefUse, Input, InputBlock as _, InputFunction, Position},
    live_ranges::{LivePoint, LiveRanges, LiveSpan},
    liveness::{Liveness, for_each_operand_rev},
    machine::RegBank,
    output::{Allocation, OutputInner, StackAllocation},
    region_allocation::RegionAllocation,
    region_tree::RegionTree,
    rpo::Rpo,
    spilled_live_ranges::{RangeEvent, SpilledLiveRanges},
    timing::Timing,
};
use alloc::vec::Vec;
use slot_classes::{SlotClasses, block_weight};

mod slot_classes;

define_entities! {
    /// A slot in the stack frame that a spilled value lives in.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct SpillSlot = "stack";

    /// The spill slots that together hold one value in a class of register
    /// groups: one slot per group member, in member order.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct SpillSlotGroup = "stack_group";

    /// An index into the contiguous storage of every spill slot group's
    /// members.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct SpillSlotGroupMembersIndex = "spill_slot_group_members_index";
}

/// The size of a spill slot: a power-of-two number of bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SpillSlotSize(u8);

#[cfg(feature = "serialize")]
impl serde::Serialize for SpillSlotSize {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_u16(self.size())
    }
}

impl SpillSlotSize {
    /// Create a `SpillSlotSize` of `size` bytes.
    ///
    /// Returns `None` if `size` is not a power of two.
    #[inline]
    pub fn new(size: u16) -> Option<Self> {
        if size.is_power_of_two() {
            let log2_size = u8::try_from(size.trailing_zeros()).unwrap();
            Some(Self::from_log2(log2_size))
        } else {
            None
        }
    }

    /// The byte size of a spill slot of this size.
    #[inline]
    pub fn size(self) -> u16 {
        1 << self.0
    }

    /// The base-two logarithm of the byte size of a spill slot of this size.
    #[inline]
    pub fn log2_size(self) -> u8 {
        self.0
    }

    /// Create a `SpillSlotSize` from the base-two logarithm of a byte size.
    #[inline]
    pub(crate) fn from_log2(log2_size: u8) -> Self {
        debug_assert!(usize::from(log2_size) < RegBank::NUM_SIZES);
        Self(log2_size)
    }

    /// This size's index into the per-size pools, which have one bucket per
    /// distinct size a machine can have.
    #[inline]
    pub(crate) fn index(self) -> usize {
        let index = usize::from(self.0);
        debug_assert!(index < RegBank::NUM_SIZES);
        index
    }
}

/// Run the spill slot allocation pass.
pub(crate) fn allocate_spill_slots<E>(
    context: &mut ContextInner<E>,
    input: &Input<'_, impl InputFunction>,
) -> IResult<()>
where
    E: EntityRepr,
{
    if input.options.narrow_spill_slot_live_ranges {
        context.spilled_live_ranges.construct(
            input,
            &context.rpo,
            &context.liveness,
            &context.live_ranges,
            &context.region_allocation,
            &context.spill_placement,
            &mut context.output,
        )?;
    }

    let _timing = Timing::new("allocate spill slots");

    context.spill_slots.allocate(
        input,
        &mut context.counts,
        &mut context.events,
        &context.rpo,
        &context.liveness,
        &context.region_tree,
        &context.region_allocation,
        &context.spilled_live_ranges,
        &mut context.output,
    )
}

/// Where the ranges we color come from.
///
/// Both carry the same shape, so the coloring is written once and reads
/// whichever it was handed. That is what makes any difference in the slots we
/// create attributable to the ranges alone.
#[derive(Clone, Copy)]
enum Ranges<'a, E>
where
    E: EntityRepr,
{
    /// Reserve each value's slot across the whole of its liveness.
    WholeLiveRange,

    /// Reserve each value's slot only where it is both live and spilled.
    Spilled(&'a SpilledLiveRanges<E>),
}

impl<E> Ranges<'_, E>
where
    E: EntityRepr,
{
    /// The values whose slot is reserved on entry to `block`.
    fn live_in<'a>(
        &'a self,
        liveness: &'a Liveness<E>,
        block: Block<E>,
        spilled: &'a EntitySet<Val<E>>,
    ) -> impl Iterator<Item = Val<E>> + 'a
    where
        E: 'a,
    {
        let (whole, narrowed) = match *self {
            Ranges::WholeLiveRange => (
                Some(block.live_in(liveness).filter(|&val| spilled.contains(val))),
                None,
            ),
            Ranges::Spilled(ranges) => (
                None,
                Some(ranges.live_in(block).filter(|&val| spilled.contains(val))),
            ),
        };
        whole
            .into_iter()
            .flatten()
            .chain(narrowed.into_iter().flatten())
    }
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

impl From<RangeEvent> for Event {
    fn from(event: RangeEvent) -> Self {
        match event {
            RangeEvent::Kill => Event::Kill,
            RangeEvent::Def => Event::Def,
        }
    }
}

/// `free_slots_index` for a slot that is not in `free_slots`.
const NOT_FREE: u32 = u32::MAX;

/// The stack slots we created, and which spilled value lives in which.
pub struct SpillSlots<E>
where
    E: EntityRepr,
{
    /// Every slot we have created, and the size of the values it holds.
    slots: PrimaryMap<SpillSlot<E>, SpillSlotSize>,

    /// Every group of slots we have created, and where its members are in
    /// `group_members`.
    groups: PrimaryMap<SpillSlotGroup<E>, EntityRange<SpillSlotGroupMembersIndex<E>>>,

    /// Contiguous storage for the members of every group of slots.
    group_members: PrimaryMap<SpillSlotGroupMembersIndex<E>, SpillSlot<E>>,

    /// Where each spilled value lives on the stack, or `None` for values that
    /// are never spilled.
    val_home: SecondaryMap<Val<E>, Option<StackAllocation<E>>>,

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

    /// Where each slot sits in its bucket of `free_slots`, or `NOT_FREE`.
    ///
    /// Lets `alloc_slot` take a preferred slot out of the middle of a bucket
    /// without scanning it.
    free_slots_index: SecondaryMap<SpillSlot<E>, u32>,

    /// The current block's events, in ascending program order once sorted.
    events: Vec<(LivePoint<E>, Event, Val<E>)>,

    /// The spilled values live at the walk's current point.
    live: EntitySet<Val<E>>,

    /// The emergency slots of each size, created on demand by
    /// [`Self::emergency_slot`] and bucketed by that size's base-two log.
    emergency: [Vec<SpillSlot<E>>; RegBank::NUM_SIZES],

    /// Which spilled values would rather share a slot, and the slots
    /// promised to them.
    classes: SlotClasses<E>,

    /// Scratch for `incoming_arg_slot`: each slot an argument occupies, and
    /// the weight of the edges it arrives on.
    votes: Vec<(SpillSlot<E>, f64)>,
}

impl<E> SpillSlots<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        SpillSlots {
            slots: PrimaryMap::new(),
            groups: PrimaryMap::new(),
            group_members: PrimaryMap::new(),
            val_home: SecondaryMap::new(None),
            max_live: [0; RegBank::NUM_SIZES],
            live_count: [0; RegBank::NUM_SIZES],
            in_use: EntitySet::new(),
            free_slots: [const { Vec::new() }; RegBank::NUM_SIZES],
            free_slots_index: SecondaryMap::new(NOT_FREE),
            events: Vec::new(),
            live: EntitySet::new(),
            emergency: [const { Vec::new() }; RegBank::NUM_SIZES],
            classes: SlotClasses::new(),
            votes: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            slots,
            groups,
            group_members,
            val_home,
            max_live,
            live_count,
            in_use,
            free_slots,
            free_slots_index,
            events,
            live,
            emergency,
            classes,
            votes,
        } = self;
        classes.reset();
        votes.clear();
        slots.reset();
        groups.reset();
        group_members.reset();
        val_home.reset();
        *max_live = [0; RegBank::NUM_SIZES];
        *live_count = [0; RegBank::NUM_SIZES];
        in_use.reset();
        for free in free_slots {
            free.clear();
        }
        free_slots_index.reset();
        events.clear();
        live.reset();
        for slots in emergency {
            slots.clear();
        }
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            slots,
            groups,
            group_members,
            val_home,
            max_live,
            live_count,
            in_use,
            free_slots,
            free_slots_index,
            events,
            live,
            emergency,
            classes,
            votes,
        } = self;
        classes.is_reset()
            && votes.is_empty()
            && slots.is_reset()
            && groups.is_reset()
            && group_members.is_reset()
            && val_home.is_reset()
            && max_live.iter().all(|&n| n == 0)
            && live_count.iter().all(|&n| n == 0)
            && in_use.is_empty()
            && free_slots.iter().all(|free| free.is_empty())
            && free_slots_index.is_reset()
            && events.is_empty()
            && live.is_empty()
            && emergency.iter().all(|slots| slots.is_empty())
    }

    /// Is every field that only holds state mid-walk empty?
    fn scratch_is_empty(&self) -> bool {
        self.live_count.iter().all(|&n| n == 0)
            && self.in_use.is_empty()
            && self.free_slots.iter().all(|free| free.is_empty())
            && self.events.is_empty()
            && self.live.is_empty()
    }

    /// How many stack slots did we create?
    #[allow(dead_code, reason = "consumed by the phases that are still to come")]
    pub fn len_slots(&self) -> usize {
        self.slots.len()
    }

    /// Every group of stack slots, in index order.
    #[cfg(feature = "visualizer")]
    pub(crate) fn groups(&self) -> impl ExactSizeIterator<Item = SpillSlotGroup<E>> {
        self.groups.keys()
    }

    /// Is this slot one of the emergency slots that move generation borrows,
    /// rather than one a value was assigned?
    #[cfg(feature = "visualizer")]
    pub(crate) fn is_emergency(&self, slot: SpillSlot<E>) -> bool {
        self.emergency.iter().flatten().any(|&s| s == slot)
    }

    /// The size of every slot we created, indexed by slot.
    ///
    /// The element type does not mention `E`, which is what lets
    /// `Output::spill_slots` iterate the slots of any representation with one
    /// concrete iterator type.
    pub(crate) fn sizes(&self) -> &[SpillSlotSize] {
        self.slots.as_slice()
    }

    /// Get a spill slot for breaking a cycle of parallel moves when no register is free.
    ///
    /// The slot must be of the given `size` and one for which `in_use` returns
    /// `false`.
    pub(crate) fn emergency_slot(
        &mut self,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        output: &mut OutputInner<E>,
        size: SpillSlotSize,
        mut in_use: impl FnMut(SpillSlot<E>) -> bool,
    ) -> IResult<SpillSlot<E>> {
        if let Some(&slot) = self.emergency[size.index()]
            .iter()
            .find(|&&slot| !in_use(slot))
        {
            return Ok(slot);
        }

        let slot = self.slots.push(output, size)?;
        self.emergency[size.index()].push(slot);
        counts.emergency_spill_slots.inc();
        counts.spill_slots.inc();
        event!(
            events,
            SpillSlotCreated {
                slot,
                size,
                emergency: true,
            }
        );
        trace!(
            "spill slots: created emergency {slot:?} ({} bytes)",
            size.size()
        );
        Ok(slot)
    }

    /// Allocate every spilled value a stack slot.
    fn allocate(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        rpo: &Rpo<E>,
        liveness: &Liveness<E>,
        region_tree: &RegionTree<E>,
        region_allocation: &RegionAllocation<E>,
        spilled_live_ranges: &SpilledLiveRanges<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        debug_assert!(self.is_reset());
        let spilled = region_allocation.spilled();
        trace!("spill slots: {} values need a stack slot", spilled.len());
        let ranges = if input.options.narrow_spill_slot_live_ranges {
            Ranges::Spilled(spilled_live_ranges)
        } else {
            Ranges::WholeLiveRange
        };
        if !spilled.is_empty() {
            self.form_classes(input, rpo, liveness, region_tree, spilled, ranges, output)?;
        }
        self.color(
            input,
            counts,
            events,
            rpo,
            liveness,
            region_tree,
            spilled,
            ranges,
            output,
        )?;
        debug_assert!(
            self.scratch_is_empty(),
            "a completed walk leaves no scratch behind",
        );
        Ok(())
    }

    /// Color `self.spilled`: walk the blocks in reverse post-order, greedily
    /// giving each spilled value a slot of its size that is free where the
    /// value is defined.
    fn color(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        rpo: &Rpo<E>,
        liveness: &Liveness<E>,
        region_tree: &RegionTree<E>,
        spilled: &EntitySet<Val<E>>,
        ranges: Ranges<'_, E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        if spilled.is_empty() {
            return Ok(());
        }

        for block in rpo.iter() {
            self.allocate_block(
                input,
                counts,
                events,
                liveness,
                region_tree,
                block,
                spilled,
                ranges,
                output,
            )?;
        }

        self.check_every_spilled_value_has_a_slot(spilled);
        self.check_optimality();

        counts.spill_slots += self.slots.len();
        Ok(())
    }

    /// Color every spilled value defined within `block`.
    fn allocate_block(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        liveness: &Liveness<E>,
        region_tree: &RegionTree<E>,
        block: Block<E>,
        spilled: &EntitySet<Val<E>>,
        ranges: Ranges<'_, E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        trace!("spill slots: coloring {block:?}");
        debug_assert!(self.scratch_is_empty());

        self.enter_block(
            input,
            counts,
            events,
            liveness,
            region_tree,
            block,
            spilled,
            ranges,
            output,
        )?;
        self.block_events(input, liveness, block, spilled, ranges, output)?;
        let mut block_events = core::mem::take(&mut self.events);
        for (point, event, val) in block_events.drain(..) {
            match event {
                Event::Kill => self.free(input, val),
                Event::Def => {
                    let _ = point;
                    // Defined here, so it arrives from no edge.
                    self.assign(input, counts, events, val, output, None)?;
                }
            }
        }
        self.events = block_events;

        self.in_use.reset();
        for free in &mut self.free_slots {
            for slot in free.drain(..) {
                self.free_slots_index[slot] = NOT_FREE;
            }
        }
        self.live_count = [0; RegBank::NUM_SIZES];
        Ok(())
    }

    /// Set up `in_use` for a walk of `block`, from the values whose slot is
    /// reserved on entry.
    ///
    /// A value whose range began elsewhere already has a slot, since that block
    /// came earlier in reverse post-order; it just marks the slot occupied. One
    /// without a slot has a range beginning on the incoming edges, so it is
    /// colored here. Over whole live ranges that is this block's parameters;
    /// over spilled live ranges it is nobody, since a range opens with a `Def`
    /// inside the block that holds its head.
    fn enter_block(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        liveness: &Liveness<E>,
        region_tree: &RegionTree<E>,
        block: Block<E>,
        spilled: &EntitySet<Val<E>>,
        ranges: Ranges<'_, E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        // First color the live-in values that already have spill slot
        // assignments. We want to make sure they retain their same slot.
        for val in ranges.live_in(liveness, block, spilled) {
            if self.val_home[val].is_none() {
                continue;
            }
            self.occupy_val_slots(input, val);
        }

        // All other slots are free in this block. Rebuild the free lists
        // accordingly.
        debug_assert!(self.free_slots.iter().all(|free| free.is_empty()));
        for (slot, &size) in self.slots.iter() {
            if !self.in_use.contains(slot) {
                self.free_slots_index[slot] =
                    u32::try_from(self.free_slots[size.index()].len()).unwrap();
                self.free_slots[size.index()].push(slot);
            }
        }

        for val in ranges.live_in(liveness, block, spilled) {
            if self.val_home[val].is_some() {
                continue;
            }
            debug_assert!(
                match ranges {
                    Ranges::WholeLiveRange => input
                        .func
                        .block(block.with_repr32())
                        .params()
                        .any(|param| param.with_repr::<E>() == Some(val)),
                    // A spilled live range begins inside the block holding its
                    // head, never on an edge, so this value is already colored.
                    Ranges::Spilled(_) => false,
                },
                "{val:?}'s slot is reserved on entry to {block:?} without having one, so its \
                 range must begin on an edge into {block:?}",
            );
            // Sharing an argument's slot makes that edge's move a no-op;
            // otherwise it pays a stack-to-stack move, the most expensive kind.
            let class_slot = self.classes.slot(val);
            let vote =
                self.incoming_arg_slot(input, region_tree, output, block, val, class_slot)?;
            // Where this parameter's own edges outweigh its class's slot, it
            // follows the edges, and the class keeps its slot for the rest.
            let prefer = vote.map(|(slot, _, _)| slot);
            match vote {
                Some((slot, weight, class_weight))
                    if weight > class_weight && self.free_slots_index[slot] != NOT_FREE =>
                {
                    self.assign_to(input, counts, events, val, output, slot)?;
                }
                _ => self.assign(input, counts, events, val, output, prefer)?,
            }
        }

        Ok(())
    }

    /// The free slot that `param`'s already-colored arguments occupy on the
    /// heaviest incoming edges, with those edges' weight and the weight of the
    /// edges whose argument is in `class_slot`.
    fn incoming_arg_slot(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        region_tree: &RegionTree<E>,
        output: &mut OutputInner<E>,
        block: Block<E>,
        param: Val<E>,
        class_slot: Option<SpillSlot<E>>,
    ) -> IResult<Option<(SpillSlot<E>, f64, f64)>> {
        let block32 = block.with_repr32();

        let mut index = None;
        for (i, p) in input.func.block(block32).params().enumerate() {
            if output.with_repr::<E, _>(p)? == param {
                index = Some(i);
                break;
            }
        }
        let Some(index) = index else {
            return Ok(None);
        };

        // A join has few distinct argument slots, so a short list beats a map.
        let mut votes = core::mem::take(&mut self.votes);
        debug_assert!(votes.is_empty());
        let result = self.tally_votes(input, region_tree, output, block, index, &mut votes);
        // The first slot found wins ties.
        let class_weight = votes
            .iter()
            .find(|&&(slot, _)| Some(slot) == class_slot)
            .map_or(0.0, |&(_, weight)| weight);
        let best = votes
            .iter()
            .rev()
            .copied()
            .max_by(|a, b| a.1.total_cmp(&b.1))
            .map(|(slot, weight)| (slot, weight, class_weight));
        votes.clear();
        self.votes = votes;
        result.map(|()| best)
    }

    /// Add up, per slot, the weight of the edges into `block` whose argument
    /// for its `index`th parameter is in that slot and free here.
    fn tally_votes(
        &self,
        input: &Input<'_, impl InputFunction>,
        region_tree: &RegionTree<E>,
        output: &mut OutputInner<E>,
        block: Block<E>,
        index: usize,
        votes: &mut Vec<(SpillSlot<E>, f64)>,
    ) -> IResult<()> {
        let block32 = block.with_repr32();
        for pred in input.func.block(block32).predecessors() {
            let pred_data = input.func.block(pred);
            for (i, succ) in pred_data.successors().enumerate() {
                if succ != block32 {
                    continue;
                }
                let Some(arg) = pred_data.successor_block_args(i).nth(index) else {
                    continue;
                };
                let arg = output.with_repr::<E, _>(arg)?;
                // Its slot has to be settled, and free here for us to take it.
                let Some(StackAllocation::SpillSlot(slot)) = self.val_home[arg] else {
                    continue;
                };
                if self.in_use.contains(slot) {
                    continue;
                }
                let holder = match pred_data.len_successors() {
                    1 => output.with_repr::<E, _>(pred)?,
                    _ => block,
                };
                let weight = block_weight(input, region_tree, holder);
                match votes.iter_mut().find(|(s, _)| *s == slot) {
                    Some((_, w)) => *w += weight,
                    None => votes.push((slot, weight)),
                }
            }
        }
        Ok(())
    }

    /// Union block parameters with their arguments into slot classes,
    /// wherever the members' reservations stay disjoint.
    fn form_classes(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        rpo: &Rpo<E>,
        liveness: &Liveness<E>,
        region_tree: &RegionTree<E>,
        spilled: &EntitySet<Val<E>>,
        ranges: Ranges<'_, E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        if !self
            .classes
            .collect_affinities(input, rpo, region_tree, spilled, output)?
        {
            return Ok(());
        }

        // A value in no pair is a class of its own that saves no move, so it
        // never asks for a promise and needs no reservations.
        let affine = self.classes.take_affine();
        let result = self.collect_ranges(input, rpo, liveness, &affine, ranges, output);
        self.classes.restore_affine(affine);
        result?;

        self.classes.order_affinities();
        self.classes.union_affinities();
        Ok(())
    }

    /// Record the reservations of every value in `affine` in `self.classes`.
    fn collect_ranges(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        rpo: &Rpo<E>,
        liveness: &Liveness<E>,
        affine: &EntitySet<Val<E>>,
        ranges: Ranges<'_, E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        for block in rpo.iter() {
            let block_start = block.start_point(input);
            for val in ranges.live_in(liveness, block, affine) {
                self.classes.open(val, block_start);
            }

            self.block_events(input, liveness, block, affine, ranges, output)?;
            let mut events = core::mem::take(&mut self.events);
            let result = events
                .drain(..)
                .try_for_each(|(point, event, val)| match event {
                    Event::Def => {
                        self.classes.open(val, point);
                        Ok(())
                    }
                    Event::Kill => self.classes.close(output, val, point),
                });
            self.events = events;
            result?;

            self.classes.close_all(output, block.end_point(input))?;
        }
        Ok(())
    }

    /// Fill `self.events` with the reservations of the values in `set` that
    /// begin or end within `block`, in program order.
    fn block_events(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        liveness: &Liveness<E>,
        block: Block<E>,
        set: &EntitySet<Val<E>>,
        ranges: Ranges<'_, E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        debug_assert!(self.events.is_empty());
        match ranges {
            Ranges::WholeLiveRange => {
                self.collect_events(input, liveness, block, set, output)?;
                self.events.sort_unstable();
            }
            // Already in program order, and already trimmed.
            Ranges::Spilled(spilled_live_ranges) => {
                self.events.extend(
                    spilled_live_ranges
                        .events(block)
                        .filter(|&(_, _, val)| set.contains(val))
                        .map(|(point, event, val)| (point, event.into(), val)),
                );
            }
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
        spilled: &EntitySet<Val<E>>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        // Everything live at the block's exit outlives the block, so it never
        // gets a kill here.
        for val in block.live_out(liveness) {
            if spilled.contains(val) {
                self.live.insert(val);
            }
        }

        let input_block = input.func.block(block.with_repr32());
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
    ///
    /// `prefer` names a slot to take if it happens to be free, which is how a
    /// block parameter lands in the same slot as the argument feeding it and
    /// so needs no move on the edge at all.
    fn assign(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        val: Val<E>,
        output: &mut OutputInner<E>,
        prefer: Option<SpillSlot<E>>,
    ) -> IResult<()> {
        debug_assert!(
            self.val_home[val].is_none(),
            "{val:?} has a single definition in SSA, so we color it exactly once",
        );

        let size = val.reg_bank(input).size(input.machine);
        let num_regs = val.num_regs(input);

        let home = if num_regs == 1 {
            StackAllocation::SpillSlot(self.alloc_class_slot(events, size, val, output, prefer)?)
        } else {
            // A multi-slot value has no single slot to match, so the
            // preference does not apply to it.
            let _ = prefer;
            let start = self.group_members.next_key(output)?;
            for _ in 0..num_regs {
                let slot = self.alloc_slot(events, size, output, None)?;
                self.group_members.push(output, slot)?;
            }
            let end = self.group_members.next_key(output)?;
            let group = self.groups.push(output, EntityRange { start, end })?;
            // After its members' events, so that the log never names a slot
            // before creating it.
            event!(
                events,
                SpillSlotGroupCreated {
                    group,
                    members: group.members(self).to_vec(),
                    size,
                }
            );
            StackAllocation::SpillSlotGroup(group)
        };

        self.record_home(input, counts, events, val, home);
        Ok(())
    }

    /// Settle `val`'s stack home, which is free here, and occupy it.
    fn record_home(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        val: Val<E>,
        home: StackAllocation<E>,
    ) {
        self.val_home[val] = Some(home);
        self.occupy_val_slots(input, val);

        counts.spill_slot_assignments.inc();
        event!(events, SpillSlotAssigned { val, slot: home });
        trace!(
            "spill slots: assigned {val:?} to {home:?}: {} slot(s) of {} bytes",
            val.num_regs(input),
            val.reg_bank(input).size(input.machine).size(),
        );
    }

    /// Give single-slot `val` the free slot `slot`, bypassing its class.
    fn assign_to(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        val: Val<E>,
        output: &mut OutputInner<E>,
        slot: SpillSlot<E>,
    ) -> IResult<()> {
        debug_assert!(self.val_home[val].is_none());
        debug_assert_eq!(val.num_regs(input), 1);
        let size = val.reg_bank(input).size(input.machine);
        let slot = self.alloc_slot(events, size, output, Some(slot))?;
        self.record_home(input, counts, events, val, StackAllocation::SpillSlot(slot));
        Ok(())
    }

    /// Take a free slot for single-slot `val`.
    ///
    /// The first time a member of a class is colored, the class is promised a
    /// free slot that no other class's promise overlaps, so that later members
    /// find it free. When none is left, or a value in no class needs a slot,
    /// it takes the free slot whose promises are worth the least.
    fn alloc_class_slot(
        &mut self,
        events: &mut EventsLog<E>,
        size: SpillSlotSize,
        val: Val<E>,
        output: &mut OutputInner<E>,
        prefer: Option<SpillSlot<E>>,
    ) -> IResult<SpillSlot<E>> {
        if let Some(slot) = self.classes.slot(val)
            && self.free_slots_index[slot] != NOT_FREE
        {
            return self.alloc_slot(events, size, output, Some(slot));
        }

        let prefer =
            prefer.filter(|&p| self.slots[p] == size && self.free_slots_index[p] != NOT_FREE);
        let free = core::mem::take(&mut self.free_slots[size.index()]);
        // `prefer` first, then the slot `alloc_slot` would take by default.
        let candidates = || {
            prefer.into_iter().chain(
                free.iter()
                    .rev()
                    .copied()
                    .filter(move |&s| Some(s) != prefer),
            )
        };

        let slot = if !self.classes.saves_moves(val) {
            self.classes.least_promised(candidates())
        } else if !self.classes.awaits_promise(val) {
            // Promised already, but that slot is taken here, which breaks the
            // promise for `val` alone. Taking the least-promised slot instead
            // displaces more classes downstream than it spares.
            prefer
        } else {
            match candidates().find(|&slot| self.classes.try_promise(val, slot)) {
                Some(slot) => Some(slot),
                None => self.classes.least_promised(candidates()),
            }
        };
        self.free_slots[size.index()] = free;

        let num_slots = self.slots.len();
        let slot = self.alloc_slot(events, size, output, slot)?;
        // A new slot has nothing promised over it yet.
        if self.slots.len() > num_slots
            && self.classes.saves_moves(val)
            && self.classes.awaits_promise(val)
        {
            let promised = self.classes.try_promise(val, slot);
            debug_assert!(promised);
        }
        Ok(slot)
    }

    /// Take a free slot of the given size, creating a new one when every
    /// existing slot of that size is occupied.
    fn alloc_slot(
        &mut self,
        events: &mut EventsLog<E>,
        size: SpillSlotSize,
        output: &mut OutputInner<E>,
        prefer: Option<SpillSlot<E>>,
    ) -> IResult<SpillSlot<E>> {
        // Any free slot is as good as any other to the coloring, so taking the
        // preferred one costs nothing and saves a stack-to-stack move.
        if let Some(want) = prefer
            && self.slots[want] == size
            && self.free_slots_index[want] != NOT_FREE
        {
            self.take_free_slot(size, usize::try_from(self.free_slots_index[want]).unwrap());
            return Ok(want);
        }

        let free = &self.free_slots[size.index()];
        match free.last().copied() {
            Some(slot) => {
                self.take_free_slot(size, free.len() - 1);
                Ok(slot)
            }
            None => {
                let slot = self.slots.push(output, size)?;
                event!(
                    events,
                    SpillSlotCreated {
                        slot,
                        size,
                        emergency: false,
                    }
                );
                Ok(slot)
            }
        }
    }

    /// Remove the slot at `i` in `size`'s bucket of `free_slots`, keeping
    /// `free_slots_index` in step with the `swap_remove`.
    fn take_free_slot(&mut self, size: SpillSlotSize, i: usize) {
        let free = &mut self.free_slots[size.index()];
        let slot = free.swap_remove(i);
        self.free_slots_index[slot] = NOT_FREE;
        // `swap_remove` moved the bucket's last slot into `i`, unless it was
        // the one removed.
        if let Some(&moved) = free.get(i) {
            self.free_slots_index[moved] = u32::try_from(i).unwrap();
        }
    }

    /// Mark all of `val`'s slots as occupied by `val`, which is live at the
    /// walk's current point.
    fn occupy_val_slots(&mut self, input: &Input<'_, impl InputFunction>, val: Val<E>) {
        let home = self.val_home[val].expect("only a value with a stack home can be occupied");
        for i in 0..home.len_scalars(self) {
            let slot = home.nth_scalar(self, i);

            let inserted = self.in_use.insert(slot);
            debug_assert!(
                inserted,
                "{slot:?} is already occupied, so {val:?} may not have it too",
            );

            let size = val.reg_bank(input).size(input.machine);
            debug_assert_eq!(self.slots[slot], size);

            self.live_count[size.index()] += 1;

            self.max_live[size.index()] =
                core::cmp::max(self.max_live[size.index()], self.live_count[size.index()]);
        }
    }

    /// Release the slots that `val` occupies.
    fn free(&mut self, input: &Input<'_, impl InputFunction>, val: Val<E>) {
        let home = self.val_home[val].expect("only a value with assigned slots can be killed");

        let size = val.reg_bank(input).size(input.machine);
        for i in 0..home.len_scalars(self) {
            let slot = home.nth_scalar(self, i);
            let removed = self.in_use.remove(slot);
            debug_assert!(removed, "{val:?} held {slot:?}, so it was occupied");
            debug_assert_eq!(self.slots[slot], size);

            self.free_slots_index[slot] =
                u32::try_from(self.free_slots[size.index()].len()).unwrap();
            self.free_slots[size.index()].push(slot);
            self.live_count[size.index()] -= 1;
        }
    }

    fn check_every_spilled_value_has_a_slot(&self, spilled: &EntitySet<Val<E>>) {
        if !cfg!(debug_assertions) {
            return;
        }
        for val in spilled.iter() {
            debug_assert!(
                self.val_home[val].is_some(),
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
        for size in self.slots.values() {
            per_size[size.index()] += 1;
        }
        for (log2_size, count) in per_size.iter().copied().enumerate() {
            debug_assert_eq!(
                count,
                self.max_live[log2_size],
                "created {count} slots of {} bytes but at most {} values of that size are ever \
                 simultaneously live; the coloring should be optimal",
                1u32 << log2_size,
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
    /// The stack slots this value lives in, one per register it occupies, or
    /// empty if it was never spilled.
    #[cfg(test)]
    pub(crate) fn spill_slots(
        self,
        spill_slots: &SpillSlots<E>,
    ) -> impl Iterator<Item = SpillSlot<E>> + Clone + '_ {
        self.stack_home(spill_slots)
            .into_iter()
            .flat_map(|home| home.slots(spill_slots))
    }

    /// Where this value lives on the stack, or `None` if it was never spilled.
    pub(crate) fn stack_home(self, spill_slots: &SpillSlots<E>) -> Option<StackAllocation<E>> {
        spill_slots.val_home[self]
    }
}

impl<E> SpillSlotGroup<E>
where
    E: EntityRepr,
{
    /// The `SpillSlot`s in this group, in member order.
    pub(crate) fn members(self, spill_slots: &SpillSlots<E>) -> &[SpillSlot<E>] {
        &spill_slots.group_members.as_slice()[spill_slots.groups[self].indices()]
    }
}

/// Spill slot queries about a span.
impl<E> LiveSpan<E>
where
    E: EntityRepr,
{
    /// Where this span's value lives over this span, or `None` when it is
    /// rematerialized whenever needed again.
    ///
    /// Note that, even when it is rematerialized on demand, the value may still
    /// have a stack home, for example, if used via a stack constraint.
    pub(crate) fn allocation(
        self,
        live_ranges: &LiveRanges<E>,
        spill_slots: &SpillSlots<E>,
    ) -> Option<Allocation<E>> {
        let bundle = self.bundle(live_ranges).unwrap();
        match bundle.reg_allocation(live_ranges) {
            Some(alloc) => Some(Allocation::Reg(alloc)),
            None if bundle.is_rematerialized(live_ranges) => None,
            None => Some(Allocation::Stack(
                self.val(live_ranges).stack_home(spill_slots).unwrap(),
            )),
        }
    }
}

impl<E> SpillSlot<E>
where
    E: EntityRepr,
{
    /// The size of the values this slot holds.
    pub(crate) fn size(self, spill_slots: &SpillSlots<E>) -> SpillSlotSize {
        spill_slots.slots[self]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        RegClass,
        context::{Context, ContextInner},
        entity::Inst,
        input::OperandConstraint,
        test::{TestInput, TestMachine},
    };
    use mutatis::{
        check::{Check, CheckResult},
        mutators as m,
    };
    use std::{
        collections::{BTreeMap, BTreeSet},
        format,
        string::String,
        sync::atomic::{AtomicUsize, Ordering},
        vec::Vec,
    };

    #[cfg(feature = "visualizer")]
    use crate::events::Event as LoggedEvent;

    /// A pass that bailed with `EntityReprTooSmall` never reached the cleanup
    /// at the end of its walk, and `Context::reset` resets that abandoned
    /// context too, so `reset` has to clear the scratch rather than assume it.
    #[test]
    fn reset_clears_scratch_from_an_abandoned_walk() {
        let mut spill_slots = SpillSlots::<u8>::new();

        spill_slots.live_count[0] = 1;
        spill_slots.in_use.insert(SpillSlot::try_new(0).unwrap());
        spill_slots.free_slots[0].push(SpillSlot::try_new(1).unwrap());
        spill_slots.live.insert(Val::try_new(0).unwrap());
        spill_slots
            .votes
            .push((SpillSlot::try_new(0).unwrap(), 1.0));
        spill_slots.classes.open(
            Val::try_new(0).unwrap(),
            LivePoint::new(Inst::try_new(0).unwrap(), Position::Early),
        );
        assert!(!spill_slots.is_reset());

        spill_slots.reset();
        assert!(spill_slots.is_reset());
    }

    /// Run every phase up through spill slot allocation.
    ///
    /// Returns `None` when register allocation itself gave up on this input,
    /// e.g. because the function needs more registers at once than the machine
    /// has; there are no spill slots to check in that case.
    fn allocate(test_input: &TestInput) -> Result<Option<Context>, String> {
        let mut context = Context::new();
        assert!(context.is_reset());

        let result = test_input.with_input(|input| -> IResult<()> {
            let context = &mut context.context32;
            analyze(context, input).map_err(|_| ())?;
            crate::coalescing::coalesce(context, input)?;
            crate::region_allocation::region_allocate(context, input)?;
            allocate_spill_slots(context, input)
        });

        if result.is_err() {
            return match context.context32.output.take_error() {
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
    ) -> Result<(), String> {
        let func = input.func;
        let result = context
            .rpo
            .construct(func, &mut context.dfs, &mut context.output)
            .and_then(|()| {
                context.region_tree.construct(
                    func,
                    &mut context.counts,
                    &mut context.dfs,
                    &mut context.output,
                )
            })
            .and_then(|()| {
                context.liveness.construct(
                    func,
                    &mut context.counts,
                    &context.rpo,
                    &mut context.output,
                )
            })
            .and_then(|()| {
                context.live_ranges.construct(
                    input,
                    &mut context.counts,
                    &mut context.events,
                    &mut context.liveness,
                    &mut context.output,
                )
            });
        result.map_err(|()| format!("analysis failed: {:?}", context.output.take_error()))
    }

    /// Where each spilled value's slot has to be reserved, as one range per
    /// block the value is live in.
    fn live_ranges_of(
        input: &Input<'_, impl InputFunction>,
        context: &ContextInner<u32>,
        spilled: &EntitySet<Val<u32>>,
    ) -> BTreeMap<Val<u32>, Vec<(LivePoint<u32>, LivePoint<u32>)>> {
        let func = input.func;
        let live_ranges = &context.live_ranges;
        let liveness = &context.liveness;

        let mut per_block: BTreeMap<(Val<u32>, Block<u32>), (LivePoint<u32>, LivePoint<u32>)> =
            BTreeMap::new();
        for span in live_ranges.spans() {
            let val = span.val(live_ranges);
            if !spilled.contains(val) {
                continue;
            }
            let block = span.block(func, live_ranges);
            let (start, end) = (span.start(live_ranges), span.end(live_ranges));
            per_block
                .entry((val, block))
                .and_modify(|range| {
                    range.0 = range.0.min(start);
                    range.1 = range.1.max(end);
                })
                .or_insert((start, end));
        }

        let mut ranges: BTreeMap<Val<u32>, Vec<_>> = BTreeMap::new();
        for (block, _) in func.blocks() {
            let (block_start, block_end) = (block.start_point(input), block.end_point(input));
            for val in spilled.iter() {
                let live_in = block.is_live_in(liveness, val);
                let live_out = block.is_live_out(liveness, val);
                let (start, end) = match per_block.get(&(val, block)) {
                    Some(&(start, end)) => (
                        if live_in { block_start } else { start },
                        if live_out { block_end } else { end },
                    ),
                    // No span here at all: the value is only in its slot, and
                    // only while it is live, which is the whole block or
                    // nothing. A value live-in and not live-out is used
                    // somewhere here, and a use has a span.
                    None if live_in && live_out => (block_start, block_end),
                    None => continue,
                };
                ranges.entry(val).or_default().push((start, end));
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
    ///
    /// Returns how many spilled values joined another's slot class, so that
    /// the caller can check the classes' paths through the coloring were
    /// covered.
    fn check_coloring(test_input: &TestInput, stride: usize) -> Result<usize, String> {
        let mut context = Context::new();

        test_input.with_input(|input| -> Result<usize, String> {
            let context = &mut context.context32;
            analyze(context, input)?;

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
            let mut spilled_set = EntitySet::<Val<u32>>::new();
            for (i, val) in vals.iter().copied().enumerate() {
                if i % stride == 0 {
                    spilled_set.insert(val);
                }
            }
            let spilled: BTreeSet<Val<u32>> = vals
                .iter()
                .copied()
                .enumerate()
                .filter(|(i, _)| i % stride == 0)
                .map(|(_, val)| val)
                .collect();

            // Narrowed ranges come from spill placement, which needs a real
            // region allocation rather than a spilled set we pick, so only
            // whole live ranges are covered here; `checker_properties` covers
            // both.
            let ranges = Ranges::WholeLiveRange;
            context
                .spill_slots
                .form_classes(
                    input,
                    &context.rpo,
                    &context.liveness,
                    &context.region_tree,
                    &spilled_set,
                    ranges,
                    &mut context.output,
                )
                .and_then(|()| {
                    context.spill_slots.color(
                        input,
                        &mut context.counts,
                        &mut context.events,
                        &context.rpo,
                        &context.liveness,
                        &context.region_tree,
                        &spilled_set,
                        ranges,
                        &mut context.output,
                    )
                })
                .map_err(|()| format!("coloring failed: {:?}", context.output.take_error()))?;

            let spill_slots = &context.spill_slots;
            let classed = spilled
                .iter()
                .filter(|&&val| spill_slots.classes.class_of(val) != val)
                .count();

            // Property 1: a value has a slot exactly when we asked for it to be
            // spilled.
            let actual: BTreeSet<Val<u32>> = vals
                .iter()
                .copied()
                .filter(|val| val.stack_home(spill_slots).is_some())
                .collect();
            if actual != spilled {
                return Err(format!(
                    "the values with a spill slot are {actual:?} but the values we spilled are \
                     {spilled:?}"
                ));
            }

            let ranges = live_ranges_of(input, context, &spilled_set);
            let size_of = |val: Val<u32>| val.reg_bank(input).size(input.machine);

            // A value in a register group has one slot per member, so compare
            // whole stack homes: any slot the two share is a slot they can
            // clobber each other in.
            let slots_of = |val: Val<u32>| -> BTreeSet<SpillSlot<u32>> {
                val.spill_slots(spill_slots).collect()
            };

            for (&a, a_ranges) in &ranges {
                for (&b, b_ranges) in &ranges {
                    if a >= b {
                        continue;
                    }
                    let shared: BTreeSet<SpillSlot<u32>> =
                        slots_of(a).intersection(&slots_of(b)).copied().collect();
                    if shared.is_empty() {
                        continue;
                    }

                    // Property 2: values that share a slot are never live at
                    // the same time, so neither can clobber the other.
                    if ranges_overlap(a_ranges, b_ranges) {
                        return Err(format!(
                            "{a:?} and {b:?} both live in {shared:?} but their live ranges \
                             {a_ranges:?} and {b_ranges:?} overlap"
                        ));
                    }

                    // Property 3: values that share a slot are the same size.
                    // Note that they need *not* be in the same bank: pooling
                    // slots across banks of equal size is the whole point.
                    if size_of(a) != size_of(b) {
                        return Err(format!(
                            "{a:?} and {b:?} both live in {shared:?} but their registers are {} \
                             and {} bytes wide",
                            size_of(a).size(),
                            size_of(b).size(),
                        ));
                    }
                }
            }

            // Property 4: a value's stack home is one slot per register it
            // occupies — a lone slot for an ordinary value, a group of one slot
            // per member for a value in a register group — and each of them is
            // the size of one of its registers.
            for &val in ranges.keys() {
                let home = val.stack_home(spill_slots);
                let shape_matches = match home {
                    Some(StackAllocation::SpillSlot(_)) => val.num_regs(input) == 1,
                    Some(StackAllocation::SpillSlotGroup(_)) => val.num_regs(input) > 1,
                    None => false,
                };
                if !shape_matches {
                    return Err(format!(
                        "{val:?} occupies {} registers but its stack home is {home:?}",
                        val.num_regs(input),
                    ));
                }

                let slots: Vec<SpillSlot<u32>> = val.spill_slots(spill_slots).collect();
                let distinct: BTreeSet<SpillSlot<u32>> = slots.iter().copied().collect();
                if slots.len() != val.num_regs(input) || distinct.len() != slots.len() {
                    return Err(format!(
                        "{val:?} occupies {} registers but its stack home is {slots:?}",
                        val.num_regs(input),
                    ));
                }
                for slot in slots {
                    if slot.size(spill_slots) != size_of(val) {
                        return Err(format!(
                            "{val:?} has {}-byte registers but {slot:?} is {} bytes",
                            size_of(val).size(),
                            slot.size(spill_slots).size(),
                        ));
                    }
                }
            }

            // Property 5: the allocation is optimal. For each size, we created
            // exactly as many slots as the largest number of slots that the
            // spilled values of that size ever need at once. No allocation can
            // do better, because those values all need distinct slots at that
            // point.
            let mut created: BTreeMap<SpillSlotSize, usize> = BTreeMap::new();
            for (slot, _) in spill_slots.slots.iter() {
                *created.entry(slot.size(spill_slots)).or_default() += 1;
            }

            // A maximum clique of an interval graph is always found at some
            // interval's start point, so those are the only points we need to
            // look at.
            let mut needed: BTreeMap<SpillSlotSize, usize> = BTreeMap::new();
            let points: Vec<LivePoint<u32>> =
                ranges.values().flatten().map(|&(start, _)| start).collect();
            for point in points {
                let mut live_here: BTreeMap<SpillSlotSize, usize> = BTreeMap::new();
                for (&val, val_ranges) in &ranges {
                    if val_ranges
                        .iter()
                        .any(|&(start, end)| start <= point && point < end)
                    {
                        *live_here.entry(size_of(val)).or_default() += val.num_regs(input);
                    }
                }
                for (size, count) in live_here {
                    let entry = needed.entry(size).or_default();
                    *entry = (*entry).max(count);
                }
            }

            if created != needed {
                return Err(format!(
                    "created {created:?} slots per size, but the maximum number of slots that \
                     simultaneously live spilled values need per size is {needed:?}"
                ));
            }

            Ok(classed)
        })
    }

    /// Run the whole allocator, which is the only way to reach the emergency
    /// slot path: move generation is what borrows an emergency slot.
    #[cfg(feature = "visualizer")]
    fn run_everything(test_input: &TestInput) -> Result<Option<Context>, String> {
        let mut context = Context::new();
        assert!(context.is_reset());

        let result = test_input
            .with_input(|input| -> IResult<()> { crate::run_inner(&mut context.context32, input) });

        if result.is_err() {
            return match context.context32.output.take_error() {
                crate::error::InternalError::Error(crate::Error::TooManyLiveRegs) => Ok(None),
                error => Err(format!("allocation failed: {error:?}")),
            };
        }

        Ok(Some(context))
    }

    /// Every slot in the stack frame was announced exactly once, with the
    /// right size, and flagged as an emergency slot exactly when it is one.
    #[cfg(feature = "visualizer")]
    #[test]
    fn every_slot_is_announced_once() -> CheckResult<TestInput> {
        Check::new()
            .min_iters(1_000)
            .min_duration(std::time::Duration::from_secs(1))
            .run_with(
                m::default::<TestInput>(),
                crate::test::corpus(),
                |test_input: &TestInput| -> Result<(), String> {
                    let Some(context) = run_everything(test_input)? else {
                        return Ok(());
                    };
                    let inner = &context.context32;
                    let spill_slots = &inner.spill_slots;

                    let mut created: BTreeMap<SpillSlot<u32>, (SpillSlotSize, bool)> =
                        BTreeMap::new();
                    for (_, event) in inner.events.iter() {
                        let LoggedEvent::SpillSlotCreated {
                            slot,
                            size,
                            emergency,
                        } = *event
                        else {
                            continue;
                        };
                        if created.insert(slot, (size, emergency)).is_some() {
                            return Err(format!("{slot:?} was created twice"));
                        }
                    }

                    let emergency: BTreeSet<SpillSlot<u32>> =
                        spill_slots.emergency.iter().flatten().copied().collect();

                    for (index, &size) in spill_slots.sizes().iter().enumerate() {
                        let slot = SpillSlot::<u32>::try_new(index).unwrap();
                        let want = (size, emergency.contains(&slot));
                        match created.remove(&slot) {
                            Some(got) if got == want => {}
                            Some(got) => {
                                return Err(format!(
                                    "{slot:?} was announced as {got:?}, but it is {want:?}"
                                ));
                            }
                            None => return Err(format!("{slot:?} was never announced")),
                        }
                    }

                    if let Some((slot, _)) = created.pop_first() {
                        return Err(format!("{slot:?} was announced but does not exist"));
                    }

                    Ok(())
                },
            )
    }

    /// Every spilled value was announced, and given a home made of slots that
    /// were announced before it.
    #[cfg(feature = "visualizer")]
    #[test]
    fn every_value_gets_an_announced_home() -> CheckResult<TestInput> {
        Check::new()
            .min_iters(1_000)
            .min_duration(std::time::Duration::from_secs(1))
            .run_with(
                m::default::<TestInput>(),
                crate::test::corpus(),
                |test_input: &TestInput| -> Result<(), String> {
                    let Some(context) = allocate(test_input)? else {
                        return Ok(());
                    };
                    let inner = &context.context32;
                    let spill_slots = &inner.spill_slots;

                    let mut slots_so_far: BTreeSet<SpillSlot<u32>> = BTreeSet::new();
                    let mut spilled: BTreeSet<Val<u32>> = BTreeSet::new();
                    let mut homes: BTreeMap<Val<u32>, StackAllocation<u32>> = BTreeMap::new();

                    for (_, event) in inner.events.iter() {
                        match *event {
                            LoggedEvent::SpillSlotCreated { slot, .. } => {
                                slots_so_far.insert(slot);
                            }
                            LoggedEvent::SpillSlotGroupCreated {
                                group, ref members, ..
                            } => {
                                if members != group.members(spill_slots) {
                                    return Err(format!(
                                        "{group:?} was announced with {members:?}, but holds {:?}",
                                        group.members(spill_slots),
                                    ));
                                }
                                for &slot in members {
                                    if !slots_so_far.contains(&slot) {
                                        return Err(format!(
                                            "{group:?} names {slot:?}, which was not created yet"
                                        ));
                                    }
                                }
                            }
                            LoggedEvent::ValueSpilled { val, num_spans } => {
                                if num_spans == 0 {
                                    return Err(format!("{val:?} was spilled with no spans"));
                                }
                                if !spilled.insert(val) {
                                    return Err(format!("{val:?} was spilled twice"));
                                }
                            }
                            LoggedEvent::SpillSlotAssigned { val, slot } => {
                                if homes.insert(val, slot).is_some() {
                                    return Err(format!("{val:?} was given two homes"));
                                }
                            }
                            _ => {}
                        }
                    }

                    let want_spilled: BTreeSet<Val<u32>> =
                        inner.region_allocation.spilled().iter().collect();
                    if spilled != want_spilled {
                        return Err(format!(
                            "the log spilled {spilled:?}, but the pass spilled {want_spilled:?}"
                        ));
                    }

                    for val in want_spilled {
                        let home = val.stack_home(spill_slots);
                        if homes.get(&val).copied() != home {
                            return Err(format!(
                                "{val:?} was announced at {:?}, but lives at {home:?}",
                                homes.get(&val),
                            ));
                        }
                    }

                    Ok(())
                },
            )
    }

    #[test]
    fn spill_slot_properties() -> CheckResult<TestInput> {
        static CLASSED: AtomicUsize = AtomicUsize::new(0);
        CLASSED.store(0, Ordering::Relaxed);

        let result = Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run_with(
                m::default::<TestInput>(),
                crate::test::corpus(),
                |test_input: &TestInput| -> Result<(), String> {
                    // Spill everything, which maximizes the pressure on the
                    // coloring, and then every other value, which interleaves
                    // spilled and unspilled values.
                    for stride in [1, 2] {
                        let classed = check_coloring(test_input, stride)?;
                        CLASSED.fetch_add(classed, Ordering::Relaxed);
                    }
                    Ok(())
                },
            );

        if result.is_ok() {
            assert!(
                CLASSED.load(Ordering::Relaxed) > 0,
                "no input formed a slot class, so the class paths went unchecked",
            );
        }
        result
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
        let slot = match val.stack_home(spill_slots) {
            Some(StackAllocation::SpillSlot(slot)) => slot,
            home => panic!("expected a single slot, got {home:?}"),
        };
        assert_eq!(slot.index(), 0);
    }

    /// A block parameter and the arguments it is passed on every edge share one
    /// slot, so that no edge copies from one slot to another.
    #[test]
    fn a_param_and_all_its_args_share_a_slot() {
        let test_input = TestInput::with_two_stack_args_to_one_stack_param();
        crate::test::check_allocation(&test_input).expect("the allocation must be correct");

        let context = allocate(&test_input).unwrap().unwrap();
        let spill_slots = &context.context32.spill_slots;
        let slot = |v| {
            Val::<u32>::try_new(v)
                .unwrap()
                .stack_home(spill_slots)
                .expect("every value here is spilled")
        };
        let (arg1, temp, arg2, param) = (slot(0), slot(1), slot(2), slot(3));
        assert_ne!(arg1, temp, "the two values in `block1` are live at once");
        assert_eq!(param, arg1);
        assert_eq!(param, arg2);
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
        assert!(context.context32.region_allocation.spilled().is_empty());
        assert_eq!(
            Val::<u32>::try_new(0).unwrap().stack_home(spill_slots),
            None
        );
    }

    /// A value carried past a block that wants every register costs no slot
    /// when recomputing it is cheaper than reloading it: the piece crossing
    /// that block gets no location, so nothing here hears of a spill -- and no
    /// store and reload come with it.
    #[test]
    fn a_recomputed_value_carried_past_a_crowded_block_gets_no_slot() {
        let mut test_input = TestInput::with_a_value_carried_past_a_crowded_block(false);
        test_input.set_remat_costs(Some(crate::input::RematCost::CheaperThanReload));

        let context = allocate(&test_input).unwrap().unwrap();
        let spill_slots = &context.context32.spill_slots;

        assert_eq!(spill_slots.len_slots(), 0);
        assert!(context.context32.region_allocation.spilled().is_empty());
        let carried = Val::<u32>::try_new(0).unwrap();
        assert_eq!(carried.stack_home(spill_slots), None);
    }

    /// The same value, but the crowded block passes it to its successor: that
    /// piece is the source half of an edge move, so it gets a slot.
    #[test]
    fn the_same_value_passed_to_a_successor_gets_a_slot() {
        let mut test_input = TestInput::with_a_value_carried_past_a_crowded_block(true);
        test_input.set_remat_costs(Some(crate::input::RematCost::CheaperThanReload));

        let context = allocate(&test_input).unwrap().unwrap();
        let spill_slots = &context.context32.spill_slots;

        let carried = Val::<u32>::try_new(0).unwrap();
        assert!(carried.stack_home(spill_slots).is_some());
    }

    /// Two values whose *slot* lifetimes do not overlap share one slot, even
    /// though the values are live at the same time.
    ///
    /// The first is spilled, reloaded, then held in a register, so nothing can
    /// read its slot again and the second can have it. Reserving across whole
    /// liveness cannot see that and takes two slots.
    #[test]
    fn two_values_share_a_slot_when_only_their_live_ranges_overlap() {
        let slots_with = |narrow: bool| {
            let mut test_input = TestInput::with_two_staggered_spilled_values();
            test_input.options.narrow_spill_slot_live_ranges = narrow;

            // The whole pipeline, so that the checker sees a real allocation
            // rather than this pass's output on its own.
            crate::test::check_allocation(&test_input).expect("the allocation must be correct");

            let context = allocate(&test_input).unwrap().unwrap();
            context.context32.spill_slots.len_slots()
        };

        assert_eq!(slots_with(false), 2, "each value keeps its own slot");
        assert_eq!(slots_with(true), 1, "the two values share one slot");
    }
}
