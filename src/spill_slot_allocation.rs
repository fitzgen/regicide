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
    input::{DefUse, Input, InputBlock as _, InputFunction, Position},
    live_ranges::{LivePoint, LiveRanges, LiveSpan},
    liveness::{Liveness, for_each_operand_rev},
    machine::RegBank,
    output::{Allocation, OutputInner, StackAllocation},
    region_allocation::RegionAllocation,
    rpo::Rpo,
    timing::Timing,
};
use alloc::vec::Vec;

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
    let _timing = Timing::new("allocate spill slots");

    let ContextInner {
        counts,
        rpo,
        liveness,
        live_ranges,
        region_allocation,
        spill_slots,
        output,
        ..
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

    /// The emergency slot of each size, created on demand by
    /// [`Self::emergency_slot`] and indexed by that size's base-two log.
    emergency: [Option<SpillSlot<E>>; RegBank::NUM_SIZES],
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
            spilled: EntitySet::new(),
            max_live: [0; RegBank::NUM_SIZES],
            live_count: [0; RegBank::NUM_SIZES],
            in_use: EntitySet::new(),
            free_slots: [const { Vec::new() }; RegBank::NUM_SIZES],
            events: Vec::new(),
            live: EntitySet::new(),
            emergency: [None; RegBank::NUM_SIZES],
        }
    }

    pub fn reset(&mut self) {
        let Self {
            slots,
            groups,
            group_members,
            val_home,
            spilled,
            max_live,
            live_count,
            in_use,
            free_slots,
            events,
            live,
            emergency,
        } = self;
        slots.reset();
        groups.reset();
        group_members.reset();
        val_home.reset();
        spilled.reset();
        *max_live = [0; RegBank::NUM_SIZES];
        debug_assert!(live_count.iter().all(|&n| n == 0));
        debug_assert!(in_use.is_empty());
        debug_assert!(free_slots.iter().all(|free| free.is_empty()));
        debug_assert!(events.is_empty());
        debug_assert!(live.is_empty());
        *emergency = [None; RegBank::NUM_SIZES];
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            slots,
            groups,
            group_members,
            val_home,
            spilled,
            max_live,
            live_count,
            in_use,
            free_slots,
            events,
            live,
            emergency,
        } = self;
        slots.is_reset()
            && groups.is_reset()
            && group_members.is_reset()
            && val_home.is_reset()
            && spilled.is_reset()
            && max_live.iter().all(|&n| n == 0)
            && live_count.iter().all(|&n| n == 0)
            && in_use.is_empty()
            && free_slots.iter().all(|free| free.is_empty())
            && events.is_empty()
            && live.is_empty()
            && emergency.iter().all(|slot| slot.is_none())
    }

    /// How many stack slots did we create?
    #[allow(dead_code, reason = "consumed by the phases that are still to come")]
    pub fn len_slots(&self) -> usize {
        self.slots.len()
    }

    /// The size of every slot we created, indexed by slot.
    ///
    /// The element type does not mention `E`, which is what lets
    /// `Output::spill_slots` iterate the slots of any representation with one
    /// concrete iterator type.
    pub(crate) fn sizes(&self) -> &[SpillSlotSize] {
        self.slots.as_slice()
    }

    /// The values that region allocation left on the stack, and that therefore
    /// have a slot.
    pub(crate) fn spilled(&self) -> &EntitySet<Val<E>> {
        &self.spilled
    }

    /// Get a spill slot of the given size that no value is assigned to, for
    /// move generation to borrow when it must break a cycle of parallel moves
    /// and no register is free.
    ///
    /// A value stays there only across one batch, and batches are
    /// sequentialized independently, so one slot per size class is enough
    /// however many cycles we break.
    pub(crate) fn emergency_slot(
        &mut self,
        counts: &mut Counts,
        size: SpillSlotSize,
        output: &mut OutputInner<E>,
    ) -> IResult<SpillSlot<E>> {
        if let Some(slot) = self.emergency[size.index()] {
            return Ok(slot);
        }

        let slot = self.slots.push(output, size)?;
        self.emergency[size.index()] = Some(slot);
        counts.emergency_spill_slots.inc();
        counts.spill_slots.inc();
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
            if !self.spilled.contains(val) || self.val_home[val].is_none() {
                continue;
            }
            self.occupy_val_slots(input, val);
        }

        // All other slots are free in this block. Rebuild the free lists
        // accordingly.
        debug_assert!(self.free_slots.iter().all(|free| free.is_empty()));
        for (slot, &size) in self.slots.iter() {
            if !self.in_use.contains(slot) {
                self.free_slots[size.index()].push(slot);
            }
        }

        // Color the live-in values that did not already have slots assigned,
        // which therefore must be this block's live block parameters.
        for val in block.live_in(liveness) {
            if !self.spilled.contains(val) || self.val_home[val].is_some() {
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
            self.val_home[val].is_none(),
            "{val:?} has a single definition in SSA, so we color it exactly once",
        );

        let size = val.reg_bank(input).size(input.machine);
        let num_regs = val.num_regs(input);

        let home = if num_regs == 1 {
            StackAllocation::SpillSlot(self.alloc_slot(size, output)?)
        } else {
            let start = self.group_members.next_key(output)?;
            for _ in 0..num_regs {
                let slot = self.alloc_slot(size, output)?;
                self.group_members.push(output, slot)?;
            }
            let end = self.group_members.next_key(output)?;
            let group = self.groups.push(output, EntityRange { start, end })?;
            StackAllocation::SpillSlotGroup(group)
        };

        self.val_home[val] = Some(home);
        self.occupy_val_slots(input, val);

        counts.spill_slot_assignments.inc();
        trace!(
            "spill slots: assigned {val:?} to {home:?}: {num_regs} slot(s) of {} bytes",
            size.size(),
        );
        Ok(())
    }

    /// Take a free slot of the given size, creating a new one when every
    /// existing slot of that size is occupied.
    fn alloc_slot(
        &mut self,
        size: SpillSlotSize,
        output: &mut OutputInner<E>,
    ) -> IResult<SpillSlot<E>> {
        match self.free_slots[size.index()].pop() {
            Some(slot) => Ok(slot),
            None => self.slots.push(output, size),
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

            self.free_slots[size.index()].push(slot);
            self.live_count[size.index()] -= 1;
        }
    }

    fn check_every_spilled_value_has_a_slot(&self) {
        if !cfg!(debug_assertions) {
            return;
        }
        for val in self.spilled.iter() {
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
    /// Where this span's value lives over this span.
    pub(crate) fn allocation(
        self,
        live_ranges: &LiveRanges<E>,
        spill_slots: &SpillSlots<E>,
    ) -> Allocation<E> {
        let bundle = self.bundle(live_ranges).unwrap();
        match bundle.reg_allocation(live_ranges) {
            Some(alloc) => Allocation::Reg(alloc),
            None => Allocation::Stack(self.val(live_ranges).stack_home(spill_slots).unwrap()),
        }
    }
}

impl<E> SpillSlot<E>
where
    E: EntityRepr,
{
    /// The size of the values this slot holds.
    #[cfg(test)]
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
        let ContextInner {
            counts,
            events,
            rpo,
            region_tree,
            liveness,
            live_ranges,
            dfs,
            output,
            ..
        } = context;
        let func = input.func;
        let result = rpo
            .construct(func, dfs, output)
            .and_then(|()| region_tree.construct(func, counts, dfs, output))
            .and_then(|()| liveness.construct(func, counts, rpo, output))
            .and_then(|()| live_ranges.construct(input, counts, events, liveness, output));
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

        test_input.with_input(|input| -> Result<(), String> {
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

            {
                let ContextInner {
                    counts,
                    rpo,
                    liveness,
                    spill_slots,
                    output,
                    ..
                } = &mut *context;
                spill_slots
                    .color(input, counts, rpo, liveness, output)
                    .map_err(|()| format!("coloring failed: {:?}", output.take_error()))?;
            }

            let spill_slots = &context.spill_slots;

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

            let ranges = live_ranges_of(context);
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
        let slot = match val.stack_home(spill_slots) {
            Some(StackAllocation::SpillSlot(slot)) => slot,
            home => panic!("expected a single slot, got {home:?}"),
        };
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
            Val::<u32>::try_new(0).unwrap().stack_home(spill_slots),
            None
        );
    }
}
