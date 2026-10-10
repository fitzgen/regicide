//! Region-based allocation.
//!
//! We do a bottom-up walk of the region tree, allocating registers within each
//! region.

mod assignments;
mod splitting;

use crate::{
    Entity, Input, InputFunction, OperandConstraint, Position, RegSet, Val,
    context::ContextInner,
    counts::Counts,
    entity::{EntityRepr, EntitySet, Region, SecondaryMap},
    error::{Error, IResult},
    events::{EventsLog, SplitKind},
    input::{DefUse, InputInst, InputValue},
    live_ranges::{
        HintPos, LiveBundle, LivePoint, LiveRanges, LiveSpan, RegPreference, SpillWeight,
    },
    machine::{Machine, Reg, RegClassMembers, RegGroup, RegUnit},
    output::{OutputInner, RegAllocation},
    region_tree::RegionTree,
    timing::Timing,
};
use alloc::{collections::BinaryHeap, vec::Vec};
use assignments::{Assignments, Occupant, QuerySpan, SpanInterference, SplitCandidate};
use core::{fmt, marker::PhantomData, ops::Range};
use splitting::{Cut, HalfSpan, SplitUse, WithinSpanCut};

pub fn region_allocate<E>(
    context: &mut ContextInner<E>,
    input: &Input<'_, impl InputFunction>,
) -> IResult<()>
where
    E: EntityRepr,
{
    let _timing = Timing::new("region allocate");

    // Reverse the pre-order so we visit children before parents, and leave the
    // cold regions for last, so that they adapt to their neighbors rather than
    // the other way around.
    let region_tree = &context.region_tree;
    let regions = region_tree
        .pre_order_iter()
        .rev()
        .filter(|&r| !region_tree.is_cold(r))
        .chain(
            region_tree
                .pre_order_iter()
                .filter(|&r| region_tree.is_cold(r)),
        );
    for region in regions {
        // Bias this region's bundles towards the registers their counterparts
        // across a region border already got. Children come first in this
        // walk, so those registers are facts by now rather than guesses.
        hint_across_regions(
            &context.coalescing.cross_region_affinities,
            &context.region_tree,
            &mut context.region_allocation.relayed_regs,
            &mut context.live_ranges,
            &mut context.events,
            input,
            region,
        );

        context.region_allocation.allocate_region(
            input,
            &context.region_tree,
            &mut context.live_ranges,
            &mut context.counts,
            &mut context.events,
            &mut context.output,
            region,
        )?;
    }

    context.coalescing.cross_region_affinities.clear();

    context.region_allocation.collect_spilled_values(
        &mut context.counts,
        &mut context.events,
        &context.live_ranges,
    );

    context.counts.final_live_spans += context.live_ranges.len_spans();
    context.counts.final_bundles += context.live_ranges.len_bundles();

    Ok(())
}

/// Bias `region`'s bundles towards the registers their counterparts across a
/// region border already hold, since the two sides disagreeing costs a move.
///
/// Hinting here rather than in coalescing is what lets the hint name a
/// register: we walk children before parents, so the far side is assigned.
///
/// When the far side is not assigned yet, because it is in a parent, we relay
/// the registers that the parent's *other* neighbors already got. Two sibling
/// loops that carry the same value through their parent otherwise each pick a
/// register on their own, and the parent can match at most one of them, which
/// leaves a move on the way into or out of the other loop.
fn hint_across_regions<E>(
    cross_region_affinities: &[(LiveSpan<E>, LiveSpan<E>)],
    region_tree: &RegionTree<E>,
    relayed_regs: &mut Vec<(LiveBundle<E>, Reg<E>)>,
    live_ranges: &mut LiveRanges<E>,
    events: &mut EventsLog<E>,
    input: &Input<'_, impl InputFunction>,
    region: Region<E>,
) where
    E: EntityRepr,
{
    // The registers each unassigned bundle outside this region has affinity
    // with, sorted by bundle so that we can look them up below.
    debug_assert!(relayed_regs.is_empty());
    for &(a, b) in cross_region_affinities {
        let (Some(bundle_a), Some(bundle_b)) = (a.bundle(live_ranges), b.bundle(live_ranges))
        else {
            continue;
        };
        for (unassigned, assigned) in [(bundle_a, bundle_b), (bundle_b, bundle_a)] {
            // Our own bundles are hinted directly below.
            if unassigned.region(live_ranges) == region {
                continue;
            }
            if let (None, Some(RegAllocation::Reg(reg))) = (
                unassigned.reg_allocation(live_ranges),
                assigned.reg_allocation(live_ranges),
            ) {
                relayed_regs.push((unassigned, reg));
            }
        }
    }
    relayed_regs.sort_unstable();

    for &(a, b) in cross_region_affinities {
        let (Some(bundle_a), Some(bundle_b)) = (a.bundle(live_ranges), b.bundle(live_ranges))
        else {
            continue;
        };

        let (region_a, region_b) = (bundle_a.region(live_ranges), bundle_b.region(live_ranges));

        // An affinity with neither side in this region is not ours to hint.
        let (ours, theirs) = if region_a == region {
            (bundle_a, bundle_b)
        } else if region_b == region {
            (bundle_b, bundle_a)
        } else {
            continue;
        };

        // A cold path does not get a say in how anything else is allocated.
        if region_tree.is_cold(theirs.region(live_ranges)) && !region_tree.is_cold(region) {
            continue;
        }

        // `assign_to_preferred` asserts the hint is within this class.
        let class = match ours.constraint(live_ranges) {
            OperandConstraint::Any => ours.value_reg_class(live_ranges, input),
            OperandConstraint::Reg(rc) => rc,
            OperandConstraint::Stack => continue,
            OperandConstraint::Reuse(_) => unreachable!("constraints are already resolved"),
        };
        let RegClassMembers::Regs(members) = class.members(input.machine) else {
            continue;
        };

        // Unassigned means the far side is a parent, or a not-yet-allocated
        // sibling under irreducible control flow.
        let Some(RegAllocation::Reg(reg)) = theirs.reg_allocation(live_ranges) else {
            // Only on the bundle and not its span: the relayed registers are
            // what another region chose, not what this edge needs, so a piece
            // split away from here should not inherit them.
            let first = relayed_regs.partition_point(|&(b, _)| b < theirs);
            let mut hint = RegSet::new();
            for &(_, reg) in relayed_regs[first..]
                .iter()
                .take_while(|&&(b, _)| b == theirs)
            {
                if members.contains(&reg.with_repr32()) {
                    hint.insert(reg.with_repr32());
                }
            }
            ours.add_hint(live_ranges, events, &hint, Some(theirs));
            continue;
        };
        if !members.contains(&reg.with_repr32()) {
            continue;
        }

        let mut hint = RegSet::new();
        hint.insert(reg.with_repr32());

        // Record which end of our span the affinity meets, so a later split
        // gives the hint only to the half that end belongs to.
        let our_span = if region_a == region { a } else { b };
        let pos = match our_span.start(live_ranges) <= first_span_start(live_ranges, ours) {
            true => HintPos::Start,
            false => HintPos::End,
        };
        our_span.add_hint_at(live_ranges, pos, hint);
        ours.add_hint(live_ranges, events, &hint, Some(theirs));
    }

    relayed_regs.clear();
}

/// What making room for a split half costs in the `c`th of a split's
/// candidates, whose units `units_of` gives.
fn half_interference<'a, E, C, Units>(
    interference: &'a mut SpanInterference<E>,
    assignments: &'a Assignments<E>,
    scratch: &'a mut Vec<LiveBundle<E>>,
    live_ranges: &'a LiveRanges<E>,
    units_of: impl Fn(C) -> Units + 'a,
) -> impl FnMut((usize, C), HalfSpan<'_, E>) -> f32 + 'a
where
    E: EntityRepr,
    Units: Iterator<Item = Range<RegUnit>> + Clone,
{
    move |(c, candidate), half| {
        interference.weight(
            assignments,
            SplitCandidate::new_unchecked(c),
            units_of(candidate),
            half,
            scratch,
            |victim| victim.spill_weight(live_ranges),
        )
    }
}

pub struct RegionAllocation<E>
where
    E: EntityRepr,
{
    /// The register allocation assignments we've committed to, across all regions.
    assignments: Assignments<E>,

    /// The work-in-progress register allocation assignments for the current
    /// region.
    region_assignments: Assignments<E>,

    /// The main work queue of bundles that still need assignment.
    queue: BinaryHeap<PqEntry<E>>,

    /// Each bundle's current allocation priority.
    bundle_priority: SecondaryMap<LiveBundle<E>, Priority>,

    /// Each bundle's clobbered-register set, once `push_bundle` has computed
    /// it, and `None` once a split has changed the bundle's spans.
    ///
    /// Most pushes re-queue a bundle an eviction displaced, and an eviction
    /// changes neither the bundle's spans nor the function's reservations,
    /// which is all the set depends on.
    bundle_clobbered: SecondaryMap<LiveBundle<E>, Option<RegSet>>,

    /// The set of bundles that must be allocated to stack slots.
    ///
    /// We just remember the set for now, and actually allocate the stack slots
    /// in later passes.
    stack_bundles: Vec<LiveBundle<E>>,

    /// The values needing a stack slot, derived from `stack_bundles` once this
    /// pass is done so that downstream passes share one copy.
    spilled: EntitySet<Val<E>>,

    /// Scratch space holding the spans of the bundle being split.
    split_spans: Vec<Range<LivePoint<E>>>,

    /// Scratch space holding the uses of the bundle being split, likewise.
    split_uses: Vec<SplitUse<E>>,

    /// Scratch space holding the cuts that shred a bundle into minimal pieces.
    minimal_cuts: Vec<Cut<E>>,

    /// Scratch space for deduplicating the bundles in the way of a half, which
    /// `SpanInterference::weight` borrows for the duration of a call and hands
    /// back empty.
    interference_scratch: Vec<LiveBundle<E>>,

    /// The registers that something clobbers in the current region.
    region_clobbers: RegSet,

    /// The queued bundles that clobbers leave at most half their class to.
    ///
    /// Set when a bundle is queued, alongside its priority, so that eviction
    /// does not walk its blocks' reservations again.
    clobber_bound: EntitySet<LiveBundle<E>>,

    /// The registers that any bundle queued in the current region has
    /// preferred.
    region_preferences: RegSet,

    /// Scratch space holding the registers `assign_to_non_preferred` tries, in
    /// order.
    non_preferred_candidates: Vec<Reg>,

    /// Scratch space for `hint_across_regions`: the registers that bundles
    /// outside the region being hinted have affinity with, by bundle.
    relayed_regs: Vec<(LiveBundle<E>, Reg<E>)>,

    /// What is in the way of each span of the bundle being split.
    split_interference: SpanInterference<E>,
}

impl<E> RegionAllocation<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        Self {
            assignments: Assignments::new(),
            region_assignments: Assignments::new(),
            queue: BinaryHeap::new(),
            bundle_priority: SecondaryMap::new(Priority::ZERO),
            bundle_clobbered: SecondaryMap::new(None),
            stack_bundles: Vec::new(),
            spilled: EntitySet::new(),
            split_spans: Vec::new(),
            split_uses: Vec::new(),
            minimal_cuts: Vec::new(),
            interference_scratch: Vec::new(),
            region_clobbers: RegSet::new(),
            clobber_bound: EntitySet::new(),
            region_preferences: RegSet::new(),
            non_preferred_candidates: Vec::new(),
            relayed_regs: Vec::new(),
            split_interference: SpanInterference::new(),
        }
    }

    pub fn reset(&mut self) {
        let RegionAllocation {
            assignments,
            region_assignments,
            queue,
            bundle_priority,
            bundle_clobbered,
            stack_bundles,
            spilled,
            split_spans,
            split_uses,
            minimal_cuts,
            interference_scratch,
            region_clobbers,
            clobber_bound,
            region_preferences,
            non_preferred_candidates,
            relayed_regs,
            split_interference,
        } = self;
        assignments.reset();
        region_assignments.reset();
        queue.clear();
        bundle_priority.reset();
        bundle_clobbered.reset();
        stack_bundles.clear();
        spilled.reset();
        split_spans.clear();
        split_uses.clear();
        minimal_cuts.clear();
        interference_scratch.clear();
        region_clobbers.reset();
        clobber_bound.reset();
        region_preferences.reset();
        non_preferred_candidates.clear();
        relayed_regs.clear();
        split_interference.clear();
    }

    pub fn is_reset(&self) -> bool {
        let RegionAllocation {
            assignments,
            region_assignments,
            queue,
            bundle_priority,
            bundle_clobbered,
            stack_bundles,
            spilled,
            split_spans,
            split_uses,
            minimal_cuts,
            interference_scratch,
            region_clobbers,
            clobber_bound,
            region_preferences,
            non_preferred_candidates,
            relayed_regs,
            split_interference,
        } = self;
        assignments.is_reset()
            && region_assignments.is_reset()
            && queue.is_empty()
            && bundle_priority.is_reset()
            && bundle_clobbered.is_reset()
            && stack_bundles.is_empty()
            && spilled.is_reset()
            && split_spans.is_empty()
            && split_uses.is_empty()
            && minimal_cuts.is_empty()
            && interference_scratch.is_empty()
            && region_clobbers.is_reset()
            && clobber_bound.is_reset()
            && region_preferences.is_reset()
            && non_preferred_candidates.is_empty()
            && relayed_regs.is_empty()
            && split_interference.is_empty()
    }

    /// The bundles that must live in memory, and so need a spill slot.
    pub(crate) fn stack_bundles(&self) -> &[LiveBundle<E>] {
        &self.stack_bundles
    }

    /// The values that we left on the stack, and that therefore need a slot.
    pub(crate) fn spilled(&self) -> &EntitySet<Val<E>> {
        &self.spilled
    }

    /// Gather the values needing a stack slot: everything covered by a bundle
    /// we could not keep in a register.
    ///
    /// Built here, where the bundles are decided, because both spill placement
    /// and spill slot allocation want it.
    fn collect_spilled_values(
        &mut self,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        live_ranges: &LiveRanges<E>,
    ) {
        // How many stack spans each value has. Only counted when we are
        // logging, which is the only thing that reads it.
        let logging = cfg!(any(
            feature = "trace-log",
            debug_assertions,
            feature = "visualizer",
        ));
        let mut num_spans = SecondaryMap::<Val<E>, usize>::new(0);

        for bundle in self.stack_bundles.iter().copied() {
            for span in bundle.spans(live_ranges) {
                let val = span.val(live_ranges);
                if self.spilled.insert(val) {
                    counts.spilled_values.inc();
                }
                if logging {
                    num_spans[val] += 1;
                }
            }
        }

        if logging {
            for val in self.spilled.iter() {
                event!(
                    events,
                    ValueSpilled {
                        val,
                        num_spans: num_spans[val],
                    }
                );
            }
        }
        trace!(
            "region allocation: {} values need a stack slot",
            self.spilled.len()
        );
    }

    /// Did we leave `reg` unassigned over all of `span`?
    pub(crate) fn is_reg_free(
        &self,
        machine: &Machine,
        reg: Reg<E>,
        span: Range<LivePoint<E>>,
    ) -> bool {
        !self.assignments.conflicts(
            core::iter::once(reg.units(machine)),
            core::iter::once(QuerySpan::sees_all_reservations(span)),
        )
    }

    /// The value sitting in `reg` over `span`, when exactly one bundle has it
    /// there and nothing has reserved it.
    ///
    /// Errs towards `None`, since naming the wrong value would write it into a
    /// home that is not its own. Treat an answer as a preference, not a fact.
    pub(crate) fn sole_reg_occupant(
        &self,
        machine: &Machine,
        live_ranges: &LiveRanges<E>,
        reg: Reg<E>,
        span: Range<LivePoint<E>>,
    ) -> Option<Val<E>> {
        let bundle = self.assignments.sole_conflicting_bundle(
            core::iter::once(reg.units(machine)),
            core::iter::once(QuerySpan::sees_all_reservations(span.clone())),
        )?;

        let mut vals = bundle
            .spans(live_ranges)
            // Moves run ahead of the instruction they sit in front of, so
            // only a value already live coming into the point is certainly in
            // the register now.
            .filter(|s| s.start(live_ranges) < span.start && span.end <= s.end(live_ranges))
            .map(|s| s.val(live_ranges));

        let val = vals.next()?;
        vals.all(|other| other == val).then_some(val)
    }

    /// Call `f` once for everything occupying any of the units `reg` covers.
    pub(crate) fn for_each_reg_occupant(
        &self,
        machine: &Machine,
        live_ranges: &LiveRanges<E>,
        reg: Reg<E>,
        span: Range<LivePoint<E>>,
        mut f: impl FnMut(RegAllocation<E>),
    ) {
        self.assignments.for_each_occupant(
            core::iter::once(reg.units(machine)),
            core::iter::once(QuerySpan::sees_all_reservations(span)),
            |occupant| {
                f(match occupant {
                    // A bundle the matrix still holds an assignment for has
                    // an allocation.
                    Occupant::Bundle(bundle) => bundle.reg_allocation(live_ranges).unwrap(),
                    Occupant::Reserved(held) => held,
                })
            },
        );
    }

    fn allocate_region(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        region_tree: &RegionTree<E>,
        live_ranges: &mut LiveRanges<E>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        output: &mut OutputInner<E>,
        region: Region<E>,
    ) -> IResult<()> {
        debug_assert!(self.queue.is_empty());

        // Hold each fixed operand's register for it before anything else can
        // take it. Blocks partition across regions, so a reservation is
        // region-local and rides this region's assignments into the global map
        // below.
        for block in region.blocks(region_tree) {
            for reservation in block.reservations(live_ranges) {
                if let (None, RegAllocation::Reg(reg)) =
                    (reservation.val(live_ranges), reservation.reg(live_ranges))
                {
                    self.region_clobbers.insert(reg.with_repr32());
                }
                self.region_assignments.insert_reservation(
                    reservation.reg(live_ranges).units(input.machine),
                    reservation.start(live_ranges)..reservation.end(live_ranges),
                    reservation.reg(live_ranges),
                    // Porous to its own value, or to nothing when it is a
                    // clobber. See `ReservationData`.
                    reservation.val(live_ranges),
                );
            }
        }

        // Insert each bundle in this region into the queue.
        //
        // Okay to call `region.bundles(..)` because we haven't split any of
        // this region's bundles yet, because we haven't allocated registers
        // within this region yet.
        for bundle in region.bundles(live_ranges) {
            self.push_bundle(
                input,
                region_tree,
                live_ranges,
                events,
                bundle,
                Phase::default(),
            );
        }

        // Keep processing bundles until they've all been assigned!
        while let Some(entry) = self.queue.pop() {
            debug_assert_eq!(entry.priority(), self.get_bundle_priority(entry.bundle()));

            counts.queue_pops.inc();

            let phase = entry.phase();

            event!(
                events,
                BundleQueuePopped {
                    bundle: entry.bundle(),
                    region: entry.bundle().region(live_ranges),
                    priority: entry.priority(),
                    phase,
                }
            );

            if self.assign_to_preferred(input, live_ranges, events, output, entry)? {
                counts.preferred_assignments.inc();
                continue;
            }

            if self.assign_to_non_preferred(input, live_ranges, events, output, entry)? {
                counts.non_preferred_assignments.inc();
                continue;
            }

            if self.assign_via_eviction(input, region_tree, live_ranges, events, output, entry)? {
                counts.evictions.inc();
                continue;
            }

            if phase <= Phase::SplitBetweenSpans
                && self.split_between_spans(
                    input,
                    region_tree,
                    live_ranges,
                    counts,
                    events,
                    output,
                    entry,
                )?
            {
                counts.split_between_spans.inc();
                continue;
            }

            if phase <= Phase::SplitWithinSpan
                && self.split_within_span(
                    input,
                    region_tree,
                    live_ranges,
                    counts,
                    events,
                    output,
                    entry,
                )?
            {
                counts.split_within_span.inc();
                continue;
            }

            self.split_into_minimal_or_spill(
                input,
                region_tree,
                live_ranges,
                counts,
                events,
                output,
                entry,
            )?;
            counts.split_into_minimal_or_spill.inc();
        }

        // Finally, commit this region's assignments.
        self.assignments.merge(&self.region_assignments);
        self.region_assignments.reset();
        self.region_clobbers.reset();
        self.clobber_bound.reset();
        self.region_preferences.reset();

        Ok(())
    }

    fn push_bundle(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        region_tree: &RegionTree<E>,
        live_ranges: &LiveRanges<E>,
        events: &mut EventsLog<E>,
        bundle: LiveBundle<E>,
        phase: Phase,
    ) {
        let clobbered = match self.bundle_clobbered[bundle] {
            Some(clobbered) => clobbered,
            None => {
                let clobbered = regs_clobbered_across(input, live_ranges, bundle);
                self.bundle_clobbered[bundle] = Some(clobbered);
                clobbered
            }
        };
        if is_clobber_bound(input, live_ranges, bundle, &clobbered) {
            self.clobber_bound.insert(bundle);
        } else {
            self.clobber_bound.remove(bundle);
        }
        let priority = compute_bundle_priority(input, region_tree, live_ranges, bundle, &clobbered);
        self.set_bundle_priority(bundle, priority);
        self.region_preferences
            .union_with(bundle.preference(live_ranges).union());
        self.queue.push(PqEntry::new(phase, priority, bundle));
        event!(
            events,
            BundleQueued {
                bundle,
                region: bundle.region(live_ranges),
                priority,
                phase,
            }
        );
    }

    /// Forget `bundle`'s cached clobber set, after a split took spans from it.
    fn forget_clobbered(&mut self, bundle: LiveBundle<E>) {
        self.bundle_clobbered[bundle] = None;
    }

    fn set_bundle_priority(&mut self, bundle: LiveBundle<E>, priority: Priority) {
        self.bundle_priority[bundle] = priority;
    }

    fn get_bundle_priority(&self, bundle: LiveBundle<E>) -> Priority {
        self.bundle_priority[bundle]
    }

    fn assign_to_preferred(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        live_ranges: &mut LiveRanges<E>,
        events: &mut EventsLog<E>,
        output: &mut OutputInner<E>,
        entry: PqEntry<E>,
    ) -> IResult<bool> {
        let bundle = entry.bundle();

        let pref = bundle.preference(live_ranges);
        if pref.is_empty() {
            return Ok(false);
        }

        // If this bundle has a register preference, then that preference had
        // better match its constraints.
        if cfg!(debug_assertions) {
            match bundle.constraint(live_ranges) {
                OperandConstraint::Any => {
                    let class = bundle.value_reg_class(live_ranges, input);
                    debug_assert!(pref.union().is_subset_of(class.member_set(input.machine)));
                    debug_assert!(matches!(
                        class.members(input.machine),
                        RegClassMembers::Regs(_)
                    ));
                }
                OperandConstraint::Reg(rc) => {
                    debug_assert!(pref.union().is_subset_of(rc.member_set(input.machine)));
                    debug_assert!(matches!(
                        rc.members(input.machine),
                        RegClassMembers::Regs(_)
                    ));
                }
                OperandConstraint::Stack => {
                    panic!("should not have reg preference with stack constraint")
                }
                OperandConstraint::Reuse(_) => unreachable!("already resolved reuse constraints"),
            }
        }

        let assigned = self.region_assignments.try_assign_to_reg(
            bundle,
            pref.intersection().iter().chain(
                pref.union()
                    .iter()
                    .filter(|r| !pref.intersection_contains(*r)),
            ),
            |r| r.units(input.machine),
            bundle.spans(live_ranges).map(|s| s.query(live_ranges)),
        );

        match assigned {
            None => Ok(false),
            Some(reg) => {
                let reg = output.with_repr::<E, _>(reg)?;
                let alloc = RegAllocation::Reg(reg);
                bundle.set_reg_allocation(live_ranges, alloc);
                event!(events, BundleAssignedPreferred { bundle, alloc });
                Ok(true)
            }
        }
    }

    fn assign_to_non_preferred(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        live_ranges: &mut LiveRanges<E>,
        events: &mut EventsLog<E>,
        output: &mut OutputInner<E>,
        entry: PqEntry<E>,
    ) -> IResult<bool> {
        let bundle = entry.bundle();
        let pref = bundle.preference(live_ranges);

        let rc = match bundle.constraint(live_ranges) {
            OperandConstraint::Any => {
                // No use constrained this bundle any further than the default
                // register class of its values, so use that default class.
                bundle.value_reg_class(live_ranges, input)
            }
            OperandConstraint::Reg(rc) => rc,
            OperandConstraint::Stack => {
                self.stack_bundles.push(bundle);
                event!(
                    events,
                    BundleSpilledToStack {
                        bundle,
                        region: bundle.region(live_ranges),
                        forced: true,
                    }
                );
                return Ok(true);
            }
            OperandConstraint::Reuse(_) => unreachable!("already resolved reuse constraints"),
        };

        let assigned = match rc.members(input.machine) {
            RegClassMembers::Regs(regs) => {
                let candidates = &mut self.non_preferred_candidates;
                order_non_preferred_candidates(
                    regs,
                    pref,
                    &self.region_clobbers,
                    &self.region_preferences,
                    candidates,
                );
                let assigned = self.region_assignments.try_assign_to_reg(
                    bundle,
                    candidates.iter().copied(),
                    |r| r.units(input.machine),
                    bundle.spans(live_ranges).map(|s| s.query(live_ranges)),
                );
                candidates.clear();
                assigned
                    .map(|reg| output.with_repr::<E, _>(reg).map(RegAllocation::Reg))
                    .transpose()?
            }
            RegClassMembers::Groups(groups) => {
                debug_assert!(pref.is_empty());
                self.region_assignments
                    .try_assign_to_reg_group(
                        bundle,
                        groups.iter().copied(),
                        |g| {
                            g.members(input.machine)
                                .iter()
                                .map(|r| r.units(input.machine))
                        },
                        bundle.spans(live_ranges).map(|s| s.query(live_ranges)),
                    )
                    .map(RegAllocation::RegGroup)
            }
        };

        match assigned {
            None => Ok(false),
            Some(alloc) => {
                bundle.set_reg_allocation(live_ranges, alloc);
                event!(
                    events,
                    BundleAssignedNonPreferred {
                        bundle,
                        alloc,
                        preference: *bundle.preference(live_ranges).union(),
                    }
                );
                Ok(true)
            }
        }
    }

    /// Try to assign `entry`'s bundle to a register by evicting a cheaper
    /// bundle from a register, freeing that register up for this bundle.
    ///
    /// We only ever get here once plain assignment has failed for every
    /// candidate. We take the cheapest-to-evict candidate, and only when that
    /// victim is strictly cheaper than this bundle. Otherwise, two bundles
    /// could evict each other forever.
    ///
    /// "Cheaper" is the whole `EvictionCost` order, not just spill weight: a
    /// bundle that still has somewhere else to go is cheaper to displace than
    /// one that does not, however much the first is worth. That is what lets a
    /// minimal bundle that must have a register take one from a bundle the
    /// stack could hold instead.
    ///
    /// Eviction does not mean that the victim is split or spilled. Instead, it
    /// is pushed back onto the queue to compete with the other unassigned
    /// bundles. The re-enqueued victim will never evict this bundle because, as
    /// explained above, it is cheaper than this bundle, guaranteeing forward
    /// progress.
    ///
    /// Returns whether this bundle was assigned (and, therefore, whether
    /// another bundle was evicted).
    fn assign_via_eviction(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        region_tree: &RegionTree<E>,
        live_ranges: &mut LiveRanges<E>,
        events: &mut EventsLog<E>,
        output: &mut OutputInner<E>,
        entry: PqEntry<E>,
    ) -> IResult<bool> {
        let machine = input.machine;
        let bundle = entry.bundle();
        let pref = bundle.preference(live_ranges);

        let rc = match bundle.constraint(live_ranges) {
            OperandConstraint::Any => bundle.value_reg_class(live_ranges, input),
            OperandConstraint::Reg(rc) => rc,
            OperandConstraint::Stack => {
                unreachable!("stack-constrained bundles are handled without a register")
            }
            OperandConstraint::Reuse(_) => unreachable!("already resolved reuse constraints"),
        };

        // The most we are willing to pay for eviction. This bundle holds no
        // register, so evicting it doesn't break any hints, and so it may only
        // break a victim's hint where that hint yields (below).
        let max_cost = EvictionCost::new(
            bundle.stickiness(input, live_ranges),
            bundle.is_minimal(live_ranges),
            0,
            SpillWeight::new(bundle.spill_weight(live_ranges)),
        );

        // A clobber-bound bundle fits only in the few registers that survive
        // its clobbers, and failing reloads at up to every one of its uses. A
        // far lighter victim's hint saves at most a move per span, so it does
        // not protect a victim with fewer spans than this bundle has uses.
        // A victim with no uses keeps its hint: the hint is all that places
        // it, and taking its register only moves its load or store.
        let (hints_yield_below, num_uses) = if self.clobber_bound.contains(bundle) {
            (
                bundle.spill_weight(live_ranges) / HINT_YIELDS_TO_HEAVIER_FACTOR,
                bundle
                    .spans(live_ranges)
                    .map(|s| s.uses(live_ranges).len())
                    .sum(),
            )
        } else {
            (0.0, 0)
        };

        // What evicting `victim` costs, where `hinted` says whether it is
        // hinted towards the register (or group) it would give up.
        let eviction_cost = |victim: LiveBundle<E>, hinted: bool| {
            let weight = victim.spill_weight(live_ranges);
            let yields = || {
                weight < hints_yield_below
                    && victim.spans(live_ranges).len() < num_uses
                    && victim
                        .spans(live_ranges)
                        .any(|s| !s.uses(live_ranges).is_empty())
            };
            EvictionCost::new(
                victim.stickiness(input, live_ranges),
                victim.is_minimal(live_ranges),
                usize::from(hinted && !yields()),
                SpillWeight::new(weight),
            )
        };

        let bundle_spans = |b: LiveBundle<E>| b.spans(live_ranges).map(|s| s.query(live_ranges));
        // The victim's own units; see `Assignments::remove_assignment`.
        let bundle_units = |b: LiveBundle<E>| {
            b.reg_allocation(live_ranges)
                .expect("a bundle being evicted holds a register")
                .units(machine)
        };

        let evicted = match rc.members(machine) {
            RegClassMembers::Regs(regs) => self
                .region_assignments
                .try_evict_reg_and_assign(
                    bundle,
                    pref.union()
                        .iter()
                        .chain(regs.iter().copied().filter(|r| !pref.union_contains(*r))),
                    |r| r.units(machine),
                    max_cost,
                    |victim, reg| {
                        eviction_cost(victim, victim.preference(live_ranges).union_contains(reg))
                    },
                    bundle_spans,
                    bundle_units,
                )
                .map(|(reg, evicted)| {
                    output
                        .with_repr::<E, _>(reg)
                        .map(|reg| (RegAllocation::Reg(reg), evicted))
                })
                .transpose()?,
            RegClassMembers::Groups(groups) => {
                debug_assert!(pref.is_empty());
                self.region_assignments
                    .try_evict_reg_group_and_assign(
                        bundle,
                        groups.iter().copied(),
                        |g| g.members(machine).iter().map(|r| r.units(machine)),
                        max_cost,
                        |victim, group| {
                            let hinted = !victim
                                .preference(live_ranges)
                                .union()
                                .intersection(group.member_set(machine))
                                .is_empty();
                            eviction_cost(victim, hinted)
                        },
                        bundle_spans,
                        bundle_units,
                    )
                    .map(|(group, evicted)| (RegAllocation::RegGroup(group), evicted))
            }
        };

        match evicted {
            None => Ok(false),
            Some((alloc, evicted)) => {
                event!(
                    events,
                    BundleEvicted {
                        bundle: evicted,
                        by: bundle,
                        alloc,
                    }
                );
                evicted.clear_reg_allocation(live_ranges);
                bundle.set_reg_allocation(live_ranges, alloc);
                event!(
                    events,
                    BundleAssignedViaEviction {
                        bundle,
                        alloc,
                        evicted,
                    }
                );
                self.push_bundle(
                    input,
                    region_tree,
                    live_ranges,
                    events,
                    evicted,
                    Phase::AssignEvict,
                );
                Ok(true)
            }
        }
    }

    fn fill_split_scratch(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        live_ranges: &LiveRanges<E>,
        bundle: LiveBundle<E>,
    ) {
        debug_assert!(self.split_spans.is_empty());
        debug_assert!(self.split_uses.is_empty());

        self.split_spans.extend(
            bundle
                .spans(live_ranges)
                .map(|s| s.start(live_ranges)..s.end(live_ranges)),
        );

        let mut prev = None;
        for span in bundle.spans(live_ranges) {
            let start = span.start(live_ranges);

            // A cut may only go immediately before a use at a `Late` point only
            // when that use is the start of its span and no use in the span
            // before it is reuse-tied to it. If it was not the start of the
            // span or it is reuse-tied to another use, then splitting would
            // demand a move in the middle of the instruction, where we cannot
            // place it.
            let cut_at_start = prev.is_none_or(|prev| !span.is_tied_to(live_ranges, input, prev));

            self.split_uses
                .extend(span.uses(live_ranges).into_iter().map(|u| {
                    let point = u.point(live_ranges);
                    SplitUse {
                        point,
                        weight: u.weight(live_ranges).as_f32(),
                        cut_before_allowed: point.pos() == Position::Early
                            || (point == start && cut_at_start),
                    }
                }));

            prev = Some(span);
        }
    }

    /// Split `entry`'s bundle in two, between spans.
    ///
    /// Returns whether the bundle was successfully cut: returns `false` when
    /// the bundle was not cut and the entry is left unqueued (so it can
    /// fallthrough to the next phase); returns `true` when the bundle was cut
    /// and its halves requeued for processing.
    fn split_between_spans(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        region_tree: &RegionTree<E>,
        live_ranges: &mut LiveRanges<E>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        output: &mut OutputInner<E>,
        entry: PqEntry<E>,
    ) -> IResult<bool> {
        let bundle = entry.bundle();

        // Can't split between fewer than two spans.
        if bundle.spans(live_ranges).len() < 2 {
            counts.split_between_spans_failed.inc();
            event!(
                events,
                BundleSplitFailed {
                    bundle,
                    split: SplitKind::BetweenSpans,
                }
            );
            return Ok(false);
        }

        self.fill_split_scratch(input, live_ranges, bundle);

        // See `has_nothing_to_split_for`.
        if has_nothing_to_split_for(live_ranges, bundle, &self.split_uses) {
            self.split_spans.clear();
            counts.split_between_spans_failed.inc();
            event!(
                events,
                BundleSplitFailed {
                    bundle,
                    split: SplitKind::BetweenSpans,
                }
            );
            return Ok(false);
        }

        // Cutting in the middle, rather than pricing every admissible cut
        // against every candidate register, is most of this pass's cost.
        let best = splitting::cut_near_middle(&self.split_spans, &self.split_uses);

        self.split_spans.clear();
        self.split_uses.clear();
        self.split_interference.clear();

        let Some(index) = best else {
            counts.split_between_spans_failed.inc();
            event!(
                events,
                BundleSplitFailed {
                    bundle,
                    split: SplitKind::BetweenSpans,
                }
            );
            return Ok(false);
        };

        let suffix = bundle.split_at_span(live_ranges, input, events, output, index)?;
        self.forget_clobbered(bundle);

        event!(
            events,
            BundleSplitBetweenSpans {
                bundle,
                suffix,
                at: first_span_start(live_ranges, suffix),
                index,
            }
        );

        // Hints attached to neither end stay true of both halves, and the
        // suffix wants what its own spans ask for at the end it now covers.
        // `bundle` already carries that hint.
        let pref = *bundle.preference(live_ranges).union();
        if !pref.is_empty() {
            suffix.add_hint(live_ranges, events, &pref, None);
        }

        // Push again with the same phase: we can afford to keep splitting
        // between spans until we can't split between spans anymore.
        self.push_bundle(
            input,
            region_tree,
            live_ranges,
            events,
            bundle,
            entry.phase(),
        );
        self.push_bundle(
            input,
            region_tree,
            live_ranges,
            events,
            suffix,
            entry.phase(),
        );

        Ok(true)
    }

    /// Split `entry`'s bundle in two, between uses inside one of its spans.
    ///
    /// Returns `false` and leaves the entry unqueued when we couldn't split the
    /// bundle, so it can fallthrough to the next phase; returns `true` when the
    /// bundle was split and both halves were requeued.
    fn split_within_span(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        region_tree: &RegionTree<E>,
        live_ranges: &mut LiveRanges<E>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        output: &mut OutputInner<E>,
        entry: PqEntry<E>,
    ) -> IResult<bool> {
        let bundle = entry.bundle();

        // Reject bundles that don't have a span with multiple uses we can cut
        // between.
        let cuttable = bundle.spans(live_ranges).any(|span| {
            let mut uses = span.uses(live_ranges).into_iter();
            match (uses.next(), uses.next_back()) {
                (Some(first), Some(last)) => {
                    first.point(live_ranges).inst() != last.point(live_ranges).inst()
                }
                _ => false,
            }
        });
        if !cuttable {
            counts.split_within_span_failed.inc();
            event!(
                events,
                BundleSplitFailed {
                    bundle,
                    split: SplitKind::WithinSpan,
                }
            );
            return Ok(false);
        }

        self.fill_split_scratch(input, live_ranges, bundle);

        let pref = *bundle.preference(live_ranges).union();

        let rc = match bundle.constraint(live_ranges) {
            OperandConstraint::Any => bundle.value_reg_class(live_ranges, input),
            OperandConstraint::Reg(rc) => rc,
            OperandConstraint::Stack => unreachable!("already handled"),
            OperandConstraint::Reuse(_) => unreachable!("already resolved"),
        };

        self.split_interference
            .reset(bundle.spans(live_ranges).map(|s| s.query(live_ranges)));

        let (cut, winner) = match rc.members(input.machine) {
            RegClassMembers::Regs(regs) => {
                let best = splitting::best_split_within_span(
                    &self.split_spans,
                    &self.split_uses,
                    pref.iter()
                        .chain(regs.iter().copied().filter(|r| !pref.contains(*r)))
                        .enumerate(),
                    half_interference(
                        &mut self.split_interference,
                        &self.region_assignments,
                        &mut self.interference_scratch,
                        live_ranges,
                        |reg: Reg| core::iter::once(reg.units(input.machine)),
                    ),
                )
                .expect("already rejected unsplittable bundles");
                (best.cut, Some(best.candidate.1))
            }
            RegClassMembers::Groups(groups) => {
                debug_assert!(pref.is_empty());
                let best = splitting::best_split_within_span(
                    &self.split_spans,
                    &self.split_uses,
                    groups.iter().copied().enumerate(),
                    half_interference(
                        &mut self.split_interference,
                        &self.region_assignments,
                        &mut self.interference_scratch,
                        live_ranges,
                        |group: RegGroup| {
                            group
                                .members(input.machine)
                                .iter()
                                .map(|r| r.units(input.machine))
                        },
                    ),
                )
                .expect("already rejected unsplittable bundles");
                (best.cut, None)
            }
        };

        self.split_spans.clear();
        self.split_uses.clear();
        self.split_interference.clear();

        // Name the span before the split rewrites it in place.
        let span = bundle
            .spans(live_ranges)
            .nth(cut.index)
            .expect("a cut names one of the bundle's spans");

        let suffix =
            bundle.split_at_point(live_ranges, input, events, output, cut.index, cut.at)?;
        self.forget_clobbered(bundle);

        event!(
            events,
            BundleSplitWithinSpan {
                bundle,
                suffix,
                span,
                at: cut.at,
            }
        );

        if let Some(reg) = winner {
            let mut winning_reg = RegSet::new();
            winning_reg.insert(reg);

            suffix.add_hint(live_ranges, events, &winning_reg, None);
            // Hints attached to neither end stay true of both halves, and the
            // suffix additionally wants whatever its own spans ask for at the
            // end it now covers.
            suffix.add_hint(live_ranges, events, &pref, None);

            bundle.add_hint(live_ranges, events, &winning_reg, None);
            // Note: `bundle` already has a hint of `pref`.
        }

        // Requeue each half at the next phase. We don't want to slowly split
        // off a single use at a time from each bundle in a high-conflict area,
        // so we only split within a span once and if we have more conflicts
        // after that, then we will split into minimal bundles and/or spill.
        debug_assert!(entry.phase() <= Phase::SplitWithinSpan);
        let phase = Phase::SplitWithinSpan.next();
        self.push_bundle(input, region_tree, live_ranges, events, bundle, phase);
        self.push_bundle(input, region_tree, live_ranges, events, suffix, phase);

        Ok(true)
    }

    /// Is `LiveBundle::narrow_to_early_half` both possible and worth doing
    /// for `bundle`?
    fn can_narrow_to_early_half(
        &self,
        input: &Input<'_, impl InputFunction>,
        live_ranges: &LiveRanges<E>,
        bundle: LiveBundle<E>,
    ) -> bool {
        debug_assert!(matches!(
            bundle.constraint(live_ranges),
            OperandConstraint::Reg(_)
        ));

        // Several spans would each need narrowing, with the carrier
        // re-formed around them.
        let mut spans = bundle.spans(live_ranges);
        let span = spans
            .next()
            .expect("a bundle always holds at least one span");
        if spans.next().is_some() {
            return false;
        }

        // The narrowing only means anything against one instruction's halves.
        if span.len_insts(live_ranges) != 1 {
            return false;
        }

        let start = span.start(live_ranges);

        // A span already ending at `inst:Late` has nothing to shed, so its
        // error is a real one.
        if span.end(live_ranges) <= start.next_point() {
            return false;
        }

        let uses = span.uses(live_ranges);
        if uses.is_empty() {
            return false;
        }

        // A `Late` operand genuinely needs the late half, and a def must start
        // its value's range at its own point.
        uses.into_iter().all(|u| {
            let point = u.point(live_ranges);
            if point != start {
                return false;
            }
            let kind = input
                .func
                .inst(point.inst().with_repr32())
                .operand(u.operand(live_ranges))
                .kind();
            kind == DefUse::Use
        })
    }

    /// The final phase for allocating a bundle: if it isn't already minimal,
    /// then split it into minimal pieces and push those back on the queue;
    /// otherwise, spill the bundle.
    ///
    /// There is nothing to fallthrough to from here, so we must handle the
    /// bundle.
    fn split_into_minimal_or_spill(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        region_tree: &RegionTree<E>,
        live_ranges: &mut LiveRanges<E>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        output: &mut OutputInner<E>,
        entry: PqEntry<E>,
    ) -> IResult<()> {
        let bundle = entry.bundle();

        let mut cuts = core::mem::take(&mut self.minimal_cuts);
        debug_assert!(cuts.is_empty());

        self.fill_split_scratch(input, live_ranges, bundle);
        let spill_whole = has_nothing_to_split_for(live_ranges, bundle, &self.split_uses);
        if !spill_whole {
            cuts.extend(splitting::minimal_cuts(&self.split_spans, &self.split_uses));
        }
        self.split_spans.clear();
        self.split_uses.clear();

        debug_assert!(
            spill_whole || bundle.is_minimal(live_ranges) == cuts.is_empty(),
            "a bundle is minimal iff there is nothing left to cut",
        );

        let result = (|| {
            if cuts.is_empty() {
                match bundle.constraint(live_ranges) {
                    // Free to live on the stack, or nowhere at all when
                    // recomputing its values is cheaper than keeping them.
                    OperandConstraint::Any => {
                        if bundle.is_cheaper_to_recompute_than_to_spill(input, live_ranges) {
                            bundle.set_rematerialized(live_ranges);
                            counts.rematerialized_bundles.inc();
                            event!(
                                events,
                                BundleRematerialized {
                                    bundle,
                                    region: bundle.region(live_ranges),
                                }
                            );
                            return Ok(());
                        }

                        // Fall through to the spill code below...
                    }

                    // It wants a register and there was none for it. One thing
                    // is left to try: split off a early-half-instruction span
                    // fo its early reads that need to be in a register, and
                    // then let the old span spill to the stack. See
                    // `LiveBundle::narrow_to_early_half`.
                    OperandConstraint::Reg(_) => {
                        if !self.can_narrow_to_early_half(input, live_ranges, bundle) {
                            return output.error(Error::TooManyLiveRegs);
                        }

                        let pref = *bundle.preference(live_ranges).union();
                        let reload =
                            bundle.narrow_to_early_half(live_ranges, input, events, output)?;
                        reload.add_hint(live_ranges, events, &pref, None);
                        self.push_bundle(
                            input,
                            region_tree,
                            live_ranges,
                            events,
                            reload,
                            Phase::SplitIntoMinimalOrSpill,
                        );
                        counts.early_half_reloads.inc();

                        // And fall through to spill the carrier bundle below...
                    }

                    OperandConstraint::Reuse(_) => unreachable!("already resolved"),
                    OperandConstraint::Stack => unreachable!("already handled"),
                }

                self.stack_bundles.push(bundle);

                counts.spilled_bundles.inc();
                event!(
                    events,
                    BundleSpilledToStack {
                        bundle,
                        region: bundle.region(live_ranges),
                        forced: false,
                    }
                );

                return Ok(());
            }

            let pref = *bundle.preference(live_ranges).union();

            event!(
                events,
                BundleSplitIntoMinimal {
                    bundle,
                    num_pieces: cuts.len() + 1,
                }
            );

            for cut in cuts.drain(..).rev() {
                let piece = match cut {
                    Cut::BetweenSpans(k) => {
                        bundle.split_at_span(live_ranges, input, events, output, k)?
                    }
                    Cut::WithinSpan(WithinSpanCut { index, at }) => {
                        bundle.split_at_point(live_ranges, input, events, output, index, at)?
                    }
                };
                self.forget_clobbered(bundle);
                piece.add_hint(live_ranges, events, &pref, None);
                self.push_bundle(
                    input,
                    region_tree,
                    live_ranges,
                    events,
                    piece,
                    Phase::SplitIntoMinimalOrSpill,
                );
            }

            self.push_bundle(
                input,
                region_tree,
                live_ranges,
                events,
                bundle,
                Phase::SplitIntoMinimalOrSpill,
            );
            Ok(())
        })();

        debug_assert!(self.minimal_cuts.is_empty());
        self.minimal_cuts = cuts;

        result
    }
}

impl<E> Default for RegionAllocation<E>
where
    E: EntityRepr,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<E> LiveSpan<E>
where
    E: EntityRepr,
{
    /// This span as a query on the matrix, porous to the reservations held for
    /// the value it carries.
    fn query(self, live_ranges: &LiveRanges<E>) -> QuerySpan<E> {
        QuerySpan::porous_to(
            self.val(live_ranges),
            self.start(live_ranges)..self.end(live_ranges),
        )
    }
}

impl<E> LiveBundle<E>
where
    E: EntityRepr,
{
    /// Would we rather recompute this bundle's values wherever they are next
    /// wanted than give it the stack slot it has fallen back to?
    fn is_cheaper_to_recompute_than_to_spill(
        self,
        input: &Input<'_, impl InputFunction>,
        live_ranges: &LiveRanges<E>,
    ) -> bool {
        self.spans(live_ranges).all(|span| {
            let val = span.val(live_ranges);
            span.uses(live_ranges).is_empty()
                && input.func.value(val.with_repr32()).remat_cost().is_some()
                && !val.is_passed_to_a_successor(input.func, span.block(input.func, live_ranges))
        })
    }

    /// How "sticky" is this bundle in a register?
    ///
    /// Zero for bundles that can be assigned to the stack if need be, highest
    /// for bundles that require a single, fixed register.
    fn stickiness(
        self,
        input: &Input<'_, impl InputFunction>,
        live_ranges: &LiveRanges<E>,
    ) -> usize {
        let rc = match self.constraint(live_ranges) {
            OperandConstraint::Reg(rc) => rc,

            // These can (or must) be allocated to the stack, so they are not
            // sticky in registers.
            OperandConstraint::Any | OperandConstraint::Stack => return 0,

            OperandConstraint::Reuse(_) => unreachable!("already resolved reuse constraints"),
        };

        let places = match rc.members(input.machine) {
            RegClassMembers::Regs(regs) => regs.len(),
            RegClassMembers::Groups(groups) => groups.len(),
        };

        // Counting down from the width of the class, and never all the way to
        // zero, so that a narrower class is stickier than a wider one and even
        // the widest one is stickier than a bundle the stack could hold.
        EVICTION_COST_STICKINESS_MAX - places.clamp(1, EVICTION_COST_STICKINESS_MAX - 1)
    }
}

/// How many times heavier than a hinted victim a clobber-bound bundle must be
/// before the victim's hint may stop protecting it from eviction.
const HINT_YIELDS_TO_HEAVIER_FACTOR: f32 = 8.0;

/// Fill `candidates` with the registers of `regs` that `pref` does not name, in
/// the order a bundle with no usable hint should try them.
///
/// Registers clobbered in the region come first: a bundle that fits in one
/// crosses no clobber, and leaves the registers that survive one to bundles
/// that do. Within each of those, registers no bundle in the region prefers
/// come before ones some bundle does, so that a bundle still in the queue
/// finds the register it was hinted towards free.
fn order_non_preferred_candidates(
    regs: &[Reg],
    pref: &RegPreference,
    region_clobbers: &RegSet,
    region_preferences: &RegSet,
    candidates: &mut Vec<Reg>,
) {
    // The tier a stable sort by `(!clobbered, preferred)` would put `r` in.
    let tier = |r: Reg| {
        2 * usize::from(!region_clobbers.contains(r)) + usize::from(region_preferences.contains(r))
    };

    // A counting sort: count each tier, then place each register after the
    // ones before it in the class's own order.
    let mut starts = [0; 5];
    for &r in regs {
        if !pref.union_contains(r) {
            starts[tier(r) + 1] += 1;
        }
    }
    for i in 1..starts.len() {
        starts[i] += starts[i - 1];
    }

    candidates.clear();
    let Some(&first) = regs.first() else {
        return;
    };
    candidates.resize(starts[4], first);
    for &r in regs {
        if !pref.union_contains(r) {
            let slot = &mut starts[tier(r)];
            candidates[*slot] = r;
            *slot += 1;
        }
    }
}

/// Is `bundle` one that splitting cannot help, so that once it fails to get a
/// register whole it should go to the stack whole?
///
/// That is a bundle no instruction reads or writes, free to live on the
/// stack. Any piece of it that won a register would only move the load or
/// store to the seam between pieces, and inside a loop that seam runs once per
/// iteration where a whole spill pays only at the loop's boundary.
///
/// `uses` are the bundle's uses, as `fill_split_scratch` collects them.
fn has_nothing_to_split_for<E>(
    live_ranges: &LiveRanges<E>,
    bundle: LiveBundle<E>,
    uses: &[SplitUse<E>],
) -> bool
where
    E: EntityRepr,
{
    uses.is_empty() && bundle.constraint(live_ranges) == OperandConstraint::Any
}

/// The registers that something clobbers while `bundle` is live.
///
/// None of these can hold the bundle whole, so a hint towards one of them is
/// one the bundle cannot honor.
fn regs_clobbered_across<E>(
    input: &Input<'_, impl InputFunction>,
    live_ranges: &LiveRanges<E>,
    bundle: LiveBundle<E>,
) -> RegSet
where
    E: EntityRepr,
{
    let mut clobbered = RegSet::new();
    for span in bundle.spans(live_ranges) {
        let (start, end) = (span.start(live_ranges), span.end(live_ranges));
        for r in span
            .block(input.func, live_ranges)
            .reservations_near(live_ranges, start..end)
        {
            if let (None, RegAllocation::Reg(reg)) = (r.val(live_ranges), r.reg(live_ranges))
                && LivePoint::spans_overlap(start, end, r.start(live_ranges), r.end(live_ranges))
            {
                clobbered.insert(reg.with_repr32());
            }
        }
    }
    clobbered
}

/// Where `bundle`'s first span begins.
fn first_span_start<E>(live_ranges: &LiveRanges<E>, bundle: LiveBundle<E>) -> LivePoint<E>
where
    E: EntityRepr,
{
    bundle
        .spans(live_ranges)
        .next()
        .expect("a bundle always holds at least one span")
        .start(live_ranges)
}

/// `clobbered` is `regs_clobbered_across` for `bundle`.
fn compute_bundle_priority<E>(
    input: &Input<'_, impl InputFunction>,
    region_tree: &RegionTree<E>,
    live_ranges: &LiveRanges<E>,
    bundle: LiveBundle<E>,
    clobbered: &RegSet,
) -> Priority
where
    E: EntityRepr,
{
    Priority::new(
        bundle.is_minimal(live_ranges),
        bundle_group_size(input, live_ranges, bundle),
        // A hint the bundle can never honor earns it no head start over the
        // bundles whose hints it would otherwise take.
        hint_rank(bundle.hinted_span_weight(input, region_tree, live_ranges, clobbered)),
        bundle.spans(live_ranges).len(),
    )
}

/// Bucket `weight` into the priority field's tiers, one per factor of ten,
/// reserving zero for an unhinted bundle.
///
/// The point is to saturate: past a bundle's first few hints the count is
/// noise, and a bundle hinted ten times does not want a register ten times as
/// much as one hinted once. See `LiveBundle::hinted_span_weight` for why a
/// tier is ten hinted spans.
fn hint_rank(weight: f64) -> usize {
    // A ladder rather than `log10`, which is `std`-only. `!(weight > 0.0)`
    // also catches a NaN, which would otherwise fall through to the loop.
    if !(weight > 0.0) {
        return 0;
    }
    let mut tier = 0;
    let mut bound = 10.0;
    while weight >= bound && tier < PRIORITY_NUM_HINTS_MAX - 1 {
        tier += 1;
        bound *= 10.0;
    }
    // A cold block weighs 0.05, so anything under 1 still beats no hint.
    1 + tier
}

/// Do the clobbers across `bundle` (`clobbered`) leave it at most half of
/// the registers in its class?
fn is_clobber_bound<E>(
    input: &Input<'_, impl InputFunction>,
    live_ranges: &LiveRanges<E>,
    bundle: LiveBundle<E>,
    clobbered: &RegSet,
) -> bool
where
    E: EntityRepr,
{
    if clobbered.is_empty() {
        return false;
    }
    let rc = match bundle.constraint(live_ranges) {
        OperandConstraint::Any => bundle.value_reg_class(live_ranges, input),
        OperandConstraint::Reg(rc) => rc,
        OperandConstraint::Stack => return false,
        OperandConstraint::Reuse(_) => unreachable!("already resolved reuse constraints"),
    };
    let members = rc.member_set(input.machine);
    2 * members.difference(clobbered).len() <= members.len()
}

fn bundle_group_size<E>(
    input: &Input<'_, impl InputFunction>,
    live_ranges: &LiveRanges<E>,
    bundle: LiveBundle<E>,
) -> usize
where
    E: EntityRepr,
{
    let machine = input.machine;

    // An `Any` bundle is assignable within the class its values live in, which
    // may itself be a class of register groups, so it has to answer the same
    // question that a `Reg` bundle does.
    let rc = match bundle.constraint(live_ranges) {
        OperandConstraint::Any => bundle.value_reg_class(live_ranges, input),
        OperandConstraint::Reg(rc) => rc,
        OperandConstraint::Stack => return 0,
        OperandConstraint::Reuse(_) => unreachable!(),
    };

    rc.group_size(machine).unwrap_or(0)
}

/// What phase of allocation is the associated bundle in?
///
/// A phase records how far down the *splitting* ladder a bundle has already
/// been pushed, so that we don't redo a split we have already done. Assignment
/// and eviction are not splits, and are attempted at every phase.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Phase {
    /// The initial phase.
    ///
    /// Nothing has been tried for this bundle yet, so every split below is
    /// still open to it.
    #[default]
    AssignEvict = 0,

    /// The first split attempt.
    ///
    /// Split a bundle in two at a span boundary, and then try allocating each
    /// half again. This optimistically keeps bundles fairly large.
    ///
    /// A bundle with no spans to cut between falls through to the next phase
    /// immediately.
    SplitBetweenSpans = 1,

    /// The second split attempt.
    ///
    /// Split a bundle at the point between two uses in the same span, and then
    /// try allocating each half again.
    ///
    /// A bundle that doesn't have two uses in the same span falls through to
    /// the next phase immediately.
    SplitWithinSpan = 2,

    /// The final phase.
    ///
    /// If this is not a minimal bundle yet, we can still split on conflict, and
    /// in this case we'll split into minimal bundles.
    ///
    /// If this is a minimal bundle, then we have to resort to spilling either
    /// this bundle or one of the others it conflicts with to the stack.
    SplitIntoMinimalOrSpill = 3,
}

#[cfg(feature = "serialize")]
impl serde::Serialize for Phase {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(match self {
            Self::AssignEvict => "assignEvict",
            Self::SplitBetweenSpans => "splitBetweenSpans",
            Self::SplitWithinSpan => "splitWithinSpan",
            Self::SplitIntoMinimalOrSpill => "splitIntoMinimalOrSpill",
        })
    }
}

impl Phase {
    /// Get the next phase after this one.
    fn next(self) -> Self {
        Self::from_raw((self as u8) + 1).unwrap()
    }

    /// Construct a `Phase` from its raw bits.
    fn from_raw(raw: u8) -> Option<Self> {
        match raw {
            0 => Some(Self::AssignEvict),
            1 => Some(Self::SplitBetweenSpans),
            2 => Some(Self::SplitWithinSpan),
            3 => Some(Self::SplitIntoMinimalOrSpill),
            _ => None,
        }
    }
}

/// A bundle's allocation priority.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Priority {
    ///    Bit:   31   ...  30   29             28  ...   26   25  ...  0
    ///         +--------------+--------------+--------------+------------+
    /// Fields: | (reserved):2 | is_minimal:1 | group_size:3 |   size:26  |
    ///         +--------------+--------------+--------------+------------+
    ///
    /// Packed so that we sort/prioritize bundles by:
    ///
    /// 1. Minimal bundles (as these can't be split any further, so allocating
    ///    to a register, rather than a spill slot, is now-or-never).
    ///
    /// 2. The size of its register group constraint (because assigning a
    ///    register groups assigns N registers at once, not just 1, so they are
    ///    harder to place and have more constraints than regular bundles).
    ///
    /// 3. Finally, by the bundle's size (number of spans) because if we assign
    ///    a larger bundle, then we get fewer moves and better codegen (and if
    ///    assigning it fails, we can always split it and try again).
    ///
    /// NB: the upper bits are reserved for encoding a `Phase` when this is
    /// packed inside a `PqEntry`.
    bits: u32,
}

const PRIORITY_SIZE_BITS: u32 = 23;
const PRIORITY_SIZE_SHIFT: u32 = 0;
const PRIORITY_SIZE_MASK: u32 = ((1 << PRIORITY_SIZE_BITS) - 1) << PRIORITY_SIZE_SHIFT;

const PRIORITY_NUM_HINTS_BITS: u32 = 3;
const PRIORITY_NUM_HINTS_SHIFT: u32 = PRIORITY_SIZE_SHIFT + PRIORITY_SIZE_BITS;
const PRIORITY_NUM_HINTS_MASK: u32 =
    ((1 << PRIORITY_NUM_HINTS_BITS) - 1) << PRIORITY_NUM_HINTS_SHIFT;
const PRIORITY_NUM_HINTS_MAX: usize = (1 << PRIORITY_NUM_HINTS_BITS) - 1;

const PRIORITY_GROUP_SIZE_BITS: u32 = 3;
const PRIORITY_GROUP_SIZE_SHIFT: u32 = PRIORITY_NUM_HINTS_SHIFT + PRIORITY_NUM_HINTS_BITS;
const PRIORITY_GROUP_SIZE_MASK: u32 =
    ((1 << PRIORITY_GROUP_SIZE_BITS) - 1) << PRIORITY_GROUP_SIZE_SHIFT;
const PRIORITY_GROUP_SIZE_MAX: usize = (1 << PRIORITY_GROUP_SIZE_BITS) - 1;

const PRIORITY_IS_MINIMAL_BITS: u32 = 1;
const PRIORITY_IS_MINIMAL_SHIFT: u32 = PRIORITY_GROUP_SIZE_SHIFT + PRIORITY_GROUP_SIZE_BITS;
const PRIORITY_IS_MINIMAL_MASK: u32 =
    ((1 << PRIORITY_IS_MINIMAL_BITS) - 1) << PRIORITY_IS_MINIMAL_SHIFT;

/// A priority queue entry.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct PqEntry<E> {
    ///    Bit:   63   62   61  ...  32   31  ...  0
    ///         +---------+-------------+------------+
    /// Fields: | phase:2 | priority:30 |  bundle:32 |
    ///         +---------+-------------+------------+
    ///
    /// Packed so that sort/prioritize by phase, then bundle priority, and
    /// finally break ties with the bundle index.
    bits: u64,

    _phantom: PhantomData<E>,
}

const PQ_ENTRY_BUNDLE_BITS: u64 = 32;
const PQ_ENTRY_BUNDLE_SHIFT: u64 = 0;
const PQ_ENTRY_BUNDLE_MASK: u64 = ((1 << PQ_ENTRY_BUNDLE_BITS) - 1) << PQ_ENTRY_BUNDLE_SHIFT;

const PQ_ENTRY_PRIORITY_BITS: u64 = 30;
const PQ_ENTRY_PRIORITY_SHIFT: u64 = PQ_ENTRY_BUNDLE_SHIFT + PQ_ENTRY_BUNDLE_BITS;
const PQ_ENTRY_PRIORITY_MASK: u64 = ((1 << PQ_ENTRY_PRIORITY_BITS) - 1) << PQ_ENTRY_PRIORITY_SHIFT;

const PQ_ENTRY_PHASE_BITS: u64 = 2;
const PQ_ENTRY_PHASE_SHIFT: u64 = PQ_ENTRY_PRIORITY_SHIFT + PQ_ENTRY_PRIORITY_BITS;
const PQ_ENTRY_PHASE_MASK: u64 = ((1 << PQ_ENTRY_PHASE_BITS) - 1) << PQ_ENTRY_PHASE_SHIFT;

impl fmt::Debug for Priority {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Priority")
            .field("is_minimal", &self.is_minimal())
            .field("group_size", &self.group_size())
            .field("num_hints", &self.num_hints())
            .field("size", &self.size())
            .finish()
    }
}

impl<E> fmt::Debug for PqEntry<E>
where
    E: EntityRepr,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PqEntry")
            .field("phase", &self.phase())
            .field("priority", &self.priority())
            .field("bundle", &self.bundle())
            .finish()
    }
}

#[cfg(feature = "serialize")]
impl serde::Serialize for Priority {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_u32(self.bits)
    }
}

impl Priority {
    /// The lowest possible priority.
    const ZERO: Priority = Priority { bits: 0 };

    fn new(is_minimal: bool, group_size: usize, num_hints: usize, size: usize) -> Self {
        let is_minimal = u32::from(is_minimal) << PRIORITY_IS_MINIMAL_SHIFT;
        debug_assert_eq!(is_minimal & PRIORITY_IS_MINIMAL_MASK, is_minimal);

        let group_size = u32::try_from(group_size.min(PRIORITY_GROUP_SIZE_MAX)).unwrap();
        let group_size = group_size << PRIORITY_GROUP_SIZE_SHIFT;
        debug_assert_eq!(group_size & PRIORITY_GROUP_SIZE_MASK, group_size);

        let num_hints = u32::try_from(num_hints.min(PRIORITY_NUM_HINTS_MAX)).unwrap();
        let num_hints = num_hints << PRIORITY_NUM_HINTS_SHIFT;
        debug_assert_eq!(num_hints & PRIORITY_NUM_HINTS_MASK, num_hints);

        let max_size = (1 << PRIORITY_SIZE_BITS) - 1;
        debug_assert!(size <= max_size);
        let size = u32::try_from(size).unwrap();
        let size = size << PRIORITY_SIZE_SHIFT;
        debug_assert_eq!(size & PRIORITY_SIZE_MASK, size);

        Priority {
            bits: is_minimal | group_size | num_hints | size,
        }
    }

    #[inline]
    fn is_minimal(&self) -> bool {
        self.bits & PRIORITY_IS_MINIMAL_MASK != 0
    }

    #[inline]
    fn num_hints(&self) -> usize {
        let num_hints = (self.bits & PRIORITY_NUM_HINTS_MASK) >> PRIORITY_NUM_HINTS_SHIFT;
        usize::try_from(num_hints).unwrap()
    }

    #[inline]
    fn group_size(&self) -> usize {
        let group_size = (self.bits & PRIORITY_GROUP_SIZE_MASK) >> PRIORITY_GROUP_SIZE_SHIFT;
        usize::try_from(group_size).unwrap()
    }

    #[inline]
    fn size(&self) -> usize {
        let size = (self.bits & PRIORITY_SIZE_MASK) >> PRIORITY_SIZE_SHIFT;
        usize::try_from(size).unwrap()
    }
}

impl<E> PqEntry<E>
where
    E: EntityRepr,
{
    fn new(phase: Phase, priority: Priority, bundle: LiveBundle<E>) -> Self {
        let phase = u64::from(phase as u8);
        let phase = phase << PQ_ENTRY_PHASE_SHIFT;
        debug_assert_eq!(phase & PQ_ENTRY_PHASE_MASK, phase);

        let priority = u64::from(priority.bits);
        let priority = priority << PQ_ENTRY_PRIORITY_SHIFT;
        debug_assert_eq!(priority & PQ_ENTRY_PRIORITY_MASK, priority);

        let bundle = u32::try_from(bundle.index()).unwrap();
        let bundle = u64::from(bundle);
        debug_assert_eq!(bundle & PQ_ENTRY_BUNDLE_MASK, bundle);

        Self {
            bits: phase | priority | bundle,
            _phantom: PhantomData,
        }
    }

    #[inline]
    fn phase(&self) -> Phase {
        let phase = (self.bits & PQ_ENTRY_PHASE_MASK) >> PQ_ENTRY_PHASE_SHIFT;
        let phase = u8::try_from(phase).unwrap();
        Phase::from_raw(phase).expect("every value of the two-bit field is a phase")
    }

    #[inline]
    fn priority(&self) -> Priority {
        let priority = (self.bits & PQ_ENTRY_PRIORITY_MASK) >> PQ_ENTRY_PRIORITY_SHIFT;
        Priority {
            bits: u32::try_from(priority).unwrap(),
        }
    }

    #[inline]
    fn bundle(&self) -> LiveBundle<E> {
        let bundle = (self.bits & PQ_ENTRY_BUNDLE_MASK) >> PQ_ENTRY_BUNDLE_SHIFT;
        let bundle = usize::try_from(bundle).unwrap();
        LiveBundle::try_new(bundle).unwrap()
    }
}

/// What it would cost us to evict one or more bundles from a register.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct EvictionCost {
    ///  Bit:    31   ...  29   28   ...  25   24             23    ...   16   15      ...       0
    ///        +--------------+--------------+--------------+----------------+---------------------+
    /// Field: | (reserved):3 | stickiness:4 | is_minimal:1 | broken_hints:8 | max_spill_weight:16 |
    ///        +--------------+--------------+--------------+----------------+---------------------+
    ///
    /// Packed so that we price a victim by, in order:
    ///
    /// 1. How few places it has left to go (see `LiveBundle::stickiness`). A
    ///    bundle the stack could hold is never stuck, so it is always the
    ///    cheapest thing to displace, however much it is worth; among bundles
    ///    that all need a register, the one with the widest class to choose
    ///    from is cheapest.
    ///
    /// 2. Whether it is minimal, because splitting is the only escape route
    ///    left to a bundle the stack cannot hold, and a minimal bundle does not
    ///    have it. This is what lets a minimal bundle take a register from a
    ///    splittable one in the same class.
    ///
    /// 3. How many hints evicting it would break, and finally
    ///
    /// 4. Its spill weight. Between two bundles that are equally stuck, take
    ///    the cheaper bundle.
    ///
    /// The budget `assign_via_eviction` compares against is the placing
    /// bundle's own cost under this same order, and it only ever takes a
    /// *strictly* cheaper victim, so the victim can never turn around and evict
    /// it back.
    bits: u32,
}

const EVICTION_COST_MAX_SPILL_WEIGHT_BITS: u32 = 16;
const EVICTION_COST_MAX_SPILL_WEIGHT_SHIFT: u32 = 0;
const EVICTION_COST_MAX_SPILL_WEIGHT_MASK: u32 =
    ((1 << EVICTION_COST_MAX_SPILL_WEIGHT_BITS) - 1) << EVICTION_COST_MAX_SPILL_WEIGHT_SHIFT;

const EVICTION_COST_BROKEN_HINTS_BITS: u32 = 8;
const EVICTION_COST_BROKEN_HINTS_SHIFT: u32 =
    EVICTION_COST_MAX_SPILL_WEIGHT_SHIFT + EVICTION_COST_MAX_SPILL_WEIGHT_BITS;
const EVICTION_COST_BROKEN_HINTS_MASK: u32 =
    ((1 << EVICTION_COST_BROKEN_HINTS_BITS) - 1) << EVICTION_COST_BROKEN_HINTS_SHIFT;
const EVICTION_COST_BROKEN_HINTS_MAX: usize = (1 << EVICTION_COST_BROKEN_HINTS_BITS) - 1;

const EVICTION_COST_IS_MINIMAL_BITS: u32 = 1;
const EVICTION_COST_IS_MINIMAL_SHIFT: u32 =
    EVICTION_COST_BROKEN_HINTS_SHIFT + EVICTION_COST_BROKEN_HINTS_BITS;
const EVICTION_COST_IS_MINIMAL_MASK: u32 =
    ((1 << EVICTION_COST_IS_MINIMAL_BITS) - 1) << EVICTION_COST_IS_MINIMAL_SHIFT;

const EVICTION_COST_STICKINESS_BITS: u32 = 4;
const EVICTION_COST_STICKINESS_SHIFT: u32 =
    EVICTION_COST_IS_MINIMAL_SHIFT + EVICTION_COST_IS_MINIMAL_BITS;
const EVICTION_COST_STICKINESS_MASK: u32 =
    ((1 << EVICTION_COST_STICKINESS_BITS) - 1) << EVICTION_COST_STICKINESS_SHIFT;
const EVICTION_COST_STICKINESS_MAX: usize = (1 << EVICTION_COST_STICKINESS_BITS) - 1;

impl fmt::Debug for EvictionCost {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EvictionCost")
            .field("stickiness", &self.stickiness())
            .field("is_minimal", &self.is_minimal())
            .field("broken_hints", &self.broken_hints())
            .field("max_spill_weight", &self.max_spill_weight())
            .finish()
    }
}

impl EvictionCost {
    fn new(
        stickiness: usize,
        is_minimal: bool,
        broken_hints: usize,
        max_spill_weight: SpillWeight,
    ) -> Self {
        let stickiness = u32::try_from(stickiness.min(EVICTION_COST_STICKINESS_MAX)).unwrap();
        let stickiness = stickiness << EVICTION_COST_STICKINESS_SHIFT;
        debug_assert_eq!(stickiness & EVICTION_COST_STICKINESS_MASK, stickiness);

        let is_minimal = u32::from(is_minimal) << EVICTION_COST_IS_MINIMAL_SHIFT;
        debug_assert_eq!(is_minimal & EVICTION_COST_IS_MINIMAL_MASK, is_minimal);

        let broken_hints = u32::try_from(broken_hints.min(EVICTION_COST_BROKEN_HINTS_MAX)).unwrap();
        let broken_hints = broken_hints << EVICTION_COST_BROKEN_HINTS_SHIFT;
        debug_assert_eq!(broken_hints & EVICTION_COST_BROKEN_HINTS_MASK, broken_hints);

        let max_spill_weight = u32::from(max_spill_weight.bits());
        let max_spill_weight = max_spill_weight << EVICTION_COST_MAX_SPILL_WEIGHT_SHIFT;
        debug_assert_eq!(
            max_spill_weight & EVICTION_COST_MAX_SPILL_WEIGHT_MASK,
            max_spill_weight
        );

        EvictionCost {
            bits: stickiness | is_minimal | broken_hints | max_spill_weight,
        }
    }

    #[inline]
    fn stickiness(self) -> usize {
        let stickiness =
            (self.bits & EVICTION_COST_STICKINESS_MASK) >> EVICTION_COST_STICKINESS_SHIFT;
        usize::try_from(stickiness).unwrap()
    }

    #[inline]
    fn is_minimal(self) -> bool {
        self.bits & EVICTION_COST_IS_MINIMAL_MASK != 0
    }

    #[inline]
    fn broken_hints(self) -> usize {
        let broken_hints =
            (self.bits & EVICTION_COST_BROKEN_HINTS_MASK) >> EVICTION_COST_BROKEN_HINTS_SHIFT;
        usize::try_from(broken_hints).unwrap()
    }

    #[inline]
    fn max_spill_weight(self) -> SpillWeight {
        let max_spill_weight = (self.bits & EVICTION_COST_MAX_SPILL_WEIGHT_MASK)
            >> EVICTION_COST_MAX_SPILL_WEIGHT_SHIFT;
        SpillWeight::from_bits(u16::try_from(max_spill_weight).unwrap())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::RegGroup;
    use std::{vec, vec::Vec};

    #[cfg(feature = "visualizer")]
    use crate::{context::Context, events::Event, input::InputValue, test::TestInput};
    #[cfg(feature = "visualizer")]
    use mutatis::{
        check::{Check, CheckResult},
        mutators as m,
    };
    #[cfg(feature = "visualizer")]
    use std::{
        collections::{BTreeMap, BTreeSet},
        format,
        string::String,
    };

    /// Run every phase up through region allocation.
    ///
    /// Returns `None` when allocation gave up on this input, e.g. because the
    /// function needs more registers at once than the machine has; there is no
    /// complete event log to check in that case.
    #[cfg(feature = "visualizer")]
    fn allocate(test_input: &TestInput) -> Result<Option<Context>, String> {
        let mut context = Context::new();
        assert!(context.is_reset());

        let result = test_input.with_input(|input| -> IResult<()> {
            let inner = &mut context.context32;
            let func = input.func;
            inner
                .rpo
                .construct(func, &mut inner.dfs, &mut inner.output)?;
            inner.region_tree.construct(
                func,
                &mut inner.counts,
                &mut inner.dfs,
                &mut inner.output,
            )?;
            inner
                .liveness
                .construct(func, &mut inner.counts, &inner.rpo, &mut inner.output)?;
            inner.live_ranges.construct(
                input,
                &mut inner.counts,
                &mut inner.events,
                &mut inner.liveness,
                &mut inner.output,
            )?;
            crate::coalescing::coalesce(inner, input)?;
            region_allocate(inner, input)
        });

        if result.is_err() {
            return match context.context32.output.take_error() {
                // Not every function fits on every machine, and that is not
                // the event log's problem.
                crate::error::InternalError::Error(Error::TooManyLiveRegs) => Ok(None),
                error => Err(format!("allocation failed: {error:?}")),
            };
        }

        Ok(Some(context))
    }

    /// Every cached clobber set that survives allocation must still be the
    /// one `regs_clobbered_across` would compute now.
    ///
    /// A missed `forget_clobbered` leaves a stale set behind, which only
    /// sometimes changes a visible decision but is always detectably stale.
    #[test]
    fn cached_clobbers_match_a_fresh_walk() -> CheckResult<TestInput> {
        Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run_with(
                m::default::<TestInput>(),
                crate::test::corpus(),
                |test_input: &TestInput| -> Result<(), String> {
                    let Some(context) = allocate(test_input)? else {
                        return Ok(());
                    };
                    let inner = &context.context32;
                    test_input
                        .with_input(|input| -> IResult<()> {
                            let live_ranges = &inner.live_ranges;
                            for bundle in live_ranges.bundles() {
                                let Some(cached) = inner.region_allocation.bundle_clobbered[bundle]
                                else {
                                    continue;
                                };
                                let fresh = regs_clobbered_across(input, live_ranges, bundle);
                                assert_eq!(cached, fresh, "{bundle:?}'s clobber set is stale");
                            }
                            Ok(())
                        })
                        .map_err(|e| format!("{e:?}"))?;

                    Ok(())
                },
            )
    }

    /// Every bundle and every span that exists at the end of allocation can be
    /// traced back to the event that created it.
    ///
    /// This is what keeps the visualizer's parent links trustworthy: a split
    /// that forgets to log its parentage orphans a piece here.
    #[cfg(feature = "visualizer")]
    #[test]
    fn everything_has_a_provenance() -> CheckResult<TestInput> {
        Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run_with(
                m::default::<TestInput>(),
                crate::test::corpus(),
                |test_input: &TestInput| -> Result<(), String> {
                    let Some(context) = allocate(test_input)? else {
                        return Ok(());
                    };
                    let inner = &context.context32;
                    let live_ranges = &inner.live_ranges;

                    let mut constructed_bundles = BTreeSet::new();
                    let mut bundle_parents: BTreeMap<LiveBundle<u32>, usize> = BTreeMap::new();
                    let mut constructed_spans = BTreeSet::new();
                    let mut span_parents: BTreeMap<crate::live_ranges::LiveSpan<u32>, usize> =
                        BTreeMap::new();

                    for (_, event) in inner.events.iter() {
                        match *event {
                            Event::BundleConstructed { bundle, .. } => {
                                constructed_bundles.insert(bundle);
                            }
                            Event::BundleSplit { child, .. } => {
                                *bundle_parents.entry(child).or_default() += 1;
                            }
                            // The reload is split out of the bundle it
                            // narrows.
                            Event::BundleNarrowedToEarlyHalf { reload, .. } => {
                                *bundle_parents.entry(reload).or_default() += 1;
                            }
                            Event::SpanConstructed { span, .. } => {
                                constructed_spans.insert(span);
                            }
                            Event::SpanSplit {
                                parent,
                                first,
                                second,
                                ..
                            } => {
                                if first != parent {
                                    return Err(format!(
                                        "a span split rewrites its first piece in \
                                         place, so {first:?} should be {parent:?}"
                                    ));
                                }
                                *span_parents.entry(second).or_default() += 1;
                            }
                            _ => {}
                        }
                    }

                    for bundle in live_ranges.bundles() {
                        let parents = bundle_parents.get(&bundle).copied().unwrap_or(0);
                        let constructed = constructed_bundles.contains(&bundle);
                        if usize::from(constructed) + parents != 1 {
                            return Err(format!(
                                "{bundle:?} was constructed {} time(s) and split out of a parent \
                                 {parents} time(s); it should be exactly one of the two",
                                usize::from(constructed),
                            ));
                        }
                    }

                    for span in live_ranges.spans() {
                        let parents = span_parents.get(&span).copied().unwrap_or(0);
                        let constructed = constructed_spans.contains(&span);
                        if usize::from(constructed) + parents != 1 {
                            return Err(format!(
                                "{span:?} was constructed {} time(s) and cut out of a parent \
                                 {parents} time(s); it should be exactly one of the two",
                                usize::from(constructed),
                            ));
                        }
                    }

                    Ok(())
                },
            )
    }

    /// An early read whose class is full over the late half allocates by
    /// narrowing: the carrier goes to the stack and the read gets its own
    /// early-half bundle.
    #[cfg(feature = "visualizer")]
    #[test]
    fn an_early_read_narrows_to_its_own_half_instruction_bundle() {
        let test_input = TestInput::with_an_early_read_under_a_full_late_half();
        let context = allocate(&test_input)
            .expect("the fixture allocates")
            .expect("the fixture does not run out of registers");
        let inner = &context.context32;
        let live_ranges = &inner.live_ranges;

        let mut narrowings = inner.events.iter().filter_map(|(_, event)| match *event {
            Event::BundleNarrowedToEarlyHalf { bundle, reload, at } => Some((bundle, reload, at)),
            _ => None,
        });
        let (carrier, reload, at) = narrowings
            .next()
            .expect("the read narrows to the early half");
        assert_eq!(narrowings.next(), None, "it narrows only the once");

        // Spilling the carrier is what frees the late half for the two
        // pinned definitions.
        assert!(
            inner.region_allocation.stack_bundles().contains(&carrier),
            "{carrier:?} should have been spilled, but the stack bundles are {:?}",
            inner.region_allocation.stack_bundles(),
        );

        let reload_spans = reload.spans(live_ranges).collect::<Vec<_>>();
        assert_eq!(reload_spans.len(), 1, "the reload holds a single span");
        let reload_span = reload_spans[0];
        assert_eq!(reload_span.start(live_ranges).pos(), Position::Early);
        assert_eq!(reload_span.end(live_ranges), at);
        assert_eq!(
            reload_span.end(live_ranges).pos(),
            Position::Late,
            "the reload ends at the late half, not at the next instruction",
        );

        // The carrier keeps its full extent, so the value stays covered
        // across the instruction it is only read in the early half of.
        let carrier_spans = carrier.spans(live_ranges).collect::<Vec<_>>();
        assert_eq!(carrier_spans.len(), 1, "the carrier holds a single span");
        assert!(
            carrier_spans[0].end(live_ranges) > reload_span.end(live_ranges),
            "the carrier should still reach past the reload",
        );
        assert!(
            carrier_spans[0].uses(live_ranges).is_empty(),
            "the carrier handed all of its uses to the reload",
        );

        // This is what puts the reload's register in `operand_allocs`
        // instead of the carrier's stack slot.
        let reload_uses = reload_span.uses(live_ranges);
        assert!(!reload_uses.is_empty(), "the reload carries the read");
        for u in reload_uses {
            assert_eq!(
                u.span(live_ranges),
                reload_span,
                "every use the reload holds should point back at it",
            );
            assert_eq!(u.point(live_ranges), reload_span.start(live_ranges));
        }
    }

    /// The queue events tell the whole story of the queue: nothing is popped
    /// that was not queued, and every pop ends in exactly one outcome.
    #[cfg(feature = "visualizer")]
    #[test]
    fn every_pop_is_queued_and_resolved() -> CheckResult<TestInput> {
        Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run_with(
                m::default::<TestInput>(),
                crate::test::corpus(),
                |test_input: &TestInput| -> Result<(), String> {
                    let Some(context) = allocate(test_input)? else {
                        return Ok(());
                    };

                    // The bundle each queue event names, and whether the event
                    // resolves a pop.
                    fn outcome(event: &Event<u32>) -> Option<LiveBundle<u32>> {
                        match *event {
                            Event::BundleAssignedPreferred { bundle, .. }
                            | Event::BundleAssignedNonPreferred { bundle, .. }
                            | Event::BundleAssignedViaEviction { bundle, .. }
                            | Event::BundleSpilledToStack { bundle, .. }
                            | Event::BundleRematerialized { bundle, .. }
                            | Event::BundleSplitBetweenSpans { bundle, .. }
                            | Event::BundleSplitWithinSpan { bundle, .. }
                            | Event::BundleSplitIntoMinimal { bundle, .. } => Some(bundle),
                            _ => None,
                        }
                    }

                    let mut queued: BTreeMap<LiveBundle<u32>, usize> = BTreeMap::new();
                    let mut popped: Option<LiveBundle<u32>> = None;
                    let mut resolutions = 0;

                    for (_, event) in context.context32.events.iter() {
                        match *event {
                            Event::BundleQueued { bundle, .. } => {
                                *queued.entry(bundle).or_default() += 1;
                            }
                            Event::BundleQueuePopped { bundle, .. } => {
                                if let Some(prev) = popped
                                    && resolutions != 1
                                {
                                    return Err(format!(
                                        "popping {prev:?} led to {resolutions} outcomes, want 1"
                                    ));
                                }
                                match queued.get_mut(&bundle) {
                                    Some(n) if *n > 0 => *n -= 1,
                                    _ => {
                                        return Err(format!(
                                            "popped {bundle:?} without queueing it"
                                        ));
                                    }
                                }
                                popped = Some(bundle);
                                resolutions = 0;
                            }
                            _ => {
                                if outcome(event) == popped {
                                    resolutions += 1;
                                }
                            }
                        }
                    }

                    if let Some(prev) = popped
                        && resolutions != 1
                    {
                        return Err(format!(
                            "popping {prev:?} led to {resolutions} outcomes, want 1"
                        ));
                    }

                    // And the queue drains: every region finishes with an empty
                    // one.
                    if let Some((bundle, _)) = queued.iter().find(|&(_, &n)| n > 0) {
                        return Err(format!("{bundle:?} was left on the queue"));
                    }

                    Ok(())
                },
            )
    }

    /// Register pressure alone never sends a value to the stack that we could
    /// recompute instead: a use-less bundle holding only recomputable values is
    /// left without a location rather than spilled.
    #[cfg(feature = "visualizer")]
    #[test]
    fn pressure_alone_never_spills_what_we_could_recompute() -> CheckResult<TestInput> {
        Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run_with(
                m::default::<TestInput>(),
                crate::test::corpus(),
                |test_input: &TestInput| -> Result<(), String> {
                    let Some(context) = allocate(test_input)? else {
                        return Ok(());
                    };
                    let inner = &context.context32;
                    let live_ranges = &inner.live_ranges;

                    for (_, event) in inner.events.iter() {
                        let Event::BundleSpilledToStack {
                            bundle,
                            forced: false,
                            ..
                        } = *event
                        else {
                            continue;
                        };
                        let could_have_been_recomputed = test_input.with_input(|input| {
                            bundle.is_cheaper_to_recompute_than_to_spill(input, live_ranges)
                        });
                        if could_have_been_recomputed {
                            return Err(format!(
                                "{bundle:?} has no uses and holds only values we could recompute, \
                             but pressure sent it to the stack anyway",
                            ));
                        }
                    }

                    Ok(())
                },
            )
    }

    /// A minimal bundle over an always-recomputable value still pays full
    /// price for the register its use needs, so under pressure it keeps one
    /// and something worth less goes to the stack instead.
    ///
    /// It never evicts for it: minimal bundles leave the queue first, so the
    /// long bundle is the one that arrives to find the register taken, splits,
    /// and leaves its useless middle on the stack.
    #[cfg(feature = "visualizer")]
    #[test]
    fn a_minimal_recomputable_bundle_keeps_a_register_rather_than_spilling() {
        let test_input = TestInput::with_a_recomputed_read_under_pressure();
        let context = allocate(&test_input)
            .expect("the input allocates")
            .expect("and fits on the machine");
        let inner = &context.context32;
        let live_ranges = &inner.live_ranges;

        let holds_a_recomputable_value = |bundle: LiveBundle<u32>| {
            test_input.with_input(|input| {
                bundle.spans(live_ranges).any(|span| {
                    input
                        .func
                        .value(span.val(live_ranges).with_repr32())
                        .remat_cost()
                        .is_some()
                })
            })
        };
        let uses = |bundle: LiveBundle<u32>| {
            bundle
                .spans(live_ranges)
                .map(|span| span.uses(live_ranges).into_iter().count())
                .sum::<usize>()
        };

        let mut in_a_register = Vec::new();
        let mut on_the_stack = Vec::new();
        for (_, event) in inner.events.iter() {
            match *event {
                Event::BundleAssignedPreferred { bundle, .. }
                | Event::BundleAssignedNonPreferred { bundle, .. }
                | Event::BundleAssignedViaEviction { bundle, .. } => in_a_register.push(bundle),
                Event::BundleSpilledToStack { bundle, .. } => on_the_stack.push(bundle),
                _ => {}
            }
        }

        // Nothing recomputable was spilled: a reload costs more than a remat.
        for &bundle in &on_the_stack {
            assert!(
                !holds_a_recomputable_value(bundle),
                "{bundle:?} holds a value cheaper to recompute than to spill, \
                 and went to the stack anyway",
            );
        }

        // Every recomputable piece with a use got a register, and one of
        // those pieces is minimal.
        let mut minimal_recomputable_uses = 0;
        for bundle in live_ranges.bundles() {
            if !holds_a_recomputable_value(bundle) || uses(bundle) == 0 {
                continue;
            }
            assert!(
                in_a_register.contains(&bundle),
                "{bundle:?} has a use that needs a register and did not get one",
            );
            if bundle.is_minimal(live_ranges) {
                minimal_recomputable_uses += 1;
            }
        }
        assert!(
            minimal_recomputable_uses > 0,
            "no minimal recomputable piece had a use to hold a register for",
        );

        // And the pressure was real: something cheaper went to the stack.
        assert!(
            !on_the_stack.is_empty(),
            "nothing was spilled, so nobody had to pay for a register",
        );
        for &spilled in &on_the_stack {
            for bundle in live_ranges.bundles() {
                if !holds_a_recomputable_value(bundle) || uses(bundle) == 0 {
                    continue;
                }
                assert!(
                    bundle.spill_weight(live_ranges) > spilled.spill_weight(live_ranges),
                    "{bundle:?} is worth {}, no more than the {} of {spilled:?}, \
                     which was spilled to make room for it",
                    bundle.spill_weight(live_ranges),
                    spilled.spill_weight(live_ranges),
                );
            }
        }
    }

    const MAX_SIZE: usize = (1 << PRIORITY_SIZE_BITS) - 1;
    const MAX_GROUP_SIZE: usize = PRIORITY_GROUP_SIZE_MAX;
    const MAX_NUM_HINTS: usize = PRIORITY_NUM_HINTS_MAX;
    const MAX_BROKEN_HINTS: usize = EVICTION_COST_BROKEN_HINTS_MAX;
    const MAX_STICKINESS: usize = EVICTION_COST_STICKINESS_MAX;

    /// Every phase, in ascending order.
    const PHASES: [Phase; 4] = [
        Phase::AssignEvict,
        Phase::SplitBetweenSpans,
        Phase::SplitWithinSpan,
        Phase::SplitIntoMinimalOrSpill,
    ];
    /// A use-less bundle over a recomputable value gets no location at all
    /// rather than a stack slot -- unless its block passes the value to a
    /// successor, making it the source half of an edge move. Both halves run on
    /// the same shape, so the guard is the only difference.
    #[cfg(feature = "visualizer")]
    #[test]
    fn a_use_less_recomputable_bundle_is_rematerialized_unless_it_is_passed_along() {
        use crate::input::RematCost;

        for passed_to_the_successor in [false, true] {
            let mut test_input =
                TestInput::with_a_value_carried_past_a_crowded_block(passed_to_the_successor);
            test_input.set_remat_costs(Some(RematCost::CheaperThanReload));

            let context = allocate(&test_input)
                .expect("the input allocates")
                .expect("and fits on the machine");
            let inner = &context.context32;
            let live_ranges = &inner.live_ranges;

            // A bundle the decision could apply to: no uses, all recomputable.
            let is_a_candidate = |bundle: LiveBundle<u32>| {
                test_input.with_input(|input| {
                    bundle.spans(live_ranges).all(|span| {
                        span.uses(live_ranges).is_empty()
                            && input
                                .func
                                .value(span.val(live_ranges).with_repr32())
                                .remat_cost()
                                .is_some()
                    })
                })
            };

            let mut rematerialized = Vec::new();
            let mut spilled = Vec::new();
            for (_, event) in inner.events.iter() {
                match *event {
                    Event::BundleRematerialized { bundle, .. } => rematerialized.push(bundle),
                    Event::BundleSpilledToStack {
                        bundle,
                        forced: false,
                        ..
                    } if is_a_candidate(bundle) => spilled.push(bundle),
                    _ => {}
                }
            }

            if passed_to_the_successor {
                assert!(
                    rematerialized.is_empty(),
                    "{rematerialized:?} was left without a location, but the block that holds \
                     it passes its value to a successor and so has a move to source",
                );
                assert!(
                    !spilled.is_empty(),
                    "nothing use-less and recomputable was spilled, so the guard was never \
                     reached",
                );
            } else {
                assert!(
                    spilled.is_empty(),
                    "{spilled:?} got a stack slot it has no use for",
                );
                assert_eq!(
                    rematerialized.len(),
                    1,
                    "the piece crossing the crowded block should be the one bundle left \
                     without a location, got {rematerialized:?}",
                );
                for bundle in rematerialized {
                    assert!(is_a_candidate(bundle));
                    assert!(bundle.is_rematerialized(live_ranges));
                    assert!(bundle.reg_allocation(live_ranges).is_none());
                }
            }
        }
    }

    fn bundle(index: usize) -> LiveBundle<u32> {
        LiveBundle::try_new(index).unwrap()
    }

    /// A priority's fields survive the round trip through its packed bits.
    #[test]
    fn priority_round_trips_its_fields() {
        for is_minimal in [false, true] {
            for group_size in [0, 1, 2, MAX_GROUP_SIZE, RegGroup::MAX_SIZE] {
                for num_hints in [0, 1, MAX_NUM_HINTS, MAX_NUM_HINTS + 9] {
                    for size in [0, 1, 1000, MAX_SIZE] {
                        let p = Priority::new(is_minimal, group_size, num_hints, size);
                        assert_eq!(p.is_minimal(), is_minimal, "{p:?}");
                        assert_eq!(p.group_size(), group_size.min(MAX_GROUP_SIZE), "{p:?}");
                        assert_eq!(p.num_hints(), num_hints.min(MAX_NUM_HINTS), "{p:?}");
                        assert_eq!(p.size(), size.min(MAX_SIZE), "{p:?}");
                    }
                }
            }
        }
    }

    /// Priorities compare by minimality first, then register group size, then
    /// how many of the bundle's spans are hinted, and only then by its size.
    #[test]
    fn priority_compares_by_tier() {
        let ascending = [
            Priority::new(false, 0, 0, 0),
            Priority::new(false, 0, 0, 1),
            Priority::new(false, 0, 0, MAX_SIZE),
            // One hinted span outranks every unhinted bundle, however large.
            Priority::new(false, 0, 1, 0),
            Priority::new(false, 0, MAX_NUM_HINTS, MAX_SIZE),
            // ... and group size still outranks any number of hints.
            Priority::new(false, 1, 0, 0),
            Priority::new(false, MAX_GROUP_SIZE, MAX_NUM_HINTS, MAX_SIZE),
            Priority::new(true, 0, 0, 0),
            Priority::new(true, MAX_GROUP_SIZE, MAX_NUM_HINTS, MAX_SIZE),
        ];
        for w in ascending.windows(2) {
            assert!(w[0] < w[1], "{:?} should sort below {:?}", w[0], w[1]);
        }
    }

    /// A queue entry's fields survive the round trip through its packed bits,
    /// including the largest bundle index a `LiveBundle<u32>` can name.
    #[test]
    fn pq_entry_round_trips_its_fields() {
        let priorities = [
            Priority::new(false, 0, 0, 0),
            Priority::new(true, MAX_GROUP_SIZE, MAX_NUM_HINTS, MAX_SIZE),
            Priority::new(true, 2, 1, 1000),
        ];
        for phase in PHASES {
            for priority in priorities {
                for index in [0, 1, 1000, LiveBundle::<u32>::MAX_REPRESENTABLE.index()] {
                    let entry = PqEntry::new(phase, priority, bundle(index));
                    assert_eq!(entry.phase(), phase, "{entry:?}");
                    assert_eq!(entry.priority(), priority, "{entry:?}");
                    assert_eq!(entry.bundle(), bundle(index), "{entry:?}");
                }
            }
        }
    }

    /// Queue entries compare by phase first, then by priority, and break
    /// remaining ties with the bundle index.
    #[test]
    fn pq_entry_compares_by_phase_then_priority_then_bundle() {
        let low = Priority::new(false, 0, 0, 0);
        let high = Priority::new(true, MAX_GROUP_SIZE, MAX_NUM_HINTS, MAX_SIZE);
        let max_index = LiveBundle::<u32>::MAX_REPRESENTABLE.index();

        let mut ascending = vec![
            PqEntry::new(Phase::AssignEvict, low, bundle(0)),
            PqEntry::new(Phase::AssignEvict, low, bundle(1)),
            PqEntry::new(Phase::AssignEvict, low, bundle(max_index)),
            PqEntry::new(Phase::AssignEvict, high, bundle(0)),
        ];
        // A later phase outranks any priority in an earlier one.
        for phase in PHASES.into_iter().skip(1) {
            ascending.push(PqEntry::new(phase, low, bundle(0)));
            ascending.push(PqEntry::new(phase, high, bundle(max_index)));
        }

        for w in ascending.windows(2) {
            assert!(w[0] < w[1], "{:?} should sort below {:?}", w[0], w[1]);
        }

        // And the queue pops the greatest entry first.
        let mut queue: BinaryHeap<PqEntry<u32>> = ascending.iter().copied().collect();
        let popped: Vec<_> = core::iter::from_fn(|| queue.pop()).collect();
        assert!(ascending.iter().rev().eq(popped.iter()));
    }

    /// An eviction cost's fields survive the round trip through its packed
    /// bits, up to the saturation of some and the lossiness of another.
    #[test]
    fn eviction_cost_round_trips_its_fields() {
        for stickiness in [
            0,
            1,
            MAX_STICKINESS - 1,
            MAX_STICKINESS,
            MAX_STICKINESS + 1,
            usize::MAX,
        ] {
            for is_minimal in [false, true] {
                for broken_hints in [
                    0,
                    1,
                    2,
                    1000,
                    MAX_BROKEN_HINTS - 1,
                    MAX_BROKEN_HINTS,
                    MAX_BROKEN_HINTS + 1,
                    usize::MAX,
                ] {
                    for weight in [0.0, 1.0, 3.25, 1e20, f32::INFINITY] {
                        let weight = SpillWeight::new(weight);
                        let cost = EvictionCost::new(stickiness, is_minimal, broken_hints, weight);
                        assert_eq!(
                            cost.stickiness(),
                            stickiness.min(MAX_STICKINESS),
                            "{cost:?}",
                        );
                        assert_eq!(cost.is_minimal(), is_minimal, "{cost:?}");
                        assert_eq!(
                            cost.broken_hints(),
                            broken_hints.min(MAX_BROKEN_HINTS),
                            "{cost:?}",
                        );
                        // A `SpillWeight` is already packed, so it survives
                        // exactly.
                        assert_eq!(cost.max_spill_weight(), weight, "{cost:?}");
                    }
                }
            }
        }
    }

    /// Eviction costs compare field by field, in the order they are packed:
    /// being one step stickier outweighs every other field put together, being
    /// minimal outweighs the two below it, and a broken hint outweighs any
    /// spill weight at all.
    #[test]
    fn eviction_costs_compare_field_by_field() {
        let ascending = [
            EvictionCost::new(0, false, 0, SpillWeight::new(0.0)),
            EvictionCost::new(0, false, 0, SpillWeight::new(1.0)),
            EvictionCost::new(0, false, 0, SpillWeight::new(1e20)),
            EvictionCost::new(0, false, 0, SpillWeight::new(f32::INFINITY)),
            EvictionCost::new(0, false, 1, SpillWeight::new(0.0)),
            EvictionCost::new(0, false, 1, SpillWeight::new(f32::INFINITY)),
            EvictionCost::new(0, false, 2, SpillWeight::new(0.0)),
            EvictionCost::new(0, false, MAX_BROKEN_HINTS, SpillWeight::new(0.0)),
            EvictionCost::new(0, false, MAX_BROKEN_HINTS, SpillWeight::new(f32::INFINITY)),
            EvictionCost::new(0, true, 0, SpillWeight::new(0.0)),
            EvictionCost::new(0, true, MAX_BROKEN_HINTS, SpillWeight::new(f32::INFINITY)),
            EvictionCost::new(1, false, 0, SpillWeight::new(0.0)),
            EvictionCost::new(1, true, MAX_BROKEN_HINTS, SpillWeight::new(f32::INFINITY)),
            EvictionCost::new(2, false, 0, SpillWeight::new(0.0)),
            EvictionCost::new(MAX_STICKINESS, false, 0, SpillWeight::new(0.0)),
            EvictionCost::new(
                MAX_STICKINESS,
                true,
                MAX_BROKEN_HINTS,
                SpillWeight::new(f32::INFINITY),
            ),
        ];
        for w in ascending.windows(2) {
            assert!(w[0] < w[1], "{:?} should sort below {:?}", w[0], w[1]);
        }

        // And saturation makes the top of each range a plateau, rather than
        // wrapping back around to the bottom of it -- or, worse, into the
        // field above.
        assert_eq!(
            EvictionCost::new(0, false, MAX_BROKEN_HINTS, SpillWeight::new(0.0)),
            EvictionCost::new(0, false, usize::MAX, SpillWeight::new(0.0)),
        );
        assert_eq!(
            EvictionCost::new(MAX_STICKINESS, false, 0, SpillWeight::new(0.0)),
            EvictionCost::new(usize::MAX, false, 0, SpillWeight::new(0.0)),
        );
    }

    /// Among bundles that are equally stuck, minimality is what decides: the
    /// budget an ordinary bundle brings to `assign_via_eviction` can never
    /// afford a minimal victim, whatever the two weigh, and a minimal bundle's
    /// budget can never afford a dearer minimal victim.
    ///
    /// Splitting is the only escape route left to a bundle the stack cannot
    /// hold, and a minimal bundle does not have it, so between two bundles
    /// with the same number of places to go the one that can still split is
    /// the one that should move. `try_evict_and_assign` takes a victim only
    /// when its cost is *strictly* cheaper than the budget, so "cannot afford"
    /// is `!(cost < budget)`.
    ///
    /// Stickiness outranks all of this, and is the one thing the rule gives
    /// way to: a victim with somewhere to go is affordable to anybody,
    /// however minimal it is and however little the bundle displacing it is
    /// worth.
    #[test]
    fn minimality_decides_between_equally_stuck_bundles() {
        let weights = [0.0, 1.0, 3.25, 1e20, f32::INFINITY].map(SpillWeight::new);

        for stickiness in [0, 1, MAX_STICKINESS - 1, MAX_STICKINESS] {
            for ours in weights {
                // A budget is built with no broken hints: we hold no register,
                // so evicting us breaks nothing.
                let ordinary = EvictionCost::new(stickiness, false, 0, ours);
                let minimal = EvictionCost::new(stickiness, true, 0, ours);

                for theirs in weights {
                    for broken_hints in [0, 1] {
                        let victim = EvictionCost::new(stickiness, true, broken_hints, theirs);
                        assert!(
                            !(victim < ordinary),
                            "an ordinary bundle at {ours:?} must not afford {victim:?}",
                        );

                        // A minimal bundle affords another minimal one only
                        // when that one is strictly cheaper, which is the same
                        // well-founded descent the whole ladder relies on.
                        assert_eq!(
                            victim < minimal,
                            (broken_hints, theirs) < (0, ours),
                            "a minimal bundle at {ours:?} against {victim:?}",
                        );

                        // But one place to go is enough to make it affordable
                        // to either of them.
                        if stickiness > 0 {
                            let unstuck =
                                EvictionCost::new(stickiness - 1, true, broken_hints, theirs);
                            assert!(
                                unstuck < ordinary && unstuck < minimal,
                                "{unstuck:?} has somewhere to go and must be affordable to \
                                 both {ordinary:?} and {minimal:?}",
                            );
                        }
                    }
                }
            }
        }
    }

    /// A minimal bundle that must have a register gets one, even when every
    /// register is held by a bundle that is dearer than it is.
    ///
    /// Those holders do not *need* a register -- an `Any` bundle can live on
    /// the stack at every one of its uses -- so they are the least sticky thing
    /// on the machine, and ordinary eviction takes one of their registers
    /// without any regard for what it is worth. The victim is requeued rather
    /// than spilled outright, so it can split around the minimal bundle and
    /// keep a register for its hot read.
    ///
    /// Deliberately not routed through `crate::test::check_allocation`, which
    /// answers `Ok` to `TooManyLiveRegs` on the grounds that not every function
    /// fits on every machine. This one fits.
    #[test]
    fn a_minimal_register_read_takes_a_register_from_a_stackable_bundle() {
        let test_input =
            crate::test::TestInput::with_a_minimal_register_read_among_stackable_values();
        let mut context = crate::Context::new();

        test_input.with_input(|input| {
            let output =
                crate::run(&mut context, input).expect("this function fits on this machine");
            crate::checker::check(input, &output).expect("and the allocation it gets is correct");
        });
    }

    /// A value carried through two sibling loops gets the same register in
    /// both, because their parent relays what the first loop allocated chose
    /// to the second.
    #[test]
    fn sibling_loops_agree_on_a_value_they_both_carry() {
        use crate::{Edit, InputFunction, InstOrEdit, Move};

        let test_input = crate::test::TestInput::with_a_value_read_in_two_sibling_loops();
        let mut context = crate::Context::new();

        test_input.with_input(|input| {
            let output =
                crate::run(&mut context, input).expect("this function fits on this machine");
            crate::checker::check(input, &output).expect("and the allocation is correct");

            let reg_moves = input
                .func
                .blocks()
                .flat_map(|(block, _)| output.block_insts_and_edits(input.func, block))
                .filter(|item| matches!(item, InstOrEdit::Edit(Edit::Move(Move::RegReg { .. }))))
                .count();
            assert_eq!(
                reg_moves, 0,
                "the carried value should stay in one register"
            );
        });
    }

    /// A value live through a loop that never reads it stays on the stack
    /// across the whole loop, rather than being reloaded inside it to suit a
    /// piece that won a register at the loop's header.
    #[test]
    fn a_value_unused_in_a_loop_is_not_reloaded_inside_it() {
        use crate::{Edit, InputFunction, InstOrEdit, Move};

        let test_input = crate::test::TestInput::with_a_value_live_through_a_busy_loop();
        let mut context = crate::Context::new();

        test_input.with_input(|input| {
            let output =
                crate::run(&mut context, input).expect("this function fits on this machine");
            crate::checker::check(input, &output).expect("and the allocation is correct");

            for (block, _) in input.func.blocks() {
                if output.loop_depth(block) == 0 {
                    continue;
                }
                let reloads = output
                    .block_insts_and_edits(input.func, block)
                    .filter(|item| {
                        matches!(item, InstOrEdit::Edit(Edit::Move(Move::Reload { .. })))
                    })
                    .count();
                assert_eq!(reloads, 0, "{block:?} is in the loop and reloads");
            }
        });
    }

    /// A bundle with no usable hint tries clobbered registers first, and within
    /// each tier leaves registers some other bundle prefers for last.
    #[test]
    fn non_preferred_candidates_avoid_other_bundles_hints() {
        let reg = |i: usize| Reg::try_new(i).unwrap();
        let set = |indices: &[usize]| {
            let mut set = RegSet::new();
            for &i in indices {
                set.insert(reg(i));
            }
            set
        };
        let class: Vec<Reg> = (0..6).map(reg).collect();

        let mut pref = RegPreference::new();
        pref.add_hint(set(&[4]));
        let clobbered = set(&[0, 1, 2]);
        let preferred = set(&[0, 3, 4]);

        let mut candidates = Vec::new();
        order_non_preferred_candidates(&class, &pref, &clobbered, &preferred, &mut candidates);

        // r4 is the bundle's own hint, already tried; r1 and r2 are clobbered
        // and unwanted; r0 is clobbered but wanted; r5 survives the clobber
        // and is unwanted; r3 survives it but is wanted.
        assert_eq!(candidates, [1, 2, 0, 5, 3].map(reg));
    }

    /// Within a region a weight is a hinted-span count times one block weight,
    /// so these tiers are counts: the rank separates a bundle's first few
    /// hints and then stops.
    #[test]
    fn hint_rank_saturates_past_a_bundles_first_hints() {
        assert_eq!(hint_rank(0.0), 0);

        // A cold block's 0.05 still outranks no hint.
        assert!(hint_rank(0.05) > hint_rank(0.0));
        assert!(hint_rank(1.0) > hint_rank(0.0));

        // A tier is ten hinted spans: one through nine rank alike.
        assert_eq!(hint_rank(1.0), hint_rank(9.0));
        assert!(hint_rank(10.0) > hint_rank(9.0));
        assert!(hint_rank(100.0) > hint_rank(10.0));

        // Saturating rather than overflowing the field.
        assert_eq!(hint_rank(1e300), MAX_NUM_HINTS);
        assert_eq!(hint_rank(1e300), hint_rank(1e7));

        assert_eq!(hint_rank(f64::NAN), 0);
        assert_eq!(hint_rank(f64::INFINITY), MAX_NUM_HINTS);
    }
}
