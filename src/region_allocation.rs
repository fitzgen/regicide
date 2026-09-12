//! Region-based allocation.
//!
//! We do a bottom-up walk of the region tree, allocating registers within each
//! region.

mod assignments;
mod splitting;

use crate::{
    Entity, Input, InputFunction, OperandConstraint, Position, RegSet,
    context::ContextInner,
    counts::Counts,
    entity::{EntityRepr, Region, SecondaryMap},
    error::{Error, IResult},
    events::{EventsLog, SplitKind},
    live_ranges::{LiveBundle, LivePoint, LiveRanges, SpillWeight},
    machine::{Machine, Reg, RegClassMembers},
    output::{OutputInner, RegAllocation},
    timing::Timing,
};
use alloc::{collections::BinaryHeap, vec::Vec};
use assignments::Assignments;
use core::{fmt, marker::PhantomData, ops::Range};
use splitting::{Cut, SplitUse, WithinSpanCut};

pub fn region_allocate<E>(
    context: &mut ContextInner<E>,
    input: &Input<'_, impl InputFunction>,
) -> IResult<()>
where
    E: EntityRepr,
{
    let _timing = Timing::new("region allocate");

    let ContextInner {
        counts,
        events,
        region_tree,
        live_ranges,
        region_allocation,
        output,
        ..
    } = context;

    // Reverse the pre-order so we visit children before parents.
    for region in region_tree.pre_order_iter().rev() {
        region_allocation.allocate_region(input, live_ranges, counts, events, output, region)?;
    }

    counts.final_live_spans += live_ranges.len_spans();
    counts.final_bundles += live_ranges.len_bundles();

    Ok(())
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

    /// The set of bundles that must be allocated to stack slots.
    ///
    /// We just remember the set for now, and actually allocate the stack slots
    /// in later passes.
    stack_bundles: Vec<LiveBundle<E>>,

    /// Scratch space holding the spans of the bundle being split.
    split_spans: Vec<Range<LivePoint<E>>>,

    /// Scratch space holding the uses of the bundle being split, likewise.
    split_uses: Vec<SplitUse<E>>,

    /// Scratch space holding the cuts that shred a bundle into minimal pieces.
    minimal_cuts: Vec<Cut<E>>,

    /// Scratch space for deduplicating the bundles in the way of a half, which
    /// [`Assignments::interference_weight`] borrows for the duration of a call
    /// and hands back empty.
    interference_scratch: Vec<LiveBundle<E>>,
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
            stack_bundles: Vec::new(),
            split_spans: Vec::new(),
            split_uses: Vec::new(),
            minimal_cuts: Vec::new(),
            interference_scratch: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        let RegionAllocation {
            assignments,
            region_assignments,
            queue,
            bundle_priority,
            stack_bundles,
            split_spans,
            split_uses,
            minimal_cuts,
            interference_scratch,
        } = self;
        assignments.reset();
        region_assignments.reset();
        queue.clear();
        bundle_priority.reset();
        stack_bundles.clear();
        split_spans.clear();
        split_uses.clear();
        minimal_cuts.clear();
        interference_scratch.clear();
    }

    pub fn is_reset(&self) -> bool {
        let RegionAllocation {
            assignments,
            region_assignments,
            queue,
            bundle_priority,
            stack_bundles,
            split_spans,
            split_uses,
            minimal_cuts,
            interference_scratch,
        } = self;
        assignments.is_reset()
            && region_assignments.is_reset()
            && queue.is_empty()
            && bundle_priority.is_reset()
            && stack_bundles.is_empty()
            && split_spans.is_empty()
            && split_uses.is_empty()
            && minimal_cuts.is_empty()
            && interference_scratch.is_empty()
    }

    /// The bundles that must live in memory, and so need a spill slot.
    pub(crate) fn stack_bundles(&self) -> &[LiveBundle<E>] {
        &self.stack_bundles
    }

    /// Did we leave `reg` unassigned over all of `span`?
    pub(crate) fn is_reg_free(
        &self,
        machine: &Machine,
        reg: Reg<E>,
        span: Range<LivePoint<E>>,
    ) -> bool {
        !self
            .assignments
            .conflicts(core::iter::once(reg.units(machine)), core::iter::once(span))
    }

    fn allocate_region(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        live_ranges: &mut LiveRanges<E>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        output: &mut OutputInner<E>,
        region: Region<E>,
    ) -> IResult<()> {
        debug_assert!(self.queue.is_empty());

        // Insert each bundle in this region into the queue.
        //
        // Okay to call `region.bundles(..)` because we haven't split any of
        // this region's bundles yet, because we haven't allocated registers
        // within this region yet.
        for bundle in region.bundles(live_ranges) {
            self.push_bundle(input, live_ranges, events, bundle, Phase::default());
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

            if phase <= Phase::AssignEvict
                && self.assign_via_eviction(input, live_ranges, events, output, entry)?
            {
                counts.evictions.inc();
                continue;
            }

            if phase <= Phase::SplitBetweenSpans
                && self.split_between_spans(input, live_ranges, counts, events, output, entry)?
            {
                counts.split_between_spans.inc();
                continue;
            }

            if phase <= Phase::SplitWithinSpan
                && self.split_within_span(input, live_ranges, counts, events, output, entry)?
            {
                counts.split_within_span.inc();
                continue;
            }

            self.split_into_minimal_or_spill(input, live_ranges, counts, events, output, entry)?;
            counts.split_into_minimal_or_spill.inc();
        }

        // Finally, commit this region's assignments.
        self.assignments.merge(&self.region_assignments);
        self.region_assignments.reset();

        Ok(())
    }

    fn push_bundle(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        live_ranges: &LiveRanges<E>,
        events: &mut EventsLog<E>,
        bundle: LiveBundle<E>,
        phase: Phase,
    ) {
        let priority = compute_bundle_priority(input, live_ranges, bundle);
        self.set_bundle_priority(bundle, priority);
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
                    debug_assert!(pref.is_subset_of(class.member_set(input.machine)));
                    debug_assert!(matches!(
                        class.members(input.machine),
                        RegClassMembers::Regs(_)
                    ));
                }
                OperandConstraint::Reg(rc) => {
                    debug_assert!(pref.is_subset_of(rc.member_set(input.machine)));
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
            pref.iter(),
            |r| r.units(input.machine),
            bundle
                .spans(live_ranges)
                .map(|s| s.start(live_ranges)..s.end(live_ranges)),
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
            RegClassMembers::Regs(regs) => self
                .region_assignments
                .try_assign_to_reg(
                    bundle,
                    regs.iter().copied().filter(|r| !pref.contains(*r)),
                    |r| r.units(input.machine),
                    bundle
                        .spans(live_ranges)
                        .map(|s| s.start(live_ranges)..s.end(live_ranges)),
                )
                .map(|reg| output.with_repr::<E, _>(reg).map(RegAllocation::Reg))
                .transpose()?,
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
                        bundle
                            .spans(live_ranges)
                            .map(|s| s.start(live_ranges)..s.end(live_ranges)),
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
                        preference: bundle.preference(live_ranges).clone(),
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
        // register, so evicting it doesn't break any hints. We never break a
        // hint to make room for a bundle that has none of its own.
        let max_cost = EvictionCost::new(0, SpillWeight::new(bundle.spill_weight(live_ranges)));

        let bundle_spans = |b: LiveBundle<E>| {
            b.spans(live_ranges)
                .map(|s| s.start(live_ranges)..s.end(live_ranges))
        };

        let evicted = match rc.members(machine) {
            RegClassMembers::Regs(regs) => self
                .region_assignments
                .try_evict_reg_and_assign(
                    bundle,
                    pref.iter()
                        .chain(regs.iter().copied().filter(|r| !pref.contains(*r))),
                    |r| r.units(machine),
                    max_cost,
                    |victim, reg| {
                        let broken_hints =
                            usize::from(victim.preference(live_ranges).contains(reg));
                        EvictionCost::new(
                            broken_hints,
                            SpillWeight::new(victim.spill_weight(live_ranges)),
                        )
                    },
                    bundle_spans,
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
                            let broken_hints = usize::from(
                                !victim
                                    .preference(live_ranges)
                                    .intersection(group.member_set(machine))
                                    .is_empty(),
                            );
                            EvictionCost::new(
                                broken_hints,
                                SpillWeight::new(victim.spill_weight(live_ranges)),
                            )
                        },
                        bundle_spans,
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
                self.push_bundle(input, live_ranges, events, evicted, Phase::AssignEvict);
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

        let pref = bundle.preference(live_ranges).clone();

        let rc = match bundle.constraint(live_ranges) {
            OperandConstraint::Any => bundle.value_reg_class(live_ranges, input),
            OperandConstraint::Reg(rc) => rc,
            OperandConstraint::Stack => unreachable!("already handled"),
            OperandConstraint::Reuse(_) => unreachable!("already resolved"),
        };

        let best = {
            let RegionAllocation {
                region_assignments,
                split_spans,
                split_uses,
                interference_scratch,
                ..
            } = self;

            match rc.members(input.machine) {
                RegClassMembers::Regs(regs) => splitting::best_split_between_spans(
                    split_spans,
                    split_uses,
                    pref.iter()
                        .chain(regs.iter().copied().filter(|r| !pref.contains(*r))),
                    |reg, half| {
                        region_assignments.interference_weight(
                            core::iter::once(reg.units(input.machine)),
                            half.iter(),
                            interference_scratch,
                            |victim| victim.spill_weight(live_ranges),
                        )
                    },
                )
                .map(|best| (best.cut, Some(best.candidate))),

                RegClassMembers::Groups(groups) => {
                    debug_assert!(pref.is_empty());
                    splitting::best_split_between_spans(
                        split_spans,
                        split_uses,
                        groups.iter().copied(),
                        |group, half| {
                            region_assignments.interference_weight(
                                group
                                    .members(input.machine)
                                    .iter()
                                    .map(|r| r.units(input.machine)),
                                half.iter(),
                                interference_scratch,
                                |victim| victim.spill_weight(live_ranges),
                            )
                        },
                    )
                    .map(|best| (best.cut, None))
                }
            }
        };

        self.split_spans.clear();
        self.split_uses.clear();

        let Some((index, winner)) = best else {
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

        event!(
            events,
            BundleSplitBetweenSpans {
                bundle,
                suffix,
                at: first_span_start(live_ranges, suffix),
                index,
            }
        );

        if let Some(reg) = winner {
            let mut winning_reg = RegSet::new();
            winning_reg.insert(reg);

            suffix.add_hint(live_ranges, events, &winning_reg, None);
            suffix.add_hint(live_ranges, events, &pref, None);

            bundle.add_hint(live_ranges, events, &winning_reg, None);
            // Note: `bundle` already has a hint of `pref`, no need to add it
            // again.
        }

        // Push again with the same phase: we can afford to keep splitting
        // between spans until we can't split between spans anymore.
        self.push_bundle(input, live_ranges, events, bundle, entry.phase());
        self.push_bundle(input, live_ranges, events, suffix, entry.phase());

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

        let pref = bundle.preference(live_ranges).clone();

        let rc = match bundle.constraint(live_ranges) {
            OperandConstraint::Any => bundle.value_reg_class(live_ranges, input),
            OperandConstraint::Reg(rc) => rc,
            OperandConstraint::Stack => unreachable!("already handled"),
            OperandConstraint::Reuse(_) => unreachable!("already resolved"),
        };

        let (cut, winner) = {
            let RegionAllocation {
                region_assignments,
                split_spans,
                split_uses,
                interference_scratch,
                ..
            } = self;

            match rc.members(input.machine) {
                RegClassMembers::Regs(regs) => {
                    let best = splitting::best_split_within_span(
                        split_spans,
                        split_uses,
                        pref.iter()
                            .chain(regs.iter().copied().filter(|r| !pref.contains(*r))),
                        |reg, half| {
                            region_assignments.interference_weight(
                                core::iter::once(reg.units(input.machine)),
                                half.iter(),
                                interference_scratch,
                                |victim| victim.spill_weight(live_ranges),
                            )
                        },
                    )
                    .expect("already rejected unsplittable bundles");
                    (best.cut, Some(best.candidate))
                }
                RegClassMembers::Groups(groups) => {
                    debug_assert!(pref.is_empty());
                    let best = splitting::best_split_within_span(
                        split_spans,
                        split_uses,
                        groups.iter().copied(),
                        |group, half| {
                            region_assignments.interference_weight(
                                group
                                    .members(input.machine)
                                    .iter()
                                    .map(|r| r.units(input.machine)),
                                half.iter(),
                                interference_scratch,
                                |victim| victim.spill_weight(live_ranges),
                            )
                        },
                    )
                    .expect("already rejected unsplittable bundles");
                    (best.cut, None)
                }
            }
        };

        self.split_spans.clear();
        self.split_uses.clear();

        // Name the span before the split rewrites it in place.
        let span = bundle
            .spans(live_ranges)
            .nth(cut.index)
            .expect("a cut names one of the bundle's spans");

        let suffix =
            bundle.split_at_point(live_ranges, input, events, output, cut.index, cut.at)?;

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
        self.push_bundle(input, live_ranges, events, bundle, phase);
        self.push_bundle(input, live_ranges, events, suffix, phase);

        Ok(true)
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
        cuts.extend(splitting::minimal_cuts(&self.split_spans, &self.split_uses));
        self.split_spans.clear();
        self.split_uses.clear();

        debug_assert_eq!(
            bundle.is_minimal(live_ranges),
            cuts.is_empty(),
            "a bundle is minimal iff there is nothing left to cut",
        );

        let result = (|| {
            if cuts.is_empty() {
                match bundle.constraint(live_ranges) {
                    // Free to live on the stack.
                    OperandConstraint::Any | OperandConstraint::Stack => {}
                    // It wants a register, we could not find one for it, and
                    // there is nothing left to try.
                    OperandConstraint::Reg(_) => return output.error(Error::TooManyLiveRegs),
                    OperandConstraint::Reuse(_) => unreachable!("already resolved"),
                }
                counts.spilled_bundles.inc();
                self.stack_bundles.push(bundle);
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

            let pref = bundle.preference(live_ranges).clone();

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
                piece.add_hint(live_ranges, events, &pref, None);
                self.push_bundle(
                    input,
                    live_ranges,
                    events,
                    piece,
                    Phase::SplitIntoMinimalOrSpill,
                );
            }

            self.push_bundle(
                input,
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

fn compute_bundle_priority<E>(
    input: &Input<'_, impl InputFunction>,
    live_ranges: &LiveRanges<E>,
    bundle: LiveBundle<E>,
) -> Priority
where
    E: EntityRepr,
{
    Priority::new(
        bundle.has_fixed_uses(live_ranges),
        bundle.is_minimal(live_ranges),
        bundle_group_size(input, live_ranges, bundle),
        bundle.spans(live_ranges).len(),
    )
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
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Phase {
    /// The initial phase.
    ///
    /// Try to assign the bundle, evicting another lower-priority bundle if
    /// necessary.
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
    ///    Bit:   31   ...  30   29                28             27  ...   25   24  ...  0
    ///         +--------------+-----------------+--------------+--------------+------------+
    /// Fields: | (reserved):2 | has_fixed_use:1 | is_minimal:1 | group_size:3 |   size:25  |
    ///         +--------------+-----------------+--------------+--------------+------------+
    ///
    /// Packed so that we sort/prioritize bundles by:
    ///
    /// 1. Those with fixed register uses (as they have the hardest constraints
    ///    to satisfy)
    ///
    /// 2. Minimal bundles (as these can't be split any further, so allocating
    ///    to a register, rather than a spill slot, is now-or-never).
    ///
    /// 3. The size of its register group constraint (because assigning a
    ///    register groups assigns N registers at once, not just 1, so they are
    ///    harder to place and have more constraints than regular bundles).
    ///
    /// 4. Finally, by the bundle's size (number of spans) because if we assign
    ///    a larger bundle, then we get fewer moves and better codegen (and if
    ///    assigning it fails, we can always split it and try again).
    ///
    /// NB: the upper bits are reserved for encoding a `Phase` when this is
    /// packed inside a `PqEntry`.
    bits: u32,
}

const PRIORITY_SIZE_BITS: u32 = 25;
const PRIORITY_SIZE_SHIFT: u32 = 0;
const PRIORITY_SIZE_MASK: u32 = ((1 << PRIORITY_SIZE_BITS) - 1) << PRIORITY_SIZE_SHIFT;

const PRIORITY_GROUP_SIZE_BITS: u32 = 3;
const PRIORITY_GROUP_SIZE_SHIFT: u32 = PRIORITY_SIZE_SHIFT + PRIORITY_SIZE_BITS;
const PRIORITY_GROUP_SIZE_MASK: u32 =
    ((1 << PRIORITY_GROUP_SIZE_BITS) - 1) << PRIORITY_GROUP_SIZE_SHIFT;
const PRIORITY_GROUP_SIZE_MAX: usize = (1 << PRIORITY_GROUP_SIZE_BITS) - 1;

const PRIORITY_IS_MINIMAL_BITS: u32 = 1;
const PRIORITY_IS_MINIMAL_SHIFT: u32 = PRIORITY_GROUP_SIZE_SHIFT + PRIORITY_GROUP_SIZE_BITS;
const PRIORITY_IS_MINIMAL_MASK: u32 =
    ((1 << PRIORITY_IS_MINIMAL_BITS) - 1) << PRIORITY_IS_MINIMAL_SHIFT;

const PRIORITY_HAS_FIXED_USE_BITS: u32 = 1;
const PRIORITY_HAS_FIXED_USE_SHIFT: u32 = PRIORITY_IS_MINIMAL_SHIFT + PRIORITY_IS_MINIMAL_BITS;
const PRIORITY_HAS_FIXED_USE_MASK: u32 =
    ((1 << PRIORITY_HAS_FIXED_USE_BITS) - 1) << PRIORITY_HAS_FIXED_USE_SHIFT;

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
            .field("has_fixed_use", &self.has_fixed_use())
            .field("is_minimal", &self.is_minimal())
            .field("group_size", &self.group_size())
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

    fn new(has_fixed_use: bool, is_minimal: bool, group_size: usize, size: usize) -> Self {
        let has_fixed_use = u32::from(has_fixed_use) << PRIORITY_HAS_FIXED_USE_SHIFT;
        debug_assert_eq!(has_fixed_use & PRIORITY_HAS_FIXED_USE_MASK, has_fixed_use);

        let is_minimal = u32::from(is_minimal) << PRIORITY_IS_MINIMAL_SHIFT;
        debug_assert_eq!(is_minimal & PRIORITY_IS_MINIMAL_MASK, is_minimal);

        let group_size = u32::try_from(group_size.min(PRIORITY_GROUP_SIZE_MAX)).unwrap();
        let group_size = group_size << PRIORITY_GROUP_SIZE_SHIFT;
        debug_assert_eq!(group_size & PRIORITY_GROUP_SIZE_MASK, group_size);

        let max_size = (1 << PRIORITY_SIZE_BITS) - 1;
        debug_assert!(size <= max_size);
        let size = u32::try_from(size).unwrap();
        let size = size << PRIORITY_SIZE_SHIFT;
        debug_assert_eq!(size & PRIORITY_SIZE_MASK, size);

        Priority {
            bits: has_fixed_use | is_minimal | group_size | size,
        }
    }

    #[inline]
    fn has_fixed_use(&self) -> bool {
        self.bits & PRIORITY_HAS_FIXED_USE_MASK != 0
    }

    #[inline]
    fn is_minimal(&self) -> bool {
        self.bits & PRIORITY_IS_MINIMAL_MASK != 0
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
    ///  Bits:   31    ...    16   15      ...       0
    ///        +-----------------+---------------------+
    /// Field: | broken_hints:16 | max_spill_weight:16 |
    ///        +-----------------+---------------------+
    ///
    /// Note: `broken_hints` comes first so we sort by that first and then
    /// `max_spill_weight` second.
    bits: u32,
}

const EVICTION_COST_MAX_SPILL_WEIGHT_BITS: u32 = 16;
const EVICTION_COST_MAX_SPILL_WEIGHT_SHIFT: u32 = 0;
const EVICTION_COST_MAX_SPILL_WEIGHT_MASK: u32 =
    ((1 << EVICTION_COST_MAX_SPILL_WEIGHT_BITS) - 1) << EVICTION_COST_MAX_SPILL_WEIGHT_SHIFT;

const EVICTION_COST_BROKEN_HINTS_BITS: u32 = 16;
const EVICTION_COST_BROKEN_HINTS_SHIFT: u32 =
    EVICTION_COST_MAX_SPILL_WEIGHT_SHIFT + EVICTION_COST_MAX_SPILL_WEIGHT_BITS;
const EVICTION_COST_BROKEN_HINTS_MASK: u32 =
    ((1 << EVICTION_COST_BROKEN_HINTS_BITS) - 1) << EVICTION_COST_BROKEN_HINTS_SHIFT;
const EVICTION_COST_BROKEN_HINTS_MAX: usize = (1 << EVICTION_COST_BROKEN_HINTS_BITS) - 1;

impl fmt::Debug for EvictionCost {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EvictionCost")
            .field("broken_hints", &self.broken_hints())
            .field("max_spill_weight", &self.max_spill_weight())
            .finish()
    }
}

impl EvictionCost {
    fn new(broken_hints: usize, max_spill_weight: SpillWeight) -> Self {
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
            bits: broken_hints | max_spill_weight,
        }
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
    use crate::{context::Context, events::Event, test::TestInput};
    #[cfg(feature = "visualizer")]
    use mutatis::check::{Check, CheckResult};
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
            } = inner;
            let func = input.func;
            rpo.construct(func, dfs, output)?;
            region_tree.construct(func, counts, dfs, output)?;
            liveness.construct(func, counts, rpo, output)?;
            live_ranges.construct(input, counts, events, liveness, output)?;
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

    /// Every bundle and every span that exists at the end of allocation can be
    /// traced back to the event that created it.
    ///
    /// This is what keeps the visualizer's parent links trustworthy: a split
    /// that forgets to log its parentage orphans a piece here.
    #[cfg(feature = "visualizer")]
    #[test]
    fn everything_has_a_provenance() -> CheckResult<TestInput> {
        Check::new()
            .iters(1_000)
            .run(|test_input: &TestInput| -> Result<(), String> {
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
                                    "a span split rewrites its first piece in place, so {first:?} \
                                     should be {parent:?}"
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
            })
    }

    /// The queue events tell the whole story of the queue: nothing is popped
    /// that was not queued, and every pop ends in exactly one outcome.
    #[cfg(feature = "visualizer")]
    #[test]
    fn every_pop_is_queued_and_resolved() -> CheckResult<TestInput> {
        Check::new()
            .iters(1_000)
            .run(|test_input: &TestInput| -> Result<(), String> {
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
                                _ => return Err(format!("popped {bundle:?} without queueing it")),
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
            })
    }

    const MAX_SIZE: usize = (1 << PRIORITY_SIZE_BITS) - 1;
    const MAX_GROUP_SIZE: usize = PRIORITY_GROUP_SIZE_MAX;
    const MAX_BROKEN_HINTS: usize = EVICTION_COST_BROKEN_HINTS_MAX;

    /// Every phase, in ascending order.
    const PHASES: [Phase; 4] = [
        Phase::AssignEvict,
        Phase::SplitBetweenSpans,
        Phase::SplitWithinSpan,
        Phase::SplitIntoMinimalOrSpill,
    ];

    fn bundle(index: usize) -> LiveBundle<u32> {
        LiveBundle::try_new(index).unwrap()
    }

    /// A priority's fields survive the round trip through its packed bits.
    #[test]
    fn priority_round_trips_its_fields() {
        for has_fixed_use in [false, true] {
            for is_minimal in [false, true] {
                for group_size in [0, 1, 2, MAX_GROUP_SIZE, RegGroup::MAX_SIZE] {
                    for size in [0, 1, 1000, MAX_SIZE] {
                        let p = Priority::new(has_fixed_use, is_minimal, group_size, size);
                        assert_eq!(p.has_fixed_use(), has_fixed_use, "{p:?}");
                        assert_eq!(p.is_minimal(), is_minimal, "{p:?}");
                        assert_eq!(p.group_size(), group_size.min(MAX_GROUP_SIZE), "{p:?}");
                        assert_eq!(p.size(), size.min(MAX_SIZE), "{p:?}");
                    }
                }
            }
        }
    }

    /// Priorities compare by fixed uses first, then minimality, then register
    /// group size, and only then by the bundle's own size.
    #[test]
    fn priority_compares_by_tier() {
        let ascending = [
            Priority::new(false, false, 0, 0),
            Priority::new(false, false, 0, 1),
            Priority::new(false, false, 0, MAX_SIZE),
            Priority::new(false, false, 1, 0),
            Priority::new(false, false, MAX_GROUP_SIZE, MAX_SIZE),
            Priority::new(false, true, 0, 0),
            Priority::new(false, true, MAX_GROUP_SIZE, MAX_SIZE),
            Priority::new(true, false, 0, 0),
            Priority::new(true, true, MAX_GROUP_SIZE, MAX_SIZE),
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
            Priority::new(false, false, 0, 0),
            Priority::new(true, true, MAX_GROUP_SIZE, MAX_SIZE),
            Priority::new(false, true, 2, 1000),
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
        let low = Priority::new(false, false, 0, 0);
        let high = Priority::new(true, true, MAX_GROUP_SIZE, MAX_SIZE);
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
    /// bits, up to the saturation of the one and the lossiness of the other.
    #[test]
    fn eviction_cost_round_trips_its_fields() {
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
                let cost = EvictionCost::new(broken_hints, weight);
                assert_eq!(
                    cost.broken_hints(),
                    broken_hints.min(MAX_BROKEN_HINTS),
                    "{cost:?}",
                );
                // A `SpillWeight` is already packed, so it survives exactly.
                assert_eq!(cost.max_spill_weight(), weight, "{cost:?}");
            }
        }
    }

    /// Eviction costs compare by broken hints first: any number of them
    /// outweighs any spill weight at all.
    #[test]
    fn eviction_cost_compares_by_broken_hints_then_spill_weight() {
        let ascending = [
            EvictionCost::new(0, SpillWeight::new(0.0)),
            EvictionCost::new(0, SpillWeight::new(1.0)),
            EvictionCost::new(0, SpillWeight::new(1e20)),
            EvictionCost::new(0, SpillWeight::new(f32::INFINITY)),
            EvictionCost::new(1, SpillWeight::new(0.0)),
            EvictionCost::new(1, SpillWeight::new(f32::INFINITY)),
            EvictionCost::new(2, SpillWeight::new(0.0)),
            EvictionCost::new(MAX_BROKEN_HINTS, SpillWeight::new(0.0)),
            EvictionCost::new(MAX_BROKEN_HINTS, SpillWeight::new(f32::INFINITY)),
        ];
        for w in ascending.windows(2) {
            assert!(w[0] < w[1], "{:?} should sort below {:?}", w[0], w[1]);
        }

        // And saturation makes the top of the range a plateau, rather than
        // wrapping back around to the bottom of it.
        assert_eq!(
            EvictionCost::new(MAX_BROKEN_HINTS, SpillWeight::new(0.0)),
            EvictionCost::new(usize::MAX, SpillWeight::new(0.0)),
        );
    }
}
