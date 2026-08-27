//! The set of assignments of live bundles to register units.

use crate::{
    Entity, Reg, RegGroup, RegUnit,
    entity::{EntityRepr, SecondaryMap},
    live_ranges::{LiveBundle, LivePoint},
    region_allocation::EvictionCost,
};
use alloc::{collections::BTreeMap, vec::Vec};
use core::{iter, ops::ControlFlow, ops::Range};

/// The key by which a register unit's assignments are ordered.
///
/// The spans inside one `RegUnitAssignments` can never overlap, as that would
/// represent a conflicting assignment, so we key by just the spans' start
/// points.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct AssignmentKey<E>
where
    E: EntityRepr,
{
    start: LivePoint<E>,
}

impl<E> AssignmentKey<E>
where
    E: EntityRepr,
{
    const fn new(start: LivePoint<E>) -> Self {
        Self { start }
    }
}

#[derive(Clone, Debug)]
struct Assignment<E>
where
    E: EntityRepr,
{
    /// The end of this assignment's span.
    ///
    /// The span's start is `AssignmentKey::start`.
    end: LivePoint<E>,

    /// The bundle that this assignment came from.
    bundle: LiveBundle<E>,
}

/// A map of all the assignments to a register unit.
///
/// When a bundle is assigned to a unit as part of assigning its register or
/// register group, we add an entry to the unit's associated
/// `RegUnitAssignments` for each span in that bundle.
type RegUnitAssignments<E> = BTreeMap<AssignmentKey<E>, Assignment<E>>;

pub struct Assignments<E>
where
    E: EntityRepr,
{
    assignments: SecondaryMap<RegUnit, RegUnitAssignments<E>>,
}

fn iter_reg_units(
    reg_units: impl Iterator<Item = Range<RegUnit>>,
) -> impl Iterator<Item = RegUnit> {
    reg_units.flat_map(|units| {
        debug_assert!(units.start <= units.end);
        (units.start.to_bits()..units.end.to_bits()).map(|i| RegUnit::from_bits(i))
    })
}

impl<E> Assignments<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        Self {
            assignments: SecondaryMap::new(RegUnitAssignments::new()),
        }
    }

    pub fn reset(&mut self) {
        let Self { assignments } = self;
        assignments.reset();
    }

    pub fn is_reset(&self) -> bool {
        let Self { assignments } = self;
        assignments.is_reset()
    }

    /// Call `f` on every existing assignment that overlaps one of the given
    /// spans.
    fn for_each_overlapping<T>(
        &self,
        reg_units: impl Iterator<Item = Range<RegUnit>>,
        spans: impl ExactSizeIterator<Item = Range<LivePoint<E>>> + Clone,
        mut f: impl FnMut(&Assignment<E>) -> ControlFlow<T>,
    ) -> Option<T> {
        for unit in iter_reg_units(reg_units) {
            for span in spans.clone() {
                for (existing_key, existing) in self.assignments[unit]
                    .range(..AssignmentKey::new(span.end))
                    .rev()
                    .take_while(|(_, existing)| span.start < existing.end)
                {
                    if LivePoint::spans_overlap(
                        span.start,
                        span.end,
                        existing_key.start,
                        existing.end,
                    ) {
                        if let ControlFlow::Break(result) = f(existing) {
                            return Some(result);
                        }
                    }
                }
            }
        }
        None
    }

    /// The total weight of the distinct bundles already assigned in `reg_units`
    /// that overlap `spans`.
    ///
    /// This is what it would cost to make room for `spans` in `reg_units`.
    pub fn interference_weight(
        &self,
        reg_units: impl Iterator<Item = Range<RegUnit>>,
        spans: impl ExactSizeIterator<Item = Range<LivePoint<E>>> + Clone,
        scratch: &mut Vec<LiveBundle<E>>,
        weight_of: impl Fn(LiveBundle<E>) -> f32,
    ) -> f32 {
        debug_assert!(scratch.is_empty());

        self.for_each_overlapping::<()>(reg_units, spans, |existing| {
            scratch.push(existing.bundle);
            ControlFlow::Continue(())
        });

        scratch.sort_unstable();
        scratch.dedup();

        let weight = scratch.iter().copied().map(weight_of).sum();
        scratch.clear();
        weight
    }

    /// Do the given spans conflict with any existing assignments in `reg_units`?
    fn conflicts(
        &self,
        reg_units: impl Iterator<Item = Range<RegUnit>>,
        spans: impl ExactSizeIterator<Item = Range<LivePoint<E>>> + Clone,
    ) -> bool {
        self.for_each_overlapping(reg_units, spans, |_| ControlFlow::Break(()))
            .is_some()
    }

    /// The one and only bundle whose existing assignments in `reg_units`
    /// conflict with the given spans, if there is exactly one such bundle.
    ///
    /// TODO: support evicting multiple bundles if that is still cheaper. will
    /// require an `&mut Vec<LiveBundle>` out parameter to these methods for
    /// writing the evicted bundles into.
    fn sole_conflicting_bundle(
        &self,
        reg_units: impl Iterator<Item = Range<RegUnit>>,
        spans: impl ExactSizeIterator<Item = Range<LivePoint<E>>> + Clone,
    ) -> Option<LiveBundle<E>> {
        let mut sole = None;
        let too_many = self.for_each_overlapping(reg_units, spans, |existing| match sole {
            Some(bundle) if bundle == existing.bundle => ControlFlow::Continue(()),
            Some(_) => ControlFlow::Break(()),
            None => {
                sole = Some(existing.bundle);
                ControlFlow::Continue(())
            }
        });
        if too_many.is_some() { None } else { sole }
    }

    /// Remove all of `bundle`'s assignments.
    ///
    /// `spans` must be exactly the spans that `bundle` was assigned with.
    fn remove_assignment(
        &mut self,
        bundle: LiveBundle<E>,
        spans: impl ExactSizeIterator<Item = Range<LivePoint<E>>> + Clone,
    ) {
        for (_unit, unit_assignments) in self.assignments.iter_mut() {
            for span in spans.clone() {
                let key = AssignmentKey::new(span.start);
                if unit_assignments
                    .get(&key)
                    .is_some_and(|existing| existing.bundle == bundle)
                {
                    unit_assignments.remove(&key);
                }
            }
        }
    }

    /// Insert a new assignment.
    ///
    /// The new assignment's spans must not conflict with any existing
    /// assignment.
    fn insert_assignment(
        &mut self,
        bundle: LiveBundle<E>,
        reg_units: impl Iterator<Item = Range<RegUnit>> + Clone,
        spans: impl ExactSizeIterator<Item = Range<LivePoint<E>>> + Clone,
    ) {
        debug_assert!(!self.conflicts(reg_units.clone(), spans.clone()));
        for unit in iter_reg_units(reg_units) {
            for span in spans.clone() {
                let old_entry = self.assignments[unit].insert(
                    AssignmentKey::new(span.start),
                    Assignment {
                        end: span.end,
                        bundle,
                    },
                );
                debug_assert!(old_entry.is_none());
            }
        }
    }

    /// Try to insert an assignment.
    ///
    /// If the proposed assignment does not conflict with any existing
    /// assignments, insert it and return `true`. Otherwise, when it does
    /// conflict with an existing assignment, return `false` and leave `self`
    /// unmodified.
    pub fn try_assign_to_reg(
        &mut self,
        bundle: LiveBundle<E>,
        candidates: impl IntoIterator<Item = Reg>,
        reg_units: impl Fn(Reg) -> Range<RegUnit>,
        spans: impl ExactSizeIterator<Item = Range<LivePoint<E>>> + Clone,
    ) -> bool {
        debug_assert!(spans.len() > 0);

        for reg in candidates {
            let units = iter::once(reg_units(reg));
            if !self.conflicts(units.clone(), spans.clone()) {
                self.insert_assignment(bundle, units, spans);
                return true;
            }
        }

        false
    }

    /// Try to insert an assignment of `bundle` to one of the candidate register
    /// groups.
    ///
    /// If the proposed assignment does not conflict with any existing
    /// assignments, insert it and return `true`. Otherwise, when it does
    /// conflict with an existing assignment, return `false` and leave `self`
    /// unmodified.
    pub fn try_assign_to_reg_group<GroupUnits>(
        &mut self,
        bundle: LiveBundle<E>,
        candidates: impl IntoIterator<Item = RegGroup>,
        group_units: impl Fn(RegGroup) -> GroupUnits,
        spans: impl ExactSizeIterator<Item = Range<LivePoint<E>>> + Clone,
    ) -> bool
    where
        GroupUnits: Iterator<Item = Range<RegUnit>> + Clone,
    {
        debug_assert!(spans.len() > 0);

        for group in candidates {
            let units = group_units(group);
            if !self.conflicts(units.clone(), spans.clone()) {
                self.insert_assignment(bundle, units, spans);
                return true;
            }
        }

        false
    }

    fn try_evict_and_assign<C, Units, Spans>(
        &mut self,
        bundle: LiveBundle<E>,
        candidates: impl IntoIterator<Item = C>,
        candidate_units: impl Fn(C) -> Units,
        max_cost: EvictionCost,
        eviction_cost: impl Fn(LiveBundle<E>, C) -> EvictionCost,
        bundle_spans: impl Fn(LiveBundle<E>) -> Spans,
    ) -> Option<LiveBundle<E>>
    where
        C: Copy,
        Units: Iterator<Item = Range<RegUnit>> + Clone,
        Spans: ExactSizeIterator<Item = Range<LivePoint<E>>> + Clone,
    {
        let spans = bundle_spans(bundle);
        debug_assert!(spans.len() > 0);

        // A tuple of:
        //
        // 1. the bundle that would be evicted, and
        // 2. the candidate that bundle is assigned to.
        let mut best: Option<(LiveBundle<E>, C)> = None;

        // The best (cheapest) eviction cost seen. Only ever taking a *strictly*
        // cheaper candidate means we both refuse evictions that are not worth
        // it and let the earliest of equally-cheap candidates win, so that the
        // caller's ordering of `candidates` decides.
        let mut best_cost = max_cost;

        for candidate in candidates {
            let units = candidate_units(candidate);
            debug_assert!(self.conflicts(units.clone(), spans.clone()));

            // Evicting a candidate bundle must make this bundle assignable (not
            // conflict), or else the bundle is not a valid eviction candidate.
            let Some(other_bundle) = self.sole_conflicting_bundle(units, spans.clone()) else {
                continue;
            };

            let cost = eviction_cost(other_bundle, candidate);
            if cost < best_cost {
                best = Some((other_bundle, candidate));
                best_cost = cost;
            }
        }

        let Some((other_bundle, candidate)) = best else {
            return None;
        };

        self.remove_assignment(other_bundle, bundle_spans(other_bundle));
        self.insert_assignment(bundle, candidate_units(candidate), spans);
        Some(other_bundle)
    }

    /// Try to insert an assignment for `bundle`, evicting another bundle if
    /// necessary.
    ///
    /// If `bundle` was assigned, then returns the other `LiveBundle` that was
    /// evicted. Otherwise, returns `None` and `self` is unmodified.
    pub fn try_evict_reg_and_assign<Spans>(
        &mut self,
        bundle: LiveBundle<E>,
        candidates: impl IntoIterator<Item = Reg>,
        reg_units: impl Fn(Reg) -> Range<RegUnit>,
        max_cost: EvictionCost,
        eviction_cost: impl Fn(LiveBundle<E>, Reg) -> EvictionCost,
        bundle_spans: impl Fn(LiveBundle<E>) -> Spans,
    ) -> Option<LiveBundle<E>>
    where
        Spans: ExactSizeIterator<Item = Range<LivePoint<E>>> + Clone,
    {
        self.try_evict_and_assign(
            bundle,
            candidates,
            |reg| iter::once(reg_units(reg)),
            max_cost,
            eviction_cost,
            bundle_spans,
        )
    }

    /// Like `try_evict_reg_and_assign` but for `RegGroup`s.
    pub fn try_evict_reg_group_and_assign<GroupUnits, Spans>(
        &mut self,
        bundle: LiveBundle<E>,
        candidates: impl IntoIterator<Item = RegGroup>,
        group_units: impl Fn(RegGroup) -> GroupUnits,
        max_cost: EvictionCost,
        eviction_cost: impl Fn(LiveBundle<E>, RegGroup) -> EvictionCost,
        bundle_spans: impl Fn(LiveBundle<E>) -> Spans,
    ) -> Option<LiveBundle<E>>
    where
        GroupUnits: Iterator<Item = Range<RegUnit>> + Clone,
        Spans: ExactSizeIterator<Item = Range<LivePoint<E>>> + Clone,
    {
        self.try_evict_and_assign(
            bundle,
            candidates,
            group_units,
            max_cost,
            eviction_cost,
            bundle_spans,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Inst, Position, live_ranges::SpillWeight};
    use mutatis::{
        Mutate,
        check::{Check, CheckResult},
        mutators as m,
    };
    use std::{
        format,
        string::{String, ToString},
        vec,
        vec::Vec,
    };

    fn bundle(index: usize) -> LiveBundle<u32> {
        LiveBundle::try_new(index).unwrap()
    }

    /// The number of instructions that a generated span may name.
    ///
    /// This is small on purpose because we want to generate overlapping spans.
    const NUM_INSTS: u8 = 4;

    const NUM_POINTS: u8 = NUM_INSTS * 2;
    const NUM_REGS: usize = REG_UNITS.len();
    const NUM_UNITS: usize = 4;

    /// ```text
    ///  unit:    0    1    2    3
    ///         +----+----+----+----+
    ///         | r0 | r1 | r2 | r3 |
    ///         +---------+---------+
    ///         |    r4   |    r5   |
    ///         +---------+---------+
    ///
    ///         r6: no units, non-allocatable
    /// ```
    const REG_UNITS: [Range<usize>; 7] = [
        0..1, // r0
        1..2, // r1
        2..3, // r2
        3..4, // r3
        0..2, // r4
        2..4, // r5
        0..0, // r6
    ];

    const R0: u8 = 0;
    const R1: u8 = 1;
    const R2: u8 = 2;
    const R3: u8 = 3;
    const R4: u8 = 4;
    const R5: u8 = 5;
    const R6: u8 = 6;

    const REG_GROUPS: [&[u8]; 8] = [
        // g0: an adjacent pair, exactly the units of r4.
        &[R0, R1],
        // g1: the other pair, exactly the units of r5.
        &[R2, R3],
        // g2: straddles the r4/r5 boundary.
        &[R1, R2],
        // g3: out of unit order and non-contiguous.
        &[R3, R0],
        // g4: the two wide registers, so every unit.
        &[R4, R5],
        // g5: one real member and one that covers no units.
        &[R0, R6],
        // g6: three members.
        &[R0, R1, R2],
        // g7: three members, shifted down one from g6.
        &[R1, R2, R3],
    ];

    const G0: u8 = 0;
    const G1: u8 = 1;
    const G2: u8 = 2;
    const G3: u8 = 3;
    const G4: u8 = 4;
    const G5: u8 = 5;
    const G6: u8 = 6;
    const G7: u8 = 7;

    const NUM_GROUPS: usize = REG_GROUPS.len();

    const MAX_OPS: usize = 12;
    const MAX_CANDIDATES: usize = 4;
    const MAX_SPANS: usize = 4;
    const NUM_BUNDLES: u8 = 4;

    fn unit(index: usize) -> RegUnit {
        RegUnit::try_new(index).unwrap()
    }

    fn reg(index: u8) -> Reg {
        Reg::try_new(usize::from(index)).unwrap()
    }

    fn reg_units(reg: Reg) -> Range<RegUnit> {
        let units = REG_UNITS[reg.index()].clone();
        if units.is_empty() {
            Entity::MAX_REPRESENTABLE..Entity::MAX_REPRESENTABLE
        } else {
            unit(units.start)..unit(units.end)
        }
    }

    fn group(index: u8) -> RegGroup {
        RegGroup::try_new(usize::from(index)).unwrap()
    }

    fn group_units(group: RegGroup) -> impl Iterator<Item = Range<RegUnit>> + Clone {
        REG_GROUPS[group.index()].iter().map(|&r| reg_units(reg(r)))
    }

    fn point(index: u8) -> LivePoint<u32> {
        debug_assert!(index <= NUM_POINTS);
        let index = usize::from(index);
        let pos = if index % 2 == 0 {
            Position::Early
        } else {
            Position::Late
        };
        let inst = Inst::try_new(index / 2).unwrap();
        LivePoint::new(inst, pos)
    }

    fn span(start: u8, end: u8) -> Range<LivePoint<u32>> {
        debug_assert!(start < end);
        point(start)..point(end)
    }

    /// One assignment as the oracle records it: one entry per (unit, span) pair.
    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    struct OracleEntry {
        unit: RegUnit,
        start: LivePoint<u32>,
        end: LivePoint<u32>,
        bundle: LiveBundle<u32>,
    }

    /// Brute-force check whether assigning `spans` to `reg_units` would
    /// conflict.
    fn oracle_conflicts(
        oracle: &[OracleEntry],
        reg_units: &[Range<RegUnit>],
        spans: &[Range<LivePoint<u32>>],
    ) -> bool {
        oracle.iter().any(|existing| {
            reg_units.iter().any(|units| units.contains(&existing.unit))
                && spans.iter().any(|span| {
                    LivePoint::spans_overlap(span.start, span.end, existing.start, existing.end)
                })
        })
    }

    fn oracle_insert(
        oracle: &mut Vec<OracleEntry>,
        bundle: LiveBundle<u32>,
        reg_units: &[Range<RegUnit>],
        spans: &[Range<LivePoint<u32>>],
    ) {
        for index in 0..NUM_UNITS {
            let unit = unit(index);
            if !reg_units.iter().any(|units| units.contains(&unit)) {
                continue;
            }
            for span in spans {
                oracle.push(OracleEntry {
                    unit,
                    start: span.start,
                    end: span.end,
                    bundle,
                });
            }
        }
    }

    /// Brute-force version of `Assignments::try_assign_to_reg` and
    /// `Assignments::try_assign_to_reg_group`.
    ///
    /// Returns the index of the candidate that the bundle was assigned to.
    fn oracle_try_assign(
        oracle: &mut Vec<OracleEntry>,
        bundle: LiveBundle<u32>,
        candidates: &[Vec<Range<RegUnit>>],
        spans: &[Range<LivePoint<u32>>],
    ) -> Option<usize> {
        let index = candidates
            .iter()
            .position(|units| !oracle_conflicts(oracle, units, spans))?;
        oracle_insert(oracle, bundle, &candidates[index], spans);
        Some(index)
    }

    /// The spans that each bundle is currently assigned with, as
    /// `try_evict_*_and_assign` wants them, indexed by bundle.
    ///
    /// The incoming bundle is the one exception: it takes the spans it is being
    /// assigned with now, rather than any it happens to already hold. In the
    /// allocator proper this all comes straight off the bundle, whose spans do
    /// not change while it is assigned.
    fn spans_by_bundle(
        oracle: &[OracleEntry],
        incoming: LiveBundle<u32>,
        incoming_spans: &[Range<LivePoint<u32>>],
    ) -> Vec<Vec<Range<LivePoint<u32>>>> {
        (0..usize::from(NUM_BUNDLES))
            .map(|index| {
                let b = bundle(index);
                if b == incoming {
                    return incoming_spans.to_vec();
                }
                let mut spans: Vec<_> = oracle
                    .iter()
                    .filter(|existing| existing.bundle == b)
                    .map(|existing| existing.start..existing.end)
                    .collect();
                spans.sort_unstable_by_key(|span| (span.start, span.end));
                spans.dedup();
                spans
            })
            .collect()
    }

    /// Brute-force version of `Assignments::try_evict_reg_and_assign` and
    /// `Assignments::try_evict_reg_group_and_assign`.
    ///
    /// `cost` is given the victim and the index of the candidate it would be
    /// evicted from. Returns the bundle that was evicted and the index of the
    /// candidate the incoming bundle took, if any.
    fn oracle_try_evict_and_assign(
        oracle: &mut Vec<OracleEntry>,
        bundle: LiveBundle<u32>,
        candidates: &[Vec<Range<RegUnit>>],
        spans: &[Range<LivePoint<u32>>],
        max_cost: EvictionCost,
        cost: impl Fn(LiveBundle<u32>, usize) -> EvictionCost,
    ) -> Option<(LiveBundle<u32>, usize)> {
        let mut best = None;
        let mut best_cost = max_cost;

        for (index, units) in candidates.iter().enumerate() {
            // The distinct bundles in the way, of which there must be exactly
            // one for a single eviction to make room here.
            let mut conflicting: Vec<LiveBundle<u32>> = oracle
                .iter()
                .filter(|existing| {
                    units.iter().any(|units| units.contains(&existing.unit))
                        && spans.iter().any(|span| {
                            LivePoint::spans_overlap(
                                span.start,
                                span.end,
                                existing.start,
                                existing.end,
                            )
                        })
                })
                .map(|existing| existing.bundle)
                .collect();
            conflicting.sort_unstable();
            conflicting.dedup();

            let [victim] = conflicting[..] else {
                continue;
            };

            let victim_cost = cost(victim, index);
            if victim_cost < best_cost {
                best = Some((victim, index));
                best_cost = victim_cost;
            }
        }

        let (victim, index) = best?;
        oracle.retain(|existing| existing.bundle != victim);
        oracle_insert(oracle, bundle, &candidates[index], spans);
        Some((victim, index))
    }

    /// Check that `assignments` records exactly what `oracle` does.
    fn check_agree(assignments: &Assignments<u32>, oracle: &[OracleEntry]) -> Result<(), String> {
        if assignments.is_reset() != oracle.is_empty() {
            return Err(format!(
                "`is_reset` is {} but the oracle holds {} assignments",
                assignments.is_reset(),
                oracle.len(),
            ));
        }

        // Only the units covered by our test registers are ever written.
        if assignments.assignments.len() > NUM_UNITS {
            return Err(format!(
                "the map has grown to hold {} units, but this test only names {NUM_UNITS}",
                assignments.assignments.len(),
            ));
        }

        // Convert the `Assignments` into our `OracleEntry` representation so we
        // can easily test equality.
        let mut actual = Vec::new();
        for (unit, unit_assignments) in assignments.assignments.iter() {
            for (key, assignment) in unit_assignments {
                actual.push(OracleEntry {
                    unit,
                    start: key.start,
                    end: assignment.end,
                    bundle: assignment.bundle,
                });
            }
        }
        actual.sort_unstable();

        let mut expected = oracle.to_vec();
        expected.sort_unstable();

        if actual != expected {
            return Err(format!(
                "the assignments are {actual:?} but should be {expected:?}"
            ));
        }

        Ok(())
    }

    fn check_no_overlaps(assignments: &Assignments<u32>) -> Result<(), String> {
        for (unit, unit_assignments) in assignments.assignments.iter() {
            let mut previous: Option<Range<LivePoint<u32>>> = None;
            for (key, assignment) in unit_assignments {
                if key.start >= assignment.end {
                    return Err(format!(
                        "{unit:?} holds the empty span {:?}..{:?}",
                        key.start, assignment.end,
                    ));
                }
                if let Some(previous) = &previous
                    && LivePoint::spans_overlap(
                        previous.start,
                        previous.end,
                        key.start,
                        assignment.end,
                    )
                {
                    return Err(format!(
                        "{unit:?} holds the overlapping spans {previous:?} and {:?}..{:?}",
                        key.start, assignment.end,
                    ));
                }
                previous = Some(key.start..assignment.end);
            }
        }
        Ok(())
    }

    /// Every unit set that `conflicts` can be asked about: the registers first,
    /// then the register groups.
    fn probe_unit_sets() -> Vec<Vec<Range<RegUnit>>> {
        (0..NUM_REGS)
            .map(|index| vec![reg_units(reg(u8::try_from(index).unwrap()))])
            .chain(
                (0..NUM_GROUPS)
                    .map(|index| group_units(group(u8::try_from(index).unwrap())).collect()),
            )
            .collect()
    }

    /// Name the `index`th entry of `probe_unit_sets`.
    fn probe_name(index: usize) -> String {
        if index < NUM_REGS {
            format!("{:?}", reg(u8::try_from(index).unwrap()))
        } else {
            format!("{:?}", group(u8::try_from(index - NUM_REGS).unwrap()))
        }
    }

    fn check_conflicts_agree(
        assignments: &Assignments<u32>,
        oracle: &[OracleEntry],
    ) -> Result<(), String> {
        for (index, units) in probe_unit_sets().iter().enumerate() {
            for start in 0..NUM_POINTS {
                for end in start + 1..=NUM_POINTS {
                    let probe = [span(start, end)];
                    let actual =
                        assignments.conflicts(units.iter().cloned(), probe.iter().cloned());
                    let expected = oracle_conflicts(oracle, units, &probe);
                    if actual != expected {
                        return Err(format!(
                            "`conflicts({}, {:?})` is {actual} but should be {expected}",
                            probe_name(index),
                            probe[0],
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    /// A distinct weight per bundle, so that every subset of the bundles has a
    /// distinct, exactly-representable sum and a double-count or an omission
    /// names its own culprit.
    const WEIGHTS: [f32; NUM_BUNDLES as usize] = [1.0, 2.0, 4.0, 8.0];

    /// Brute-force version of `Assignments::interference_weight`.
    fn oracle_interference_weight(
        oracle: &[OracleEntry],
        reg_units: &[Range<RegUnit>],
        spans: &[Range<LivePoint<u32>>],
        weight_of: impl Fn(LiveBundle<u32>) -> f32,
    ) -> f32 {
        let mut conflicting: Vec<LiveBundle<u32>> = oracle
            .iter()
            .filter(|existing| {
                reg_units.iter().any(|units| units.contains(&existing.unit))
                    && spans.iter().any(|span| {
                        LivePoint::spans_overlap(span.start, span.end, existing.start, existing.end)
                    })
            })
            .map(|existing| existing.bundle)
            .collect();
        conflicting.sort_unstable();
        conflicting.dedup();
        conflicting.into_iter().map(weight_of).sum()
    }

    /// The span sets that `interference_weight` is probed with.
    fn probe_span_sets() -> Vec<Vec<Range<LivePoint<u32>>>> {
        vec![
            vec![span(0, 8)],
            vec![span(3, 5)],
            vec![span(2, 3)],
            vec![span(0, 1), span(2, 3)],
            vec![span(0, 1), span(3, 4)],
            vec![span(0, 2), span(4, 6)],
            vec![span(0, 1), span(7, 8)],
            vec![span(1, 2), span(3, 5), span(6, 8)],
            vec![span(0, 4), span(4, 8)],
        ]
    }

    fn check_interference_weight_agrees(
        assignments: &Assignments<u32>,
        oracle: &[OracleEntry],
    ) -> Result<(), String> {
        let scratch = &mut Vec::new();
        let weight_of = |b: LiveBundle<u32>| WEIGHTS[b.index()];
        let span_sets = probe_span_sets();

        for (index, units) in probe_unit_sets().iter().enumerate() {
            let weigh = |spans: &[Range<LivePoint<u32>>],
                         scratch: &mut Vec<LiveBundle<u32>>,
                         weight_of: &dyn Fn(LiveBundle<u32>) -> f32| {
                assignments.interference_weight(
                    units.iter().cloned(),
                    spans.iter().cloned(),
                    scratch,
                    weight_of,
                )
            };

            for spans in &span_sets {
                let actual = weigh(spans, scratch, &weight_of);
                let expected = oracle_interference_weight(oracle, units, spans, weight_of);
                if actual != expected {
                    return Err(format!(
                        "`interference_weight({}, {spans:?})` is {actual} but should be {expected}",
                        probe_name(index),
                    ));
                }
                if !scratch.is_empty() {
                    return Err(format!(
                        "`interference_weight({}, {spans:?})` left {} bundles in the scratch \
                         buffer",
                        probe_name(index),
                        scratch.len(),
                    ));
                }

                // Weighing every bundle 1 counts the distinct bundles in the way,
                // which is zero exactly when nothing is in the way at all. This
                // ties the new method to `conflicts`, which is already under test
                // against an oracle of its own, so the two would have to be wrong
                // together to agree here.
                let count = weigh(spans, scratch, &|_| 1.0);
                let conflicts = assignments.conflicts(units.iter().cloned(), spans.iter().cloned());
                if (count != 0.0) != conflicts {
                    return Err(format!(
                        "`interference_weight({}, {spans:?})` counts {count} bundles in the way, \
                         but `conflicts` is {conflicts}",
                        probe_name(index),
                    ));
                }
            }

            // Two adjacent ranges cover exactly what the single range they tile
            // does, so they must cost exactly what it does: no bundle in the way
            // of both may be charged twice for straddling the seam.
            let split = weigh(&[span(0, 4), span(4, 8)], scratch, &weight_of);
            let whole = weigh(&[span(0, 8)], scratch, &weight_of);
            if split != whole {
                return Err(format!(
                    "`interference_weight({}, ..)` is {split} for two adjacent halves but \
                     {whole} for the single range they tile",
                    probe_name(index),
                ));
            }
        }

        Ok(())
    }

    fn check_try_assign(
        assignments: &Assignments<u32>,
        what: &str,
        candidates: &[Vec<Range<RegUnit>>],
        spans: &[Range<LivePoint<u32>>],
        actual: bool,
        expected: Option<usize>,
    ) -> Result<(), String> {
        if actual != expected.is_some() {
            return Err(match expected {
                Some(index) => format!(
                    "assigning {what} for {spans:?} returned {actual}, but it should have gone \
                     in candidate {index}, which covers {:?}",
                    candidates[index],
                ),
                None => format!(
                    "assigning {what} for {spans:?} returned {actual}, but every candidate is \
                     in conflict",
                ),
            });
        }

        if let Some(index) = expected {
            let units = &candidates[index];
            let no_units = units.iter().all(|units| units.start == units.end);
            let taken = assignments.conflicts(units.iter().cloned(), spans.iter().cloned());
            if taken == no_units {
                return Err(format!(
                    "after assigning {what} for {spans:?}, `conflicts` on candidate {index}, \
                     which covers {units:?}, for those same spans is {taken}",
                ));
            }
        }

        Ok(())
    }

    fn check_try_evict(
        assignments: &Assignments<u32>,
        what: &str,
        candidates: &[Vec<Range<RegUnit>>],
        spans: &[Range<LivePoint<u32>>],
        actual: Option<LiveBundle<u32>>,
        expected: Option<(LiveBundle<u32>, usize)>,
    ) -> Result<(), String> {
        if actual != expected.map(|(victim, _)| victim) {
            return Err(match expected {
                Some((victim, index)) => format!(
                    "evicting to assign {what} for {spans:?} returned {actual:?}, but it should \
                     have evicted {victim:?} from candidate {index}, which covers {:?}",
                    candidates[index],
                ),
                None => format!(
                    "evicting to assign {what} for {spans:?} returned {actual:?}, but no \
                     eviction is both possible and worth it",
                ),
            });
        }

        if let Some((_, index)) = expected {
            let units = &candidates[index];
            let no_units = units.iter().all(|units| units.start == units.end);
            let taken = assignments.conflicts(units.iter().cloned(), spans.iter().cloned());
            if taken == no_units {
                return Err(format!(
                    "after evicting to assign {what} for {spans:?}, `conflicts` on candidate \
                     {index}, which covers {units:?}, for those same spans is {taken}",
                ));
            }
        }

        Ok(())
    }

    #[derive(Clone, Debug, Mutate)]
    enum Op {
        TryAssign {
            bundle: u8,
            candidates: Vec<u8>,
            spans: Vec<(u8, u8)>,
        },
        TryAssignGroup {
            bundle: u8,
            candidates: Vec<u8>,
            spans: Vec<(u8, u8)>,
        },
        TryEvictAndAssign {
            bundle: u8,
            candidates: Vec<u8>,
            spans: Vec<(u8, u8)>,
            /// Each bundle's spill weight, indexed by bundle.
            weights: Vec<u8>,
            /// Each bundle's preferred candidate, indexed by bundle. Evicting a
            /// bundle from the candidate it prefers costs one broken hint. The
            /// one out-of-range value means "no preference".
            hints: Vec<u8>,
        },
        TryEvictGroupAndAssign {
            bundle: u8,
            candidates: Vec<u8>,
            spans: Vec<(u8, u8)>,
            weights: Vec<u8>,
            hints: Vec<u8>,
        },
        Reset,
    }

    impl Default for Op {
        fn default() -> Self {
            Op::TryAssign {
                bundle: 0,
                candidates: Vec::new(),
                spans: Vec::new(),
            }
        }
    }

    /// Ensure that the spans are in-range.
    fn fixup_spans(spans: &mut Vec<(u8, u8)>) {
        spans.truncate(MAX_SPANS);

        for (start, end) in spans.iter_mut() {
            *start %= NUM_POINTS;
            if !(*start < *end && *end <= NUM_POINTS) {
                *end = *start + 1 + (*end % (NUM_POINTS - *start));
            }
        }

        spans.sort_unstable();

        // Remove overlapping spans.
        let mut previous_end = 0;
        spans.retain(|&(start, end)| {
            let keep = start >= previous_end;
            if keep {
                previous_end = end;
            }
            keep
        });

        // Ensure we always have at least one span.
        if spans.is_empty() {
            spans.push((0, 1));
        }
    }

    /// Ensure that the per-bundle cost tables are the right shape and in range.
    ///
    /// Missing weights default to zero, and missing hints to the one value that
    /// is out of range for every candidate, and so names none of them.
    fn fixup_costs(weights: &mut Vec<u8>, hints: &mut Vec<u8>, num_candidates: u8) {
        let num_bundles = usize::from(NUM_BUNDLES);

        weights.truncate(num_bundles);
        weights.resize(num_bundles, 0);

        hints.truncate(num_bundles);
        hints.resize(num_bundles, num_candidates);
        for hint in hints.iter_mut() {
            *hint %= num_candidates + 1;
        }
    }

    /// Ensure that our test ops are valid.
    fn fixup_ops(ops: &mut Vec<Op>) {
        let num_regs = u8::try_from(NUM_REGS).unwrap();
        let num_groups = u8::try_from(NUM_GROUPS).unwrap();
        ops.truncate(MAX_OPS);
        for op in ops.iter_mut() {
            let (bundle, candidates, spans, costs, num_candidates) = match op {
                Op::TryAssign {
                    bundle,
                    candidates,
                    spans,
                } => (bundle, candidates, spans, None, num_regs),
                Op::TryAssignGroup {
                    bundle,
                    candidates,
                    spans,
                } => (bundle, candidates, spans, None, num_groups),
                Op::TryEvictAndAssign {
                    bundle,
                    candidates,
                    spans,
                    weights,
                    hints,
                } => (bundle, candidates, spans, Some((weights, hints)), num_regs),
                Op::TryEvictGroupAndAssign {
                    bundle,
                    candidates,
                    spans,
                    weights,
                    hints,
                } => (
                    bundle,
                    candidates,
                    spans,
                    Some((weights, hints)),
                    num_groups,
                ),
                Op::Reset => continue,
            };
            *bundle %= NUM_BUNDLES;
            candidates.truncate(MAX_CANDIDATES);
            for candidate in candidates.iter_mut() {
                *candidate %= num_candidates;
            }
            fixup_spans(spans);
            if let Some((weights, hints)) = costs {
                fixup_costs(weights, hints, num_candidates);
            }
        }
    }

    fn try_assign(bundle: u8, candidates: &[u8], spans: &[(u8, u8)]) -> Op {
        Op::TryAssign {
            bundle,
            candidates: candidates.to_vec(),
            spans: spans.to_vec(),
        }
    }

    fn try_assign_group(bundle: u8, candidates: &[u8], spans: &[(u8, u8)]) -> Op {
        Op::TryAssignGroup {
            bundle,
            candidates: candidates.to_vec(),
            spans: spans.to_vec(),
        }
    }

    fn try_evict(
        bundle: u8,
        candidates: &[u8],
        spans: &[(u8, u8)],
        weights: &[u8],
        hints: &[u8],
    ) -> Op {
        Op::TryEvictAndAssign {
            bundle,
            candidates: candidates.to_vec(),
            spans: spans.to_vec(),
            weights: weights.to_vec(),
            hints: hints.to_vec(),
        }
    }

    fn try_evict_group(
        bundle: u8,
        candidates: &[u8],
        spans: &[(u8, u8)],
        weights: &[u8],
        hints: &[u8],
    ) -> Op {
        Op::TryEvictGroupAndAssign {
            bundle,
            candidates: candidates.to_vec(),
            spans: spans.to_vec(),
            weights: weights.to_vec(),
            hints: hints.to_vec(),
        }
    }

    fn seeds() -> Vec<Vec<Op>> {
        let mut seeds = vec![
            // An existing assignment that *encloses* the queried span. Because
            // the assignments in a unit are keyed by their start point, this is
            // the one case that a forward range query over `[span.start,
            // span.end)` cannot see: on the register itself, on the two it
            // aliases, and as an assignment that has to fall through to a
            // second candidate.
            vec![
                try_assign(0, &[R4], &[(0, 6)]),
                try_assign(1, &[R4], &[(2, 4)]),
                try_assign(2, &[R0], &[(2, 4)]),
                try_assign(3, &[R1, R2], &[(2, 4)]),
            ],
            // Exact-boundary abutment: `[0, 3)` ends where `[3, 6)` begins, so
            // the two do not conflict and both fit in one unit. This is the
            // case that an over-eager fix to `conflicts` gets wrong. The span
            // that reaches one point further does conflict.
            vec![
                try_assign(0, &[R0], &[(0, 3)]),
                try_assign(1, &[R0], &[(3, 6)]),
                try_assign(2, &[R0], &[(2, 4)]),
            ],
            // The identical span twice: the second attempt conflicts on the
            // same register and on one that aliases it, and succeeds on one
            // whose units are disjoint.
            vec![
                try_assign(0, &[R1], &[(1, 4)]),
                try_assign(1, &[R1], &[(1, 4)]),
                try_assign(2, &[R4], &[(1, 4)]),
                try_assign(3, &[R3], &[(1, 4)]),
            ],
            // Aliasing in the other direction: a wide register first, then the
            // narrow ones it covers and the ones it does not.
            vec![
                try_assign(0, &[R5], &[(0, 6)]),
                try_assign(1, &[R2], &[(0, 6)]),
                try_assign(2, &[R3], &[(0, 6)]),
                try_assign(3, &[R0, R1], &[(0, 6)]),
            ],
            // Spans one program point wide, and their immediate neighbors,
            // which must not conflict with them.
            vec![
                try_assign(0, &[R2], &[(2, 3)]),
                try_assign(1, &[R5], &[(1, 2), (3, 4)]),
                try_assign(2, &[R5], &[(2, 3)]),
            ],
            // A bundle of two spans with a hole between them, which something
            // else can be assigned to, and then a span covering the whole
            // thing, which cannot.
            vec![
                try_assign(0, &[R0], &[(0, 2), (4, 6)]),
                try_assign(1, &[R0], &[(2, 4)]),
                try_assign(2, &[R0], &[(0, 6)]),
            ],
            // Preference order: the first candidate is taken, so the second one
            // wins; and an empty candidate list assigns nothing at all.
            vec![
                try_assign(0, &[R0], &[(0, 6)]),
                try_assign(1, &[R0, R1], &[(0, 6)]),
                try_assign(2, &[R4, R2], &[(0, 6)]),
                try_assign(3, &[], &[(0, 6)]),
            ],
            // The register with no units, which has nothing to conflict with,
            // and so "succeeds" while recording nothing and standing in nobody
            // else's way.
            vec![
                try_assign(0, &[R6], &[(0, 6)]),
                try_assign(1, &[R6], &[(0, 6)]),
                try_assign(2, &[R6, R4], &[(0, 6)]),
            ],
            // Reset and start over: what was taken is free again.
            vec![
                try_assign(0, &[R4], &[(0, 6)]),
                Op::Reset,
                try_assign(0, &[R4], &[(0, 6)]),
            ],
            // A register blocks every group that contains it, but leaves a
            // group whose members are all disjoint from it alone.
            vec![
                try_assign(0, &[R0], &[(0, 6)]),
                try_assign_group(1, &[G0], &[(0, 6)]),
                try_assign_group(2, &[G1], &[(0, 6)]),
            ],
            // And the other way around: a group blocks each of its members and
            // the wide register that covers them, but nothing else.
            vec![
                try_assign_group(0, &[G0], &[(0, 6)]),
                try_assign(1, &[R0], &[(0, 6)]),
                try_assign(2, &[R1], &[(0, 6)]),
                try_assign(3, &[R4], &[(0, 6)]),
                try_assign(0, &[R2], &[(0, 6)]),
            ],
            // Only the *second* member of the group is taken, so the group as a
            // whole is unusable and we fall through to the next candidate.
            vec![
                try_assign(0, &[R1], &[(0, 6)]),
                try_assign_group(1, &[G0, G1], &[(0, 6)]),
            ],
            // Aliasing through the wide registers: r4 covers exactly g0's
            // units, so it blocks g0 and g4, but leaves g1 alone.
            vec![
                try_assign(0, &[R4], &[(0, 6)]),
                try_assign_group(1, &[G0], &[(0, 6)]),
                try_assign_group(2, &[G4], &[(0, 6)]),
                try_assign_group(3, &[G1], &[(0, 6)]),
            ],
            // A group whose members are out of unit order and not adjacent,
            // against the registers it covers and the ones it leaves between
            // them.
            vec![
                try_assign_group(0, &[G3], &[(0, 6)]),
                try_assign(1, &[R0], &[(0, 6)]),
                try_assign(2, &[R3], &[(0, 6)]),
                try_assign_group(3, &[G2], &[(0, 6)]),
            ],
            // A group with a member that covers no units. Unlike the bare
            // register r6, which never conflicts with anything, g5 records r0's
            // unit and so conflicts with itself the second time around.
            vec![
                try_assign_group(0, &[G5], &[(0, 6)]),
                try_assign_group(1, &[G5], &[(0, 6)]),
                try_assign(2, &[R6], &[(0, 6)]),
                try_assign(3, &[R1], &[(0, 6)]),
            ],
            // Exact-boundary abutment, for groups: `[0, 3)` ends where `[3, 6)`
            // begins, so both fit in g0; the span that reaches one point
            // further does conflict.
            vec![
                try_assign_group(0, &[G0], &[(0, 3)]),
                try_assign_group(1, &[G0], &[(3, 6)]),
                try_assign_group(2, &[G0], &[(2, 4)]),
            ],
            // A group assignment that *encloses* the queried span -- the case a
            // forward range query cannot see -- probed on the group itself, on
            // one of its members, and on a group that overlaps it in part.
            vec![
                try_assign_group(0, &[G0], &[(0, 6)]),
                try_assign_group(1, &[G0], &[(2, 4)]),
                try_assign(2, &[R1], &[(2, 4)]),
                try_assign_group(3, &[G2], &[(2, 4)]),
            ],
            // A group bundle with a hole between its spans, which a register
            // can slot into, and then a span covering the whole thing, which
            // cannot.
            vec![
                try_assign_group(0, &[G1], &[(0, 2), (4, 6)]),
                try_assign(1, &[R2], &[(2, 4)]),
                try_assign_group(2, &[G1], &[(0, 6)]),
            ],
            // Preference order for groups: the first candidate is taken, so the
            // second one wins; and an empty candidate list assigns nothing.
            vec![
                try_assign_group(0, &[G0], &[(0, 6)]),
                try_assign_group(1, &[G0, G1], &[(0, 6)]),
                try_assign_group(2, &[], &[(0, 6)]),
                try_assign(3, &[R3], &[(0, 6)]),
            ],
            // A three-member group, and what it does and does not leave free.
            vec![
                try_assign_group(0, &[G6], &[(0, 6)]),
                try_assign(1, &[R3], &[(0, 6)]),
                try_assign_group(2, &[G1], &[(0, 6)]),
                try_assign_group(3, &[G4], &[(0, 6)]),
            ],
            // Two three-member groups.
            vec![
                try_assign_group(0, &[G6, G7], &[(0, 3)]),
                try_assign(1, &[R0, R1, R2, R3], &[(0, 4)]),
                try_assign_group(2, &[G6, G7], &[(3, 6)]),
                try_assign(3, &[R0, R1, R2, R3], &[(4, 6)]),
            ],
            // Reset frees a group's units again, just as it does a register's.
            vec![
                try_assign_group(0, &[G4], &[(0, 6)]),
                try_assign(1, &[R0], &[(0, 6)]),
                Op::Reset,
                try_assign_group(0, &[G4], &[(0, 6)]),
            ],
            // The whole point: a bundle worth more than the one in its way
            // takes the register, and one worth less does not.
            vec![
                try_assign(0, &[R0], &[(0, 6)]),
                try_evict(1, &[R0], &[(0, 6)], &[1, 2], &[]),
            ],
            vec![
                try_assign(0, &[R0], &[(0, 6)]),
                try_evict(1, &[R0], &[(0, 6)], &[3, 2], &[]),
            ],
            // Two bundles are in the way, so evicting either one still leaves
            // the other and this register is no candidate at all, no matter how
            // cheap they both are.
            vec![
                try_assign(0, &[R0], &[(0, 2)]),
                try_assign(1, &[R0], &[(2, 4)]),
                try_evict(2, &[R0], &[(0, 4)], &[1, 1, 5], &[]),
            ],
            // Given a choice, we evict the cheaper of the two victims, even
            // though the more expensive one is in the earlier candidate.
            vec![
                try_assign(0, &[R0], &[(0, 6)]),
                try_assign(1, &[R1], &[(0, 6)]),
                try_evict(2, &[R0, R1], &[(0, 6)], &[3, 1, 5], &[]),
            ],
            // Equally cheap victims go to the earlier candidate.
            vec![
                try_assign(0, &[R0], &[(0, 6)]),
                try_assign(1, &[R1], &[(0, 6)]),
                try_evict(2, &[R1, R0], &[(0, 6)], &[1, 1, 5], &[]),
            ],
            // Broken hints outweigh spill weight: the cheap victim sits in the
            // register it prefers, so we take the expensive one instead.
            vec![
                try_assign(0, &[R0], &[(0, 6)]),
                try_assign(1, &[R1], &[(0, 6)]),
                try_evict(2, &[R0, R1], &[(0, 6)], &[1, 3, 5], &[R0]),
            ],
            // And when breaking a hint is the only option, we do not take it,
            // however light the victim.
            vec![
                try_assign(0, &[R0], &[(0, 6)]),
                try_evict(1, &[R0], &[(0, 6)], &[1, 5], &[R0]),
            ],
            // A hint only counts against the register it actually names, so
            // evicting this bundle from a *different* register is free.
            vec![
                try_assign(0, &[R1], &[(0, 6)]),
                try_evict(1, &[R1], &[(0, 6)], &[1, 2], &[R0]),
            ],
            // The victim holds a wide register, so evicting it has to free
            // every one of its units, not just the one we wanted.
            vec![
                try_assign(0, &[R4], &[(0, 6)]),
                try_evict(1, &[R0], &[(0, 6)], &[1, 2], &[]),
                try_assign(2, &[R1], &[(0, 6)]),
            ],
            // Likewise, evicting a victim has to free every one of its spans,
            // not just the one that was in the way.
            vec![
                try_assign(0, &[R0], &[(0, 2), (4, 6)]),
                try_evict(1, &[R0], &[(1, 3)], &[1, 2], &[]),
                try_assign(2, &[R0], &[(4, 6)]),
            ],
            // A bundle can never evict itself, however the weights fall.
            vec![
                try_assign(0, &[R0], &[(0, 6)]),
                try_evict(0, &[R0], &[(0, 6)], &[1], &[]),
            ],
            // The bundle doing the evicting already holds a register of its
            // own, and keeps it.
            vec![
                try_assign(0, &[R0], &[(0, 6)]),
                try_assign(1, &[R1], &[(0, 6)]),
                try_evict(1, &[R0], &[(0, 6)], &[1, 2], &[]),
            ],
            // A victim can in turn be evicted by the next bundle along.
            vec![
                try_assign(0, &[R0], &[(0, 6)]),
                try_evict(1, &[R0], &[(0, 6)], &[1, 2], &[]),
                try_evict(2, &[R0], &[(0, 6)], &[1, 2, 3], &[]),
            ],
            // Reset after an eviction: everything is free again.
            vec![
                try_assign(0, &[R0], &[(0, 6)]),
                try_evict(1, &[R0], &[(0, 6)], &[1, 2], &[]),
                Op::Reset,
                try_assign(0, &[R0], &[(0, 6)]),
            ],
            // A register in the way of a group, and the group's other member
            // left free.
            vec![
                try_assign(0, &[R1], &[(0, 6)]),
                try_evict_group(1, &[G0], &[(0, 6)], &[1, 2], &[]),
                try_assign(2, &[R2], &[(0, 6)]),
            ],
            // A group victim spanning every unit, evicted for a group that
            // needs only half of them.
            vec![
                try_assign_group(0, &[G4], &[(0, 6)]),
                try_evict_group(1, &[G1], &[(0, 6)], &[1, 2], &[]),
                try_assign(2, &[R0], &[(0, 6)]),
            ],
            // A group victim evicted by a plain register assignment.
            vec![
                try_assign_group(0, &[G0], &[(0, 6)]),
                try_evict(1, &[R0], &[(0, 6)], &[1, 2], &[]),
                try_assign(2, &[R1], &[(0, 6)]),
            ],
            // Two different bundles in one group's way, so no single eviction
            // frees it, but each of them alone frees a group of its own.
            vec![
                try_assign(0, &[R0], &[(0, 6)]),
                try_assign(1, &[R1], &[(0, 6)]),
                try_evict_group(2, &[G0], &[(0, 6)], &[1, 1, 5], &[]),
                try_evict_group(3, &[G2], &[(0, 6)], &[1, 1, 5, 5], &[]),
            ],
            // Broken hints for groups: the cheap victim prefers the first
            // group, so the expensive one in the second group goes instead.
            vec![
                try_assign_group(0, &[G0], &[(0, 6)]),
                try_assign_group(1, &[G1], &[(0, 6)]),
                try_evict_group(2, &[G0, G1], &[(0, 6)], &[1, 3, 5], &[G0]),
            ],
        ];
        for ops in seeds.iter_mut() {
            fixup_ops(ops);
        }
        seeds
    }

    #[test]
    fn assignments_properties() -> CheckResult<Vec<Op>> {
        let mutator = m::default::<Vec<Op>>().map(|_ctx, ops| {
            fixup_ops(ops);
            Ok(())
        });

        Check::new().iters(10_000).run_with(
            mutator,
            seeds(),
            |ops: &Vec<Op>| -> Result<(), String> {
                let mut assignments = Assignments::<u32>::new();
                let mut oracle = Vec::new();

                if !assignments.is_reset() {
                    return Err("new assignments are not reset".to_string());
                }
                check_agree(&assignments, &oracle)?;
                check_conflicts_agree(&assignments, &oracle)?;

                for op in ops {
                    match op {
                        Op::TryAssign {
                            bundle: b,
                            candidates,
                            spans,
                        } => {
                            let b = bundle(usize::from(*b));
                            let candidates: Vec<Reg> =
                                candidates.iter().map(|&index| reg(index)).collect();
                            let spans: Vec<Range<LivePoint<u32>>> =
                                spans.iter().map(|&(start, end)| span(start, end)).collect();
                            let units: Vec<Vec<Range<RegUnit>>> =
                                candidates.iter().map(|&r| vec![reg_units(r)]).collect();

                            let expected = oracle_try_assign(&mut oracle, b, &units, &spans);
                            let actual = assignments.try_assign_to_reg(
                                b,
                                candidates.iter().copied(),
                                reg_units,
                                spans.iter().cloned(),
                            );
                            check_try_assign(
                                &assignments,
                                &format!("{b:?} to one of {candidates:?}"),
                                &units,
                                &spans,
                                actual,
                                expected,
                            )?;
                        }

                        Op::TryAssignGroup {
                            bundle: b,
                            candidates,
                            spans,
                        } => {
                            let b = bundle(usize::from(*b));
                            let candidates: Vec<RegGroup> =
                                candidates.iter().map(|&index| group(index)).collect();
                            let spans: Vec<Range<LivePoint<u32>>> =
                                spans.iter().map(|&(start, end)| span(start, end)).collect();
                            let units: Vec<Vec<Range<RegUnit>>> = candidates
                                .iter()
                                .map(|&g| group_units(g).collect())
                                .collect();

                            let expected = oracle_try_assign(&mut oracle, b, &units, &spans);
                            let actual = assignments.try_assign_to_reg_group(
                                b,
                                candidates.iter().copied(),
                                group_units,
                                spans.iter().cloned(),
                            );
                            check_try_assign(
                                &assignments,
                                &format!("{b:?} to one of {candidates:?}"),
                                &units,
                                &spans,
                                actual,
                                expected,
                            )?;
                        }

                        Op::TryEvictAndAssign {
                            bundle: b,
                            candidates,
                            spans,
                            weights,
                            hints,
                        } => {
                            let b = bundle(usize::from(*b));
                            let spans: Vec<Range<LivePoint<u32>>> =
                                spans.iter().map(|&(start, end)| span(start, end)).collect();

                            // Every candidate must already be in conflict, so
                            // filter out the ones that are not: this method is
                            // only ever reached once plain assignment has
                            // failed everywhere.
                            let candidates: Vec<Reg> = candidates
                                .iter()
                                .map(|&index| reg(index))
                                .filter(|&r| oracle_conflicts(&oracle, &[reg_units(r)], &spans))
                                .collect();
                            let units: Vec<Vec<Range<RegUnit>>> =
                                candidates.iter().map(|&r| vec![reg_units(r)]).collect();

                            let spans_of = spans_by_bundle(&oracle, b, &spans);
                            let bundle_spans =
                                |bb: LiveBundle<u32>| spans_of[bb.index()].iter().cloned();

                            let cost = |victim: LiveBundle<u32>, r: Reg| {
                                let broken_hints =
                                    usize::from(usize::from(hints[victim.index()]) == r.index());
                                EvictionCost::new(
                                    broken_hints,
                                    SpillWeight::new(f32::from(weights[victim.index()])),
                                )
                            };
                            let max_cost = EvictionCost::new(
                                0,
                                SpillWeight::new(f32::from(weights[b.index()])),
                            );

                            let expected = oracle_try_evict_and_assign(
                                &mut oracle,
                                b,
                                &units,
                                &spans,
                                max_cost,
                                |victim, index| cost(victim, candidates[index]),
                            );
                            let actual = assignments.try_evict_reg_and_assign(
                                b,
                                candidates.iter().copied(),
                                reg_units,
                                max_cost,
                                cost,
                                bundle_spans,
                            );
                            check_try_evict(
                                &assignments,
                                &format!("{b:?} to one of {candidates:?}"),
                                &units,
                                &spans,
                                actual,
                                expected,
                            )?;
                        }

                        Op::TryEvictGroupAndAssign {
                            bundle: b,
                            candidates,
                            spans,
                            weights,
                            hints,
                        } => {
                            let b = bundle(usize::from(*b));
                            let spans: Vec<Range<LivePoint<u32>>> =
                                spans.iter().map(|&(start, end)| span(start, end)).collect();

                            let candidates: Vec<RegGroup> = candidates
                                .iter()
                                .map(|&index| group(index))
                                .filter(|&g| {
                                    let units: Vec<_> = group_units(g).collect();
                                    oracle_conflicts(&oracle, &units, &spans)
                                })
                                .collect();
                            let units: Vec<Vec<Range<RegUnit>>> = candidates
                                .iter()
                                .map(|&g| group_units(g).collect())
                                .collect();

                            let spans_of = spans_by_bundle(&oracle, b, &spans);
                            let bundle_spans =
                                |bb: LiveBundle<u32>| spans_of[bb.index()].iter().cloned();

                            let cost = |victim: LiveBundle<u32>, g: RegGroup| {
                                let broken_hints =
                                    usize::from(usize::from(hints[victim.index()]) == g.index());
                                EvictionCost::new(
                                    broken_hints,
                                    SpillWeight::new(f32::from(weights[victim.index()])),
                                )
                            };
                            let max_cost = EvictionCost::new(
                                0,
                                SpillWeight::new(f32::from(weights[b.index()])),
                            );

                            let expected = oracle_try_evict_and_assign(
                                &mut oracle,
                                b,
                                &units,
                                &spans,
                                max_cost,
                                |victim, index| cost(victim, candidates[index]),
                            );
                            let actual = assignments.try_evict_reg_group_and_assign(
                                b,
                                candidates.iter().copied(),
                                group_units,
                                max_cost,
                                cost,
                                bundle_spans,
                            );
                            check_try_evict(
                                &assignments,
                                &format!("{b:?} to one of {candidates:?}"),
                                &units,
                                &spans,
                                actual,
                                expected,
                            )?;
                        }

                        Op::Reset => {
                            assignments.reset();
                            oracle.clear();
                            if !assignments.is_reset() {
                                return Err(
                                    "the assignments are not reset after `reset`".to_string()
                                );
                            }
                        }
                    }

                    check_agree(&assignments, &oracle)?;
                    check_no_overlaps(&assignments)?;
                    check_conflicts_agree(&assignments, &oracle)?;
                    check_interference_weight_agrees(&assignments, &oracle)?;
                }

                Ok(())
            },
        )
    }
}
