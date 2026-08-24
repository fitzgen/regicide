//! The set of assignments of live bundles to register units.

use crate::{
    Entity, Reg, RegUnit,
    entity::{EntityRepr, SecondaryMap},
    live_ranges::{LiveBundle, LivePoint},
};
use alloc::collections::BTreeMap;
use core::ops::Range;

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
    #[allow(dead_code, reason = "will use it soon")]
    end: LivePoint<E>,

    /// The bundle that this assignment came from.
    #[allow(dead_code, reason = "will use it soon")]
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

fn iter_reg_units(reg_units: Range<RegUnit>) -> impl ExactSizeIterator<Item = RegUnit> {
    debug_assert!(reg_units.start <= reg_units.end);
    (reg_units.start.to_bits()..reg_units.end.to_bits()).map(|i| RegUnit::from_bits(i))
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

    /// Do the given spans conflict with any existing assignments in `reg_units`?
    fn conflicts(
        &self,
        reg_units: Range<RegUnit>,
        spans: impl ExactSizeIterator<Item = Range<LivePoint<E>>> + Clone,
    ) -> bool {
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
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Insert a new assignment.
    ///
    /// The new assignment's spans must not conflict with any existing
    /// assignment.
    fn insert_assignment(
        &mut self,
        bundle: LiveBundle<E>,
        reg_units: Range<RegUnit>,
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
            if !self.conflicts(reg_units(reg), spans.clone()) {
                self.insert_assignment(bundle, reg_units(reg), spans);
                return true;
            }
        }

        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Inst, Position};
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

    const MAX_OPS: usize = 12;
    const MAX_CANDIDATES: usize = 3;
    const MAX_SPANS: usize = 3;
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
        reg_units: Range<RegUnit>,
        spans: &[Range<LivePoint<u32>>],
    ) -> bool {
        oracle.iter().any(|existing| {
            reg_units.contains(&existing.unit)
                && spans.iter().any(|span| {
                    LivePoint::spans_overlap(span.start, span.end, existing.start, existing.end)
                })
        })
    }

    fn oracle_insert(
        oracle: &mut Vec<OracleEntry>,
        bundle: LiveBundle<u32>,
        reg_units: Range<RegUnit>,
        spans: &[Range<LivePoint<u32>>],
    ) {
        for index in 0..NUM_UNITS {
            let unit = unit(index);
            if !reg_units.contains(&unit) {
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

    /// Brute-force version of `Assignments::try_assign_to_reg`.
    ///
    /// Returns the register that the bundle was assigned to.
    fn oracle_try_assign(
        oracle: &mut Vec<OracleEntry>,
        bundle: LiveBundle<u32>,
        candidates: &[Reg],
        spans: &[Range<LivePoint<u32>>],
    ) -> Option<Reg> {
        let reg = *candidates
            .iter()
            .find(|&&reg| !oracle_conflicts(oracle, reg_units(reg), spans))?;
        oracle_insert(oracle, bundle, reg_units(reg), spans);
        Some(reg)
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

    fn check_conflicts_agree(
        assignments: &Assignments<u32>,
        oracle: &[OracleEntry],
    ) -> Result<(), String> {
        for index in 0..NUM_REGS {
            let reg = reg(u8::try_from(index).unwrap());
            let units = reg_units(reg);
            for start in 0..NUM_POINTS {
                for end in start + 1..=NUM_POINTS {
                    let probe = [span(start, end)];
                    let actual = assignments.conflicts(units.clone(), probe.iter().cloned());
                    let expected = oracle_conflicts(oracle, units.clone(), &probe);
                    if actual != expected {
                        return Err(format!(
                            "`conflicts({reg:?}, {:?})` is {actual} but should be {expected}",
                            probe[0],
                        ));
                    }
                }
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
            *end = *start + 1 + (*end % (NUM_POINTS - *start));
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

    /// Ensure that our test ops are valid.
    fn fixup_ops(ops: &mut Vec<Op>) {
        let num_regs = u8::try_from(NUM_REGS).unwrap();
        ops.truncate(MAX_OPS);
        for op in ops.iter_mut() {
            match op {
                Op::TryAssign {
                    bundle,
                    candidates,
                    spans,
                } => {
                    *bundle %= NUM_BUNDLES;
                    candidates.truncate(MAX_CANDIDATES);
                    for candidate in candidates.iter_mut() {
                        *candidate %= num_regs;
                    }
                    fixup_spans(spans);
                }
                Op::Reset => {}
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

                            let expected = oracle_try_assign(&mut oracle, b, &candidates, &spans);
                            let actual = assignments.try_assign_to_reg(
                                b,
                                candidates.iter().copied(),
                                reg_units,
                                spans.iter().cloned(),
                            );
                            if actual != expected.is_some() {
                                return Err(match expected {
                                    Some(reg) => format!(
                                        "assigning {b:?} to one of {candidates:?} for {spans:?} \
                                         returned {actual}, but it should have gone in {reg:?}",
                                    ),
                                    None => format!(
                                        "assigning {b:?} to one of {candidates:?} for {spans:?} \
                                         returned {actual}, but every candidate is in conflict",
                                    ),
                                });
                            }

                            // Those spans are taken now, so asking about them
                            // again reports a conflict -- unless the register
                            // covers no units, in which case there was nothing
                            // to take and nothing ever conflicts with it.
                            if let Some(reg) = expected {
                                let units = reg_units(reg);
                                let taken =
                                    assignments.conflicts(units.clone(), spans.iter().cloned());
                                if taken == units.is_empty() {
                                    return Err(format!(
                                        "after assigning {b:?} to {reg:?} for {spans:?}, \
                                         `conflicts` on {reg:?} for those same spans is {taken}",
                                    ));
                                }
                            }
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
                }

                Ok(())
            },
        )
    }
}
