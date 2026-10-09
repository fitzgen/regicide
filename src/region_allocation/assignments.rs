//! The set of assignments of live bundles to register units.

use crate::{
    Entity, Reg, RegGroup, RegUnit, Val,
    entity::{EntityRange, EntityRepr, PrimaryMap, SecondaryMap},
    live_ranges::{LiveBundle, LivePoint},
    output::RegAllocation,
    region_allocation::{EvictionCost, splitting::HalfSpan},
};
use alloc::vec::Vec;
use core::{iter, ops::ControlFlow, ops::Range};

/// A span offered to the matrix, together with which reservations it may see
/// through.
///
/// A reservation holds one register for one value, so that value's own span
/// may sit underneath it and no other may.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct QuerySpan<E>
where
    E: EntityRepr,
{
    /// The value this span carries, when a reservation held for that value is
    /// one this span may share a register with.
    porous_to: Option<Val<E>>,

    /// The range of the span itself.
    range: Range<LivePoint<E>>,
}

impl<E> QuerySpan<E>
where
    E: EntityRepr,
{
    /// A span carrying `val`, which may share a register with a reservation
    /// holding that register for `val`.
    pub(crate) fn porous_to(val: Val<E>, range: Range<LivePoint<E>>) -> Self {
        QuerySpan {
            porous_to: Some(val),
            range,
        }
    }

    /// A span that may share a register with no reservation at all, which is
    /// what a question about a bare register wants.
    pub(crate) fn sees_all_reservations(range: Range<LivePoint<E>>) -> Self {
        QuerySpan {
            porous_to: None,
            range,
        }
    }

    /// The value a reservation must be held for to be porous to this span, if
    /// any.
    pub(crate) fn val(&self) -> Option<Val<E>> {
        self.porous_to
    }

    /// The range this span covers.
    pub(crate) fn range(&self) -> Range<LivePoint<E>> {
        self.range.clone()
    }
}

/// The key by which a register unit's assignments are ordered.
///
/// The spans inside one `RegUnitAssignments` can never overlap, as that would
/// represent a conflicting assignment, so we key by just the spans' start
/// points.
///
/// Reservations are the same, in a map of their own: a reservation may overlap
/// an assignment, but never another reservation.
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
type RegUnitAssignments<E> = UnitMap<E, Assignment<E>>;

/// One register unit's entries, sorted by key.
#[derive(Clone, Debug)]
struct UnitMap<E, V>
where
    E: EntityRepr,
{
    /// A sorted vector rather than a B-tree: splitting and eviction search
    /// these far more often than anything changes them.
    entries: Vec<(AssignmentKey<E>, V)>,
}

impl<E, V> UnitMap<E, V>
where
    E: EntityRepr,
{
    const fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Where `key` is, or would go.
    fn search(&self, key: AssignmentKey<E>) -> Result<usize, usize> {
        self.entries.binary_search_by_key(&key, |(k, _)| *k)
    }

    /// The entries whose keys are before `end`.
    fn before(&self, end: AssignmentKey<E>) -> &[(AssignmentKey<E>, V)] {
        let i = self.entries.partition_point(|(k, _)| *k < end);
        &self.entries[..i]
    }

    fn get(&self, key: AssignmentKey<E>) -> Option<&V> {
        let i = self.search(key).ok()?;
        Some(&self.entries[i].1)
    }

    fn remove(&mut self, key: AssignmentKey<E>) {
        if let Ok(i) = self.search(key) {
            self.entries.remove(i);
        }
    }

    /// Insert `value` at `key`, which must not be in the map yet.
    fn insert(&mut self, key: AssignmentKey<E>, value: V) {
        match self.search(key) {
            Ok(_) => debug_assert!(false, "{key:?} is already in the map"),
            Err(i) => self.entries.insert(i, (key, value)),
        }
    }

    /// Add all of `other`'s entries, none of whose keys may be in `self`.
    fn merge(&mut self, other: &Self)
    where
        V: Clone,
    {
        // Merge from the back, into the room the copies of `other` make.
        let mut i = self.entries.len();
        self.entries.extend(other.entries.iter().cloned());
        for (j, theirs) in other.entries.iter().enumerate().rev() {
            while i > 0 && self.entries[i - 1].0 > theirs.0 {
                self.entries.swap(i - 1, i + j);
                i -= 1;
            }
            self.entries[i + j] = theirs.clone();
        }
        debug_assert!(self.entries.windows(2).all(|w| w[0].0 < w[1].0));
    }
}

impl<'a, E, V> IntoIterator for &'a UnitMap<E, V>
where
    E: EntityRepr,
{
    type Item = &'a (AssignmentKey<E>, V);
    type IntoIter = core::slice::Iter<'a, (AssignmentKey<E>, V)>;

    fn into_iter(self) -> Self::IntoIter {
        self.entries.iter()
    }
}

/// A register unit held for a fixed operand.
///
/// Rather than let the value's bundle compete for the register the operand
/// names, we take it out of circulation for the half-instruction the operand
/// owns and move-connect the value to it.
///
/// Reservations are never evicted and never removed: no amount of splitting or
/// spilling can change where a fixed operand must live.
#[derive(Clone, Debug)]
struct ReservationEntry<E>
where
    E: EntityRepr,
{
    /// The end of the reserved range, whose start is `AssignmentKey::start`.
    end: LivePoint<E>,

    /// What occupies these units over the reserved range.
    held: RegAllocation<E>,

    /// Who this reservation is for, if any.
    ///
    /// This is the only value part that this reservation may share its
    /// associated unit with.
    porous_to: Option<PorousTo<E>>,
}

/// What a reservation may share one of its register units with.
///
/// Sharing takes the same *piece* of the same value in the same place: a span
/// assigned the group `(r0, r2)` may not sit under a reservation of `(r1, r0)`
/// even for its own value, since each wants a different piece of it in `r0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct PorousTo<E>
where
    E: EntityRepr,
{
    /// The value the reservation holds the register for.
    val: Val<E>,

    /// Which piece of `val` belongs in this unit: the index of the member of
    /// the reserved register group that covers it, and zero for a plain
    /// register.
    ///
    /// Comparing indices is enough to compare pieces: both allocations hold
    /// the same value, so both draw on one register bank, whose registers have
    /// disjoint units.
    member: usize,
}

/// A map of all the reservations on a register unit.
type RegUnitReservations<E> = UnitMap<E, ReservationEntry<E>>;

/// A conflict at a register unit over a span.
enum Conflict<'a, E>
where
    E: EntityRepr,
{
    /// A bundle's assignment, which can be evicted or split around.
    Assignment(&'a Assignment<E>),

    /// A register held for a fixed operand, which can be neither, and what it
    /// holds.
    Reservation(RegAllocation<E>),
}

/// The entity occupying a register unit over a span.
pub(crate) enum Occupant<E>
where
    E: EntityRepr,
{
    /// A bundle assigned here.
    Bundle(LiveBundle<E>),

    /// A fixed-register operand reservation.
    Reserved(RegAllocation<E>),
}

pub struct Assignments<E>
where
    E: EntityRepr,
{
    assignments: SecondaryMap<RegUnit, RegUnitAssignments<E>>,
    reservations: SecondaryMap<RegUnit, RegUnitReservations<E>>,
}

/// The total weight of the distinct bundles in `bundles`, which is left empty.
///
/// Summing in sorted order makes the total independent of the order the
/// bundles were found in.
fn sum_distinct<E>(
    bundles: &mut Vec<LiveBundle<E>>,
    weight_of: impl Fn(LiveBundle<E>) -> f32,
) -> f32
where
    E: EntityRepr,
{
    bundles.sort_unstable();
    bundles.dedup();
    let weight = bundles.iter().copied().map(weight_of).sum();
    bundles.clear();
    weight
}

define_entities! {
    /// A span of the bundle being split, by its position in program order.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct SplitSpan = "split_span";

    /// One of the registers or register groups a split is choosing among, in
    /// the order the splitting kernel offers them.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub(crate) struct SplitCandidate = "split_candidate";

    /// A slot in the arena of bundles found in the way of split spans.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct InterferenceStorageIndex = "interference_storage_index";
}

/// What is in the way of each of a bundle's spans in each of its candidates.
///
/// Splitting prices both halves of every cut it considers, and each span lies
/// in many of those halves. Querying each span at most once per candidate makes
/// that linearly many queries in the number of spans, not quadratically.
pub struct SpanInterference<E>
where
    E: EntityRepr,
{
    /// The spans being split.
    spans: PrimaryMap<SplitSpan, QuerySpan<E>>,

    /// Where each candidate's row starts in `prefix`, once that candidate has
    /// been asked about.
    rows: SecondaryMap<SplitCandidate, Option<usize>>,

    /// A row of `spans.len() + 1` entries per candidate asked about. Entry `i`
    /// of a row is where span `i`'s conflicts start in `bundles`, and how many
    /// of the spans before `i` count as reserved.
    ///
    /// A row's spans' conflicts are contiguous and in span order, so any run of
    /// spans' conflicts is one slice of `bundles`.
    prefix: Vec<(usize, usize)>,

    bundles: PrimaryMap<InterferenceStorageIndex, LiveBundle<E>>,

    /// Where the run of equal entries of `bundles` holding each entry starts,
    /// once `fill_row` has filled in that entry's row.
    run_starts: SecondaryMap<InterferenceStorageIndex, Option<usize>>,
}

impl<E> SpanInterference<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        Self {
            spans: PrimaryMap::new(),
            rows: SecondaryMap::new(None),
            prefix: Vec::new(),
            bundles: PrimaryMap::new(),
            run_starts: SecondaryMap::new(None),
        }
    }

    /// Start over with the spans of a new bundle.
    pub fn reset(&mut self, spans: impl IntoIterator<Item = QuerySpan<E>>) {
        self.clear();
        self.spans.extend(spans);
    }

    pub fn clear(&mut self) {
        self.spans.reset();
        self.rows.reset();
        self.prefix.clear();
        self.bundles.reset();
        self.run_starts.reset();
    }

    pub fn is_empty(&self) -> bool {
        self.spans.is_reset()
            && self.rows.is_reset()
            && self.prefix.is_empty()
            && self.bundles.is_reset()
            && self.run_starts.is_reset()
    }

    /// The one bundle filling `range` of `bundles`, `Some(None)` when that is
    /// empty, and `None` when it holds two or more distinct bundles.
    fn sole(&self, range: EntityRange<InterferenceStorageIndex>) -> Option<Option<LiveBundle<E>>> {
        // Not `range.len()`, which spends a branch on `EntityRange::empty`; a
        // range built from `prefix` is never that sentinel.
        let (start, end) = (range.start.index(), range.end.index());
        match end - start {
            0 => Some(None),
            _ => {
                let last = InterferenceStorageIndex::new_unchecked(end - 1);
                (self.run_starts[last].unwrap() <= start).then(|| Some(self.bundles[range.start]))
            }
        }
    }

    /// Push the bundles in the way of `span` in `units` onto `bundles`, and
    /// an entry for it onto `prefix` holding how many there are and whether a
    /// reservation is in its way.
    fn query(
        &mut self,
        assignments: &Assignments<E>,
        units: impl Iterator<Item = Range<RegUnit>>,
        span: SplitSpan,
    ) -> bool {
        let start = self.bundles.next_key_unwrap();
        let clear = assignments.push_interfering(
            units,
            iter::once(self.spans[span].clone()),
            &mut self.bundles,
        );
        if !clear {
            self.bundles.truncate(start);
        }
        self.prefix
            .push((self.bundles.len() - start.index(), usize::from(!clear)));
        clear
    }

    /// `candidate`'s row of `prefix`, querying its spans in `units` the first
    /// time it is asked about.
    #[inline]
    fn row(
        &mut self,
        assignments: &Assignments<E>,
        candidate: SplitCandidate,
        units: impl Iterator<Item = Range<RegUnit>> + Clone,
    ) -> Range<usize> {
        let row = match self.rows[candidate] {
            Some(row) => row,
            None => self.fill_row(assignments, candidate, units),
        };
        row..row + self.spans.len() + 1
    }

    /// Query `candidate`'s spans in `units` into a new row of `prefix`, and
    /// return where it starts.
    #[cold]
    #[inline(never)]
    fn fill_row(
        &mut self,
        assignments: &Assignments<E>,
        candidate: SplitCandidate,
        units: impl Iterator<Item = Range<RegUnit>> + Clone,
    ) -> usize {
        let n = self.spans.len();
        let row = self.prefix.len();
        self.rows[candidate] = Some(row);
        // Everything this row pushes, truncates or reverses is at or after
        // here, and `run_starts` has nothing there yet.
        let row_bundles = self.bundles.next_key_unwrap();

        // Each entry first holds a span's count of conflicts and whether it is
        // reserved, and becomes running totals at the end.
        //
        // A half holds every span on its side of the cut, so one holding a span
        // between the first and last reserved ones holds one of those too, and
        // is infinite whatever else is in its way. Those spans are not queried,
        // and count as reserved.
        let mut first = None;
        for i in 0..n {
            let span = SplitSpan::new_unchecked(i);
            if !self.query(assignments, units.clone(), span) {
                first = Some(span);
                break;
            }
        }
        if let Some(first) = first {
            let tail = self.prefix.len();
            let back = self.bundles.next_key_unwrap();
            for i in (first.index() + 1..n).rev() {
                if !self.query(assignments, units.clone(), SplitSpan::new_unchecked(i)) {
                    break;
                }
            }
            // That walk went backwards; put it in span order, after the skipped
            // spans. Each span's own conflicts may stay reversed.
            let walked = self.prefix.len() - tail;
            let skipped = row + n - self.prefix.len();
            self.prefix.resize(row + n, (0, 1));
            self.prefix[tail..].rotate_left(walked);
            self.prefix[tail + skipped..].reverse();
            self.bundles
                .slice_mut(EntityRange {
                    start: back,
                    end: self.bundles.next_key_unwrap(),
                })
                .reverse();
        }
        debug_assert_eq!(self.prefix.len(), row + n);

        let (mut start, mut reserved) = (self.bundles.len(), 0);
        for (len, _) in &self.prefix[row..] {
            start -= len;
        }
        for entry in &mut self.prefix[row..] {
            let (len, is_reserved) = *entry;
            *entry = (start, reserved);
            start += len;
            reserved += is_reserved;
        }
        self.prefix.push((start, reserved));

        let pushed = EntityRange {
            start: row_bundles,
            end: self.bundles.next_key_unwrap(),
        };
        for i in pushed {
            // A run may reach back into the previous row, which `sole` allows.
            let start = match i.index().checked_sub(1) {
                Some(prev) if self.bundles.as_slice()[prev] == self.bundles[i] => {
                    self.run_starts[InterferenceStorageIndex::new_unchecked(prev)].unwrap()
                }
                _ => i.index(),
            };
            self.run_starts[i] = Some(start);
        }
        // Each row fills in its entries contiguously, so the last one stands for
        // all of them.
        debug_assert!(
            self.bundles
                .keys()
                .next_back()
                .is_none_or(|last| self.run_starts[last].is_some())
        );
        row
    }

    /// The same as `Assignments::interference_weight` for `half` in
    /// `candidate`, whose units are `units`.
    ///
    /// `half` must be carved from the spans given to `reset`. Its divided span
    /// is queried afresh when the cut changed it.
    pub fn weight(
        &mut self,
        assignments: &Assignments<E>,
        candidate: SplitCandidate,
        units: impl Iterator<Item = Range<RegUnit>> + Clone,
        half: HalfSpan<'_, E>,
        scratch: &mut Vec<LiveBundle<E>>,
        weight_of: impl Fn(LiveBundle<E>) -> f32,
    ) -> f32 {
        debug_assert!(scratch.is_empty());

        let row = self.row(assignments, candidate, units.clone());
        let prefix = &self.prefix[row];
        let whole = half.whole_indices();
        let (index, range) = half.clipped();

        // When the divided span is intact, the half is a run of undivided spans,
        // whose conflicts are one slice of `bundles`.
        let intact = half.is_intact();
        let spans = if intact {
            whole.start.min(index)..whole.end.max(index + 1)
        } else {
            whole
        };
        let (start, reserved_before) = prefix[spans.start];
        let (end, reserved_after) = prefix[spans.end];
        let conflicts = EntityRange {
            start: InterferenceStorageIndex::new_unchecked(start),
            end: InterferenceStorageIndex::new_unchecked(end),
        };
        if reserved_before != reserved_after
            || !intact
                && !assignments.push_interfering(
                    units,
                    iter::once(QuerySpan {
                        porous_to: self.spans[SplitSpan::new_unchecked(index)].porous_to,
                        range,
                    }),
                    scratch,
                )
        {
            scratch.clear();
            return f32::INFINITY;
        }

        // Usually one bundle, at most, is in the way of the whole half, which
        // needs neither the copy nor the sort.
        if let Some(sole) = self.sole(conflicts) {
            let mut fresh = scratch.iter().copied();
            let sole = sole.or_else(|| fresh.next());
            if fresh.all(|b| Some(b) == sole) {
                scratch.clear();
                return sole.into_iter().map(weight_of).sum();
            }
        }

        // One entry per run of equal bundles is enough for the sum.
        let mut end = conflicts.end.index();
        while end > conflicts.start.index() {
            let last = InterferenceStorageIndex::new_unchecked(end - 1);
            scratch.push(self.bundles[last]);
            end = self.run_starts[last].unwrap();
        }
        sum_distinct(scratch, weight_of)
    }
}

/// The units one register covers.
fn units_in(units: Range<RegUnit>) -> impl Iterator<Item = RegUnit> {
    debug_assert!(units.start <= units.end);
    (units.start.to_bits()..units.end.to_bits()).map(|i| RegUnit::from_bits(i))
}

fn iter_reg_units(
    reg_units: impl Iterator<Item = Range<RegUnit>>,
) -> impl Iterator<Item = RegUnit> {
    reg_units.flat_map(units_in)
}

impl<E> Assignments<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        Self {
            assignments: SecondaryMap::new(RegUnitAssignments::new()),
            reservations: SecondaryMap::new(RegUnitReservations::new()),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            assignments,
            reservations,
        } = self;
        assignments.reset();
        reservations.reset();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            assignments,
            reservations,
        } = self;
        assignments.is_reset() && reservations.is_reset()
    }

    /// Iterate over the existing assignments in `unit` that overlap `span`.
    fn overlapping(
        &self,
        unit: RegUnit,
        span: Range<LivePoint<E>>,
    ) -> impl Iterator<Item = &Assignment<E>> {
        let (start, end) = (span.start, span.end);
        self.assignments[unit]
            .before(AssignmentKey::new(end))
            .iter()
            .rev()
            .take_while(move |(_, existing)| start < existing.end)
            .filter(move |(existing_key, existing)| {
                LivePoint::spans_overlap(start, end, existing_key.start, existing.end)
            })
            .map(|(_, existing)| existing)
    }

    /// Iterate over the reservations on `unit` that overlap `span`.
    fn overlapping_reservations(
        &self,
        unit: RegUnit,
        span: Range<LivePoint<E>>,
    ) -> impl Iterator<Item = &ReservationEntry<E>> {
        let (start, end) = (span.start, span.end);
        self.reservations[unit]
            .before(AssignmentKey::new(end))
            .iter()
            .rev()
            .take_while(move |(_, existing)| start < existing.end)
            .filter(move |(existing_key, existing)| {
                LivePoint::spans_overlap(start, end, existing_key.start, existing.end)
            })
            .map(|(_, existing)| existing)
    }

    /// Call `f` on everything already occupying one of `reg_units` over one of
    /// the given spans.
    ///
    /// A reservation the querying span's value may share is skipped; see
    /// `ReservationEntry::porous_to`.
    ///
    /// `reg_units` is one candidate allocation's units member by member, since
    /// which member a unit belongs to is part of the porosity question.
    fn for_each_overlapping<T>(
        &self,
        reg_units: impl Iterator<Item = Range<RegUnit>>,
        spans: impl ExactSizeIterator<Item = QuerySpan<E>> + Clone,
        mut f: impl FnMut(Conflict<'_, E>) -> ControlFlow<T>,
    ) -> Option<T> {
        for (member, units) in reg_units.enumerate() {
            for unit in units_in(units) {
                for span in spans.clone() {
                    let val = span.val();
                    let range = span.range();
                    let porous_to = val.map(|val| PorousTo { val, member });
                    for existing in self.overlapping_reservations(unit, range.clone()) {
                        if porous_to.is_some() && existing.porous_to == porous_to {
                            continue;
                        }
                        if let ControlFlow::Break(result) = f(Conflict::Reservation(existing.held))
                        {
                            return Some(result);
                        }
                    }
                    for existing in self.overlapping(unit, range) {
                        if let ControlFlow::Break(result) = f(Conflict::Assignment(existing)) {
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
    ///
    /// A reservation cannot be evicted at any price, so a span running into
    /// one costs infinitely much to place there.
    ///
    /// Splitting asks this through `SpanInterference` instead.
    #[cfg(test)]
    pub fn interference_weight(
        &self,
        reg_units: impl Iterator<Item = Range<RegUnit>>,
        spans: impl ExactSizeIterator<Item = QuerySpan<E>> + Clone,
        scratch: &mut Vec<LiveBundle<E>>,
        weight_of: impl Fn(LiveBundle<E>) -> f32,
    ) -> f32 {
        debug_assert!(scratch.is_empty());

        if !self.push_interfering(reg_units, spans, scratch) {
            scratch.clear();
            return f32::INFINITY;
        }

        sum_distinct(scratch, weight_of)
    }

    /// Push the bundles already assigned in `reg_units` that overlap `spans`
    /// onto `out`, possibly more than once each.
    ///
    /// Returns `false` when a reservation is in the way, leaving `out` partly
    /// filled.
    fn push_interfering(
        &self,
        reg_units: impl Iterator<Item = Range<RegUnit>>,
        spans: impl ExactSizeIterator<Item = QuerySpan<E>> + Clone,
        out: &mut impl Extend<LiveBundle<E>>,
    ) -> bool {
        self.for_each_overlapping(reg_units, spans, |existing| match existing {
            Conflict::Assignment(existing) => {
                out.extend(iter::once(existing.bundle));
                ControlFlow::Continue(())
            }
            Conflict::Reservation(_) => ControlFlow::Break(()),
        })
        .is_none()
    }

    /// Do the given spans conflict with any existing assignment or reservation
    /// in `reg_units`?
    pub(crate) fn conflicts(
        &self,
        reg_units: impl Iterator<Item = Range<RegUnit>>,
        spans: impl ExactSizeIterator<Item = QuerySpan<E>> + Clone,
    ) -> bool {
        self.for_each_overlapping(reg_units, spans, |_| ControlFlow::Break(()))
            .is_some()
    }

    /// The one and only bundle whose existing assignments in `reg_units`
    /// conflict with the given spans.
    ///
    /// Returns `None` when there is no single conflicting assignment or there
    /// is a conflicting reservation.
    ///
    /// TODO: support evicting multiple bundles if that is still cheaper. will
    /// require an `&mut Vec<LiveBundle>` out parameter to these methods for
    /// writing the evicted bundles into.
    pub(crate) fn sole_conflicting_bundle(
        &self,
        reg_units: impl Iterator<Item = Range<RegUnit>> + Clone,
        spans: impl ExactSizeIterator<Item = QuerySpan<E>> + Clone,
    ) -> Option<LiveBundle<E>> {
        self.sole_conflicting_bundle_with(reg_units, spans, &mut None, |_| Some(()))
            .map(|(bundle, ())| bundle)
    }

    /// Like `sole_conflicting_bundle`, but `accept` sees the first bundle as
    /// soon as it is found, and may reject it by returning `None`, which stops
    /// the search early. When a reservation is what rules the candidate out,
    /// `reserved_at` is set to the span it is over.
    ///
    /// Spans are asked about one at a time, so that a reservation can be pinned
    /// to its span. The answer does not depend on that: two distinct bundles or
    /// any reservation rule the candidate out, and `accept` sees the same sole
    /// bundle either way.
    fn sole_conflicting_bundle_with<T>(
        &self,
        reg_units: impl Iterator<Item = Range<RegUnit>> + Clone,
        spans: impl ExactSizeIterator<Item = QuerySpan<E>> + Clone,
        reserved_at: &mut Option<QuerySpan<E>>,
        mut accept: impl FnMut(LiveBundle<E>) -> Option<T>,
    ) -> Option<(LiveBundle<E>, T)> {
        let mut sole: Option<(LiveBundle<E>, T)> = None;
        for span in spans {
            // `Some(true)` when a reservation rules the candidate out, and
            // `Some(false)` for anything else that does.
            let rejected = self.for_each_overlapping(
                reg_units.clone(),
                iter::once(span.clone()),
                |existing| {
                    let Conflict::Assignment(existing) = existing else {
                        return ControlFlow::Break(true);
                    };
                    match &sole {
                        Some((bundle, _)) if *bundle == existing.bundle => {
                            ControlFlow::Continue(())
                        }
                        Some(_) => ControlFlow::Break(false),
                        None => match accept(existing.bundle) {
                            Some(accepted) => {
                                sole = Some((existing.bundle, accepted));
                                ControlFlow::Continue(())
                            }
                            None => ControlFlow::Break(false),
                        },
                    }
                },
            );
            match rejected {
                None => {}
                Some(by_reservation) => {
                    if by_reservation {
                        *reserved_at = Some(span);
                    }
                    return None;
                }
            }
        }
        sole
    }

    /// Does a reservation that `span` may not share hold one of `reg_units`
    /// over it?
    fn reserved(
        &self,
        reg_units: impl Iterator<Item = Range<RegUnit>>,
        span: &QuerySpan<E>,
    ) -> bool {
        self.for_each_overlapping(
            reg_units,
            iter::once(span.clone()),
            |existing| match existing {
                Conflict::Reservation(_) => ControlFlow::Break(()),
                Conflict::Assignment(_) => ControlFlow::Continue(()),
            },
        )
        .is_some()
    }

    /// Call `f` with everything already occupying any of `reg_units` over
    /// `spans`, possibly more than once for the same occupant.
    pub(crate) fn for_each_occupant(
        &self,
        reg_units: impl Iterator<Item = Range<RegUnit>>,
        spans: impl ExactSizeIterator<Item = QuerySpan<E>> + Clone,
        mut f: impl FnMut(Occupant<E>),
    ) {
        let never: Option<()> = self.for_each_overlapping(reg_units, spans, |existing| {
            match existing {
                Conflict::Assignment(existing) => f(Occupant::Bundle(existing.bundle)),
                Conflict::Reservation(held) => f(Occupant::Reserved(held)),
            }
            ControlFlow::Continue(())
        });
        debug_assert!(never.is_none());
    }

    /// Remove all of `bundle`'s assignments.
    ///
    /// `spans` must be exactly the spans that `bundle` was assigned with.
    fn remove_assignment(
        &mut self,
        bundle: LiveBundle<E>,
        spans: impl ExactSizeIterator<Item = QuerySpan<E>> + Clone,
    ) {
        for (_unit, unit_assignments) in self.assignments.iter_mut() {
            for span in spans.clone() {
                let key = AssignmentKey::new(span.range().start);
                if unit_assignments
                    .get(key)
                    .is_some_and(|existing| existing.bundle == bundle)
                {
                    unit_assignments.remove(key);
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
        spans: impl ExactSizeIterator<Item = QuerySpan<E>> + Clone,
    ) {
        debug_assert!(!self.conflicts(reg_units.clone(), spans.clone()));
        for unit in iter_reg_units(reg_units) {
            for span in spans.clone() {
                let range = span.range();
                self.assignments[unit].insert(
                    AssignmentKey::new(range.start),
                    Assignment {
                        end: range.end,
                        bundle,
                    },
                );
            }
        }
    }

    /// Hold `reg_units` over `span` for a fixed operand.
    ///
    /// `held` is the allocation the units are held for, so that a reservation
    /// can answer who occupies a register.
    ///
    /// `porous_to` is the value the reservation holds the register for, and
    /// `None` when nothing may share it; see `ReservationEntry::porous_to`.
    ///
    /// `reg_units` is the reserved allocation's units member by member, which
    /// says which piece of the value each unit is porous to.
    ///
    /// No two reservations on a unit may overlap.
    pub fn insert_reservation(
        &mut self,
        reg_units: impl Iterator<Item = Range<RegUnit>>,
        span: Range<LivePoint<E>>,
        held: RegAllocation<E>,
        porous_to: Option<Val<E>>,
    ) {
        debug_assert!(span.start < span.end);
        for (member, units) in reg_units.enumerate() {
            let porous_to = porous_to.map(|val| PorousTo { val, member });
            for unit in units_in(units) {
                debug_assert!(
                    self.overlapping_reservations(unit, span.clone())
                        .next()
                        .is_none(),
                    "reserving {:?}..{:?} of {unit:?} overlaps an existing reservation",
                    span.start,
                    span.end,
                );
                self.reservations[unit].insert(
                    AssignmentKey::new(span.start),
                    ReservationEntry {
                        end: span.end,
                        held,
                        porous_to,
                    },
                );
            }
        }
    }

    /// Try to insert an assignment.
    ///
    /// If the proposed assignment does not conflict with any existing
    /// assignments, insert it and return the candidate it was assigned to.
    /// Otherwise, when every candidate conflicts with an existing assignment,
    /// return `None` and leave `self` unmodified.
    pub fn try_assign_to_reg(
        &mut self,
        bundle: LiveBundle<E>,
        candidates: impl IntoIterator<Item = Reg>,
        reg_units: impl Fn(Reg) -> Range<RegUnit>,
        spans: impl ExactSizeIterator<Item = QuerySpan<E>> + Clone,
    ) -> Option<Reg> {
        self.try_assign(bundle, candidates, |reg| iter::once(reg_units(reg)), spans)
    }

    /// Try to insert an assignment of `bundle` to one of the candidate register
    /// groups.
    ///
    /// If the proposed assignment does not conflict with any existing
    /// assignments, insert it and return the candidate it was assigned to.
    /// Otherwise, when every candidate conflicts with an existing assignment,
    /// return `None` and leave `self` unmodified.
    pub fn try_assign_to_reg_group<GroupUnits>(
        &mut self,
        bundle: LiveBundle<E>,
        candidates: impl IntoIterator<Item = RegGroup>,
        group_units: impl Fn(RegGroup) -> GroupUnits,
        spans: impl ExactSizeIterator<Item = QuerySpan<E>> + Clone,
    ) -> Option<RegGroup>
    where
        GroupUnits: Iterator<Item = Range<RegUnit>> + Clone,
    {
        self.try_assign(bundle, candidates, group_units, spans)
    }

    /// `try_assign_to_reg` and `try_assign_to_reg_group`, for candidates whose
    /// units `candidate_units` gives.
    fn try_assign<C, Units>(
        &mut self,
        bundle: LiveBundle<E>,
        candidates: impl IntoIterator<Item = C>,
        candidate_units: impl Fn(C) -> Units,
        spans: impl ExactSizeIterator<Item = QuerySpan<E>> + Clone,
    ) -> Option<C>
    where
        C: Copy,
        Units: Iterator<Item = Range<RegUnit>> + Clone,
    {
        debug_assert!(spans.len() > 0);

        // Where the last candidate first ran into something. Neighboring
        // candidates are usually blocked at the same busy point, so checking
        // that span first usually rules a candidate out in one query, and the
        // scan after it need not ask about it again.
        let mut blocked_at: Option<QuerySpan<E>> = None;
        for candidate in candidates {
            let units = candidate_units(candidate);
            if let Some(span) = &blocked_at
                && self.conflicts(units.clone(), iter::once(span.clone()))
            {
                continue;
            }
            let conflict = spans.clone().find(|span| {
                Some(span) != blocked_at.as_ref()
                    && self.conflicts(units.clone(), iter::once(span.clone()))
            });
            match conflict {
                Some(span) => blocked_at = Some(span),
                None => {
                    self.insert_assignment(bundle, units, spans);
                    return Some(candidate);
                }
            }
        }

        None
    }

    fn try_evict_and_assign<C, Units, Spans>(
        &mut self,
        bundle: LiveBundle<E>,
        candidates: impl IntoIterator<Item = C>,
        candidate_units: impl Fn(C) -> Units,
        max_cost: EvictionCost,
        eviction_cost: impl Fn(LiveBundle<E>, C) -> EvictionCost,
        bundle_spans: impl Fn(LiveBundle<E>) -> Spans,
    ) -> Option<(C, LiveBundle<E>)>
    where
        C: Copy,
        Units: Iterator<Item = Range<RegUnit>> + Clone,
        Spans: ExactSizeIterator<Item = QuerySpan<E>> + Clone,
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

        // Where a reservation last ruled a candidate out. Neighboring candidates
        // are usually held for the same fixed operand, so checking that span
        // first usually rules a candidate out in one query.
        let mut reserved_at = None;

        for candidate in candidates {
            let units = candidate_units(candidate);
            debug_assert!(self.conflicts(units.clone(), spans.clone()));

            // A reservation cannot be evicted, so one anywhere rules the
            // candidate out whatever else is in its way.
            if let Some(span) = &reserved_at
                && self.reserved(units.clone(), span)
            {
                continue;
            }

            // Evicting a candidate bundle must make this bundle assignable (not
            // conflict), or else the bundle is not a valid eviction candidate.
            //
            // The first bundle in the way is the only one this candidate could
            // evict, so price it at once and give up on the candidate as soon as
            // it cannot win, without looking for others.
            let Some((other_bundle, cost)) = self.sole_conflicting_bundle_with(
                units,
                spans.clone(),
                &mut reserved_at,
                |victim| {
                    let cost = eviction_cost(victim, candidate);
                    (cost < best_cost).then_some(cost)
                },
            ) else {
                continue;
            };

            debug_assert!(cost < best_cost);
            best = Some((other_bundle, candidate));
            best_cost = cost;
        }

        let Some((other_bundle, candidate)) = best else {
            return None;
        };

        self.remove_assignment(other_bundle, bundle_spans(other_bundle));
        self.insert_assignment(bundle, candidate_units(candidate), spans);
        Some((candidate, other_bundle))
    }

    /// Try to insert an assignment for `bundle`, evicting another bundle if
    /// necessary.
    ///
    /// If `bundle` was assigned, then returns the candidate it was assigned to
    /// along with the other `LiveBundle` that was evicted to make room for it.
    /// Otherwise, returns `None` and `self` is unmodified.
    pub fn try_evict_reg_and_assign<Spans>(
        &mut self,
        bundle: LiveBundle<E>,
        candidates: impl IntoIterator<Item = Reg>,
        reg_units: impl Fn(Reg) -> Range<RegUnit>,
        max_cost: EvictionCost,
        eviction_cost: impl Fn(LiveBundle<E>, Reg) -> EvictionCost,
        bundle_spans: impl Fn(LiveBundle<E>) -> Spans,
    ) -> Option<(Reg, LiveBundle<E>)>
    where
        Spans: ExactSizeIterator<Item = QuerySpan<E>> + Clone,
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
    ) -> Option<(RegGroup, LiveBundle<E>)>
    where
        GroupUnits: Iterator<Item = Range<RegUnit>> + Clone,
        Spans: ExactSizeIterator<Item = QuerySpan<E>> + Clone,
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

    /// Merge all of `other`'s assignments and reservations into `self`.
    ///
    /// None of `other`'s assignments may conflict with any assignment already
    /// in `self`, and none of its reservations with any reservation already in
    /// `self`.
    pub fn merge(&mut self, other: &Self) {
        for (unit, other_unit_assignments) in other.assignments.iter() {
            if other_unit_assignments.is_empty() {
                continue;
            }

            // Check the whole unit before touching `self`, so that the check
            // sees exactly the assignments we already had.
            if cfg!(debug_assertions) {
                for (key, assignment) in other_unit_assignments {
                    debug_assert!(
                        self.overlapping(unit, key.start..assignment.end)
                            .next()
                            .is_none(),
                        "merging {:?}'s assignment of {:?}..{:?} to {unit:?} conflicts with an \
                         existing assignment",
                        assignment.bundle,
                        key.start,
                        assignment.end,
                    );
                }
            }

            self.assignments[unit].merge(other_unit_assignments);
        }

        for (unit, other_unit_reservations) in other.reservations.iter() {
            if other_unit_reservations.is_empty() {
                continue;
            }

            if cfg!(debug_assertions) {
                for (key, reservation) in other_unit_reservations {
                    debug_assert!(
                        self.overlapping_reservations(unit, key.start..reservation.end)
                            .next()
                            .is_none(),
                        "merging a reservation of {:?}..{:?} on {unit:?} conflicts with an \
                         existing reservation",
                        key.start,
                        reservation.end,
                    );
                }
            }

            self.reservations[unit].merge(other_unit_reservations);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Inst, Position, live_ranges::SpillWeight};
    use core::fmt;
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

    /// The number of distinct values a generated span may carry.
    ///
    /// Small on purpose: we want the same value to turn up on both sides of a
    /// porosity question often enough to exercise it.
    const NUM_VALS: u8 = 3;

    fn val(index: u8) -> Val<u32> {
        Val::try_new(usize::from(index)).unwrap()
    }

    /// Decode a test op's value selector.
    ///
    /// Zero is the question a bare register asks, porous to nothing; the rest
    /// name a value.
    fn val_of(index: u8) -> Option<Val<u32>> {
        debug_assert!(index <= NUM_VALS);
        (index > 0).then(|| val(index - 1))
    }

    /// A span as the test ops name it: a start point, an end point, and a
    /// value selector.
    type TestSpan = (u8, u8, u8);

    fn query_span(&(start, end, v): &TestSpan) -> QuerySpan<u32> {
        match val_of(v) {
            Some(val) => QuerySpan::porous_to(val, span(start, end)),
            None => QuerySpan::sees_all_reservations(span(start, end)),
        }
    }

    fn query_spans(spans: &[TestSpan]) -> Vec<QuerySpan<u32>> {
        spans.iter().map(query_span).collect()
    }

    fn qspan(start: u8, end: u8, v: u8) -> QuerySpan<u32> {
        query_span(&(start, end, v))
    }

    /// One assignment as the oracle records it: one entry per (unit, span) pair.
    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    struct OracleEntry {
        unit: RegUnit,
        start: LivePoint<u32>,
        end: LivePoint<u32>,
        bundle: LiveBundle<u32>,
    }

    /// One reservation as the oracle records it: one entry per (unit, span)
    /// pair, exactly as for an assignment.
    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    struct OracleReservation {
        unit: RegUnit,
        start: LivePoint<u32>,
        end: LivePoint<u32>,
        porous_to: Option<PorousTo<u32>>,
    }

    /// Everything the matrix is supposed to be holding, in a shape that is
    /// obviously right rather than efficient.
    #[derive(Clone, Debug, Default)]
    struct Oracle {
        assignments: Vec<OracleEntry>,
        reservations: Vec<OracleReservation>,
    }

    impl Oracle {
        fn clear(&mut self) {
            self.assignments.clear();
            self.reservations.clear();
        }

        fn is_empty(&self) -> bool {
            self.assignments.is_empty() && self.reservations.is_empty()
        }
    }

    fn overlaps(span: &Range<LivePoint<u32>>, start: LivePoint<u32>, end: LivePoint<u32>) -> bool {
        LivePoint::spans_overlap(span.start, span.end, start, end)
    }

    /// Which member of `reg_units` covers `unit`, if any of them does.
    fn member_covering(reg_units: &[Range<RegUnit>], unit: RegUnit) -> Option<usize> {
        reg_units.iter().position(|units| units.contains(&unit))
    }

    /// Brute-force check whether any reservation stands in the way of putting
    /// `spans` in `reg_units`.
    fn oracle_reserved(
        oracle: &Oracle,
        reg_units: &[Range<RegUnit>],
        spans: &[QuerySpan<u32>],
    ) -> bool {
        oracle.reservations.iter().any(|existing| {
            let Some(member) = member_covering(reg_units, existing.unit) else {
                return false;
            };
            spans.iter().any(|span| {
                let porous_to = span.val().map(|val| PorousTo { val, member });
                !(porous_to.is_some() && existing.porous_to == porous_to)
                    && overlaps(&span.range(), existing.start, existing.end)
            })
        })
    }

    /// Brute-force check whether assigning `spans` to `reg_units` would
    /// conflict.
    fn oracle_conflicts(
        oracle: &Oracle,
        reg_units: &[Range<RegUnit>],
        spans: &[QuerySpan<u32>],
    ) -> bool {
        oracle.assignments.iter().any(|existing| {
            reg_units.iter().any(|units| units.contains(&existing.unit))
                && spans
                    .iter()
                    .any(|span| overlaps(&span.range(), existing.start, existing.end))
        }) || oracle_reserved(oracle, reg_units, spans)
    }

    fn oracle_insert(
        oracle: &mut Oracle,
        bundle: LiveBundle<u32>,
        reg_units: &[Range<RegUnit>],
        spans: &[QuerySpan<u32>],
    ) {
        for index in 0..NUM_UNITS {
            let unit = unit(index);
            if !reg_units.iter().any(|units| units.contains(&unit)) {
                continue;
            }
            for span in spans {
                let range = span.range();
                oracle.assignments.push(OracleEntry {
                    unit,
                    start: range.start,
                    end: range.end,
                    bundle,
                });
            }
        }
    }

    fn oracle_insert_reservation(
        oracle: &mut Oracle,
        reg_units: &[Range<RegUnit>],
        span: &Range<LivePoint<u32>>,
        porous_to: Option<Val<u32>>,
    ) {
        for index in 0..NUM_UNITS {
            let unit = unit(index);
            let Some(member) = member_covering(reg_units, unit) else {
                continue;
            };
            oracle.reservations.push(OracleReservation {
                unit,
                start: span.start,
                end: span.end,
                porous_to: porous_to.map(|val| PorousTo { val, member }),
            });
        }
    }

    /// Would reserving `span` on `reg_units` collide with a reservation that
    /// is already there?
    ///
    /// `insert_reservation` forbids it, so the test declines to make the call.
    fn oracle_reservation_would_overlap(
        oracle: &Oracle,
        reg_units: &[Range<RegUnit>],
        span: &Range<LivePoint<u32>>,
    ) -> bool {
        oracle.reservations.iter().any(|existing| {
            reg_units.iter().any(|units| units.contains(&existing.unit))
                && overlaps(span, existing.start, existing.end)
        })
    }

    /// Brute-force version of `Assignments::try_assign_to_reg` and
    /// `Assignments::try_assign_to_reg_group`.
    ///
    /// Returns the index of the candidate that the bundle was assigned to.
    fn oracle_try_assign(
        oracle: &mut Oracle,
        bundle: LiveBundle<u32>,
        candidates: &[Vec<Range<RegUnit>>],
        spans: &[QuerySpan<u32>],
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
    ///
    /// A victim's spans carry no value, faithfully: `remove_assignment` never
    /// looks at one.
    fn spans_by_bundle(
        oracle: &Oracle,
        incoming: LiveBundle<u32>,
        incoming_spans: &[QuerySpan<u32>],
    ) -> Vec<Vec<QuerySpan<u32>>> {
        (0..usize::from(NUM_BUNDLES))
            .map(|index| {
                let b = bundle(index);
                if b == incoming {
                    return incoming_spans.to_vec();
                }
                let mut spans: Vec<_> = oracle
                    .assignments
                    .iter()
                    .filter(|existing| existing.bundle == b)
                    .map(|existing| existing.start..existing.end)
                    .collect();
                spans.sort_unstable_by_key(|span| (span.start, span.end));
                spans.dedup();
                spans
                    .into_iter()
                    .map(QuerySpan::sees_all_reservations)
                    .collect()
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
        oracle: &mut Oracle,
        bundle: LiveBundle<u32>,
        candidates: &[Vec<Range<RegUnit>>],
        spans: &[QuerySpan<u32>],
        max_cost: EvictionCost,
        cost: impl Fn(LiveBundle<u32>, usize) -> EvictionCost,
    ) -> Option<(LiveBundle<u32>, usize)> {
        let mut best = None;
        let mut best_cost = max_cost;

        for (index, units) in candidates.iter().enumerate() {
            // A reservation cannot be evicted, so no eviction clears this.
            if oracle_reserved(oracle, units, spans) {
                continue;
            }

            // The distinct bundles in the way, of which there must be exactly
            // one for a single eviction to make room here.
            let mut conflicting: Vec<LiveBundle<u32>> = oracle
                .assignments
                .iter()
                .filter(|existing| {
                    units.iter().any(|units| units.contains(&existing.unit))
                        && spans
                            .iter()
                            .any(|span| overlaps(&span.range(), existing.start, existing.end))
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
        oracle
            .assignments
            .retain(|existing| existing.bundle != victim);
        oracle_insert(oracle, bundle, &candidates[index], spans);
        Some((victim, index))
    }

    /// Check that `assignments` records exactly what `oracle` does.
    fn check_agree(assignments: &Assignments<u32>, oracle: &Oracle) -> Result<(), String> {
        if assignments.is_reset() != oracle.is_empty() {
            return Err(format!(
                "`is_reset` is {} but the oracle holds {} assignments and {} reservations",
                assignments.is_reset(),
                oracle.assignments.len(),
                oracle.reservations.len(),
            ));
        }

        // Only the units covered by our test registers are ever written.
        if assignments.assignments.len() > NUM_UNITS {
            return Err(format!(
                "the map has grown to hold {} units, but this test only names {NUM_UNITS}",
                assignments.assignments.len(),
            ));
        }
        if assignments.reservations.len() > NUM_UNITS {
            return Err(format!(
                "the reservation map has grown to hold {} units, but this test only names \
                 {NUM_UNITS}",
                assignments.reservations.len(),
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

        let mut expected = oracle.assignments.clone();
        expected.sort_unstable();

        if actual != expected {
            return Err(format!(
                "the assignments are {actual:?} but should be {expected:?}"
            ));
        }

        let mut actual = Vec::new();
        for (unit, unit_reservations) in assignments.reservations.iter() {
            for (key, reservation) in unit_reservations {
                actual.push(OracleReservation {
                    unit,
                    start: key.start,
                    end: reservation.end,
                    porous_to: reservation.porous_to,
                });
            }
        }
        actual.sort_unstable();

        let mut expected = oracle.reservations.clone();
        expected.sort_unstable();

        if actual != expected {
            return Err(format!(
                "the reservations are {actual:?} but should be {expected:?}"
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

        for (unit, unit_reservations) in assignments.reservations.iter() {
            let mut previous: Option<Range<LivePoint<u32>>> = None;
            for (key, reservation) in unit_reservations {
                if key.start >= reservation.end {
                    return Err(format!(
                        "{unit:?} reserves the empty span {:?}..{:?}",
                        key.start, reservation.end,
                    ));
                }
                if let Some(previous) = &previous
                    && LivePoint::spans_overlap(
                        previous.start,
                        previous.end,
                        key.start,
                        reservation.end,
                    )
                {
                    return Err(format!(
                        "{unit:?} reserves the overlapping spans {previous:?} and {:?}..{:?}",
                        key.start, reservation.end,
                    ));
                }
                previous = Some(key.start..reservation.end);
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
        oracle: &Oracle,
    ) -> Result<(), String> {
        for (index, units) in probe_unit_sets().iter().enumerate() {
            for start in 0..NUM_POINTS {
                for end in start + 1..=NUM_POINTS {
                    // The querying value decides which reservations are in
                    // the way, so rotate it across the grid rather than
                    // sweeping every value at every point.
                    let probe = [query_span(&(start, end, (start + end) % (NUM_VALS + 1)))];
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
        oracle: &Oracle,
        reg_units: &[Range<RegUnit>],
        spans: &[QuerySpan<u32>],
        weight_of: impl Fn(LiveBundle<u32>) -> f32,
    ) -> f32 {
        // Nothing can buy out a reservation, so there is no finite price.
        if oracle_reserved(oracle, reg_units, spans) {
            return f32::INFINITY;
        }

        let mut conflicting: Vec<LiveBundle<u32>> = oracle
            .assignments
            .iter()
            .filter(|existing| {
                reg_units.iter().any(|units| units.contains(&existing.unit))
                    && spans
                        .iter()
                        .any(|span| overlaps(&span.range(), existing.start, existing.end))
            })
            .map(|existing| existing.bundle)
            .collect();
        conflicting.sort_unstable();
        conflicting.dedup();
        conflicting.into_iter().map(weight_of).sum()
    }

    /// The span sets that `interference_weight` is probed with.
    ///
    /// Each set asks on behalf of a different value, including no value at
    /// all, since that decides which reservations are in the way.
    fn probe_span_sets() -> Vec<Vec<QuerySpan<u32>>> {
        let v = &mut 0;
        let mut s = move |start, end| {
            let span = query_span(&(start, end, *v % (NUM_VALS + 1)));
            *v += 1;
            span
        };
        vec![
            vec![s(0, 8)],
            vec![s(3, 5)],
            vec![s(2, 3)],
            vec![s(0, 1), s(2, 3)],
            vec![s(0, 1), s(3, 4)],
            vec![s(0, 2), s(4, 6)],
            vec![s(0, 1), s(7, 8)],
            vec![s(1, 2), s(3, 5), s(6, 8)],
            vec![s(0, 4), s(4, 8)],
            // Enough spans that a reservation in the middle leaves several on
            // each side, which `fill_row` walks from both ends.
            vec![s(0, 1), s(2, 3), s(3, 4), s(5, 6), s(7, 8)],
        ]
    }

    fn check_interference_weight_agrees(
        assignments: &Assignments<u32>,
        oracle: &Oracle,
    ) -> Result<(), String> {
        let scratch = &mut Vec::new();
        let weight_of = |b: LiveBundle<u32>| WEIGHTS[b.index()];
        let span_sets = probe_span_sets();

        for (index, units) in probe_unit_sets().iter().enumerate() {
            let weigh = |spans: &[QuerySpan<u32>],
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
            let split = weigh(&[qspan(0, 4, 1), qspan(4, 8, 1)], scratch, &weight_of);
            let whole = weigh(&[qspan(0, 8, 1)], scratch, &weight_of);
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

    /// `SpanInterference` must price every half exactly as `interference_weight`
    /// does, whether its divided span is intact, clipped, or widened, and
    /// whatever order candidates are asked about in.
    fn check_span_interference_agrees(assignments: &Assignments<u32>) -> Result<(), String> {
        let scratch = &mut Vec::new();
        let weight_of = |b: LiveBundle<u32>| WEIGHTS[b.index()];
        let mut cache = SpanInterference::new();
        let units = probe_unit_sets();

        for spans in probe_span_sets() {
            let ranges: Vec<_> = spans.iter().map(|s| s.range()).collect();

            // Every prefix and suffix the kernel can carve: dividing each span
            // at either of its ends, between them, or reaching back a point.
            let mut halves = Vec::new();
            for (k, range) in ranges.iter().enumerate() {
                let mut ats = vec![range.start, range.end];
                if range.start.next_point() < range.end {
                    ats.push(range.start.next_point());
                }
                for at in ats {
                    if range.start < at {
                        halves.push(HalfSpan::prefix(&ranges, k, at));
                    }
                    if at < range.end {
                        halves.push(HalfSpan::suffix(&ranges, k, at));
                    }
                }
                if range.start > point(0) {
                    halves.push(HalfSpan::suffix(&ranges, k, range.start.prev_point()));
                }
            }

            // Ask about the candidates backwards and then forwards, so that
            // each one is first asked about out of order.
            cache.reset(spans.iter().cloned());
            let order = (0..units.len()).rev().chain(0..units.len());
            for candidate in order {
                for half in &halves {
                    let actual = cache.weight(
                        assignments,
                        SplitCandidate::try_new(candidate).unwrap(),
                        units[candidate].iter().cloned(),
                        *half,
                        scratch,
                        weight_of,
                    );
                    let pieces: Vec<_> = half
                        .iter_indexed()
                        .map(|(i, range)| QuerySpan {
                            porous_to: spans[i].porous_to,
                            range,
                        })
                        .collect();
                    let expected = assignments.interference_weight(
                        units[candidate].iter().cloned(),
                        pieces.iter().cloned(),
                        scratch,
                        weight_of,
                    );
                    if actual != expected {
                        return Err(format!(
                            "`SpanInterference::weight({}, {pieces:?})` for {spans:?} is \
                             {actual} but `interference_weight` is {expected}",
                            probe_name(candidate),
                        ));
                    }
                    if !scratch.is_empty() {
                        return Err(format!(
                            "`SpanInterference::weight({}, {pieces:?})` left {} bundles in the \
                             scratch buffer",
                            probe_name(candidate),
                            scratch.len(),
                        ));
                    }
                }
            }
        }

        Ok(())
    }

    /// Which candidate did `try_assign_*`/`try_evict_*_and_assign` choose?
    ///
    /// The oracle answers in indices but the methods in registers, so map back.
    fn candidate_index<C>(candidates: &[C], chosen: C) -> usize
    where
        C: Copy + PartialEq + fmt::Debug,
    {
        candidates
            .iter()
            .position(|&c| c == chosen)
            .unwrap_or_else(|| panic!("{chosen:?} is not one of the candidates {candidates:?}"))
    }

    fn check_try_assign(
        assignments: &Assignments<u32>,
        what: &str,
        candidates: &[Vec<Range<RegUnit>>],
        spans: &[QuerySpan<u32>],
        actual: Option<usize>,
        expected: Option<usize>,
    ) -> Result<(), String> {
        if actual != expected {
            return Err(match expected {
                Some(index) => format!(
                    "assigning {what} for {spans:?} returned {actual:?}, but it should have gone \
                     in candidate {index}, which covers {:?}",
                    candidates[index],
                ),
                None => format!(
                    "assigning {what} for {spans:?} returned {actual:?}, but every candidate is \
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
        spans: &[QuerySpan<u32>],
        actual: Option<(LiveBundle<u32>, usize)>,
        expected: Option<(LiveBundle<u32>, usize)>,
    ) -> Result<(), String> {
        if actual != expected {
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
            spans: Vec<TestSpan>,
        },
        TryAssignGroup {
            bundle: u8,
            candidates: Vec<u8>,
            spans: Vec<TestSpan>,
        },
        TryEvictAndAssign {
            bundle: u8,
            candidates: Vec<u8>,
            spans: Vec<TestSpan>,
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
            spans: Vec<TestSpan>,
            weights: Vec<u8>,
            hints: Vec<u8>,
        },
        /// Reserve a register over one span, porous to the span's value
        /// selector; zero makes it a hard wall.
        Reserve {
            candidate: u8,
            span: TestSpan,
        },
        ReserveGroup {
            candidate: u8,
            span: TestSpan,
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

    /// Ensure that a single span is in-range.
    fn fixup_span(span: &mut TestSpan) {
        let (start, end, v) = span;
        *start %= NUM_POINTS;
        if !(*start < *end && *end <= NUM_POINTS) {
            *end = *start + 1 + (*end % (NUM_POINTS - *start));
        }
        *v %= NUM_VALS + 1;
    }

    /// Ensure that the spans are in-range.
    fn fixup_spans(spans: &mut Vec<TestSpan>) {
        spans.truncate(MAX_SPANS);

        for span in spans.iter_mut() {
            fixup_span(span);
        }

        spans.sort_unstable();

        // Remove overlapping spans.
        let mut previous_end = 0;
        spans.retain(|&(start, end, _)| {
            let keep = start >= previous_end;
            if keep {
                previous_end = end;
            }
            keep
        });

        // Ensure we always have at least one span.
        if spans.is_empty() {
            spans.push((0, 1, 1));
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
                Op::Reserve { candidate, span } => {
                    *candidate %= num_regs;
                    fixup_span(span);
                    continue;
                }
                Op::ReserveGroup { candidate, span } => {
                    *candidate %= num_groups;
                    fixup_span(span);
                    continue;
                }
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

    fn reserve(candidate: u8, span: TestSpan) -> Op {
        Op::Reserve { candidate, span }
    }

    fn reserve_group(candidate: u8, span: TestSpan) -> Op {
        Op::ReserveGroup { candidate, span }
    }

    fn try_assign(bundle: u8, candidates: &[u8], spans: &[TestSpan]) -> Op {
        Op::TryAssign {
            bundle,
            candidates: candidates.to_vec(),
            spans: spans.to_vec(),
        }
    }

    fn try_assign_group(bundle: u8, candidates: &[u8], spans: &[TestSpan]) -> Op {
        Op::TryAssignGroup {
            bundle,
            candidates: candidates.to_vec(),
            spans: spans.to_vec(),
        }
    }

    fn try_evict(
        bundle: u8,
        candidates: &[u8],
        spans: &[TestSpan],
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
        spans: &[TestSpan],
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
                try_assign(0, &[R4], &[(0, 6, 1)]),
                try_assign(1, &[R4], &[(2, 4, 1)]),
                try_assign(2, &[R0], &[(2, 4, 1)]),
                try_assign(3, &[R1, R2], &[(2, 4, 1)]),
            ],
            // Exact-boundary abutment: `[0, 3)` ends where `[3, 6)` begins, so
            // the two do not conflict and both fit in one unit. This is the
            // case that an over-eager fix to `conflicts` gets wrong. The span
            // that reaches one point further does conflict.
            vec![
                try_assign(0, &[R0], &[(0, 3, 1)]),
                try_assign(1, &[R0], &[(3, 6, 1)]),
                try_assign(2, &[R0], &[(2, 4, 1)]),
            ],
            // The identical span twice: the second attempt conflicts on the
            // same register and on one that aliases it, and succeeds on one
            // whose units are disjoint.
            vec![
                try_assign(0, &[R1], &[(1, 4, 1)]),
                try_assign(1, &[R1], &[(1, 4, 1)]),
                try_assign(2, &[R4], &[(1, 4, 1)]),
                try_assign(3, &[R3], &[(1, 4, 1)]),
            ],
            // Aliasing in the other direction: a wide register first, then the
            // narrow ones it covers and the ones it does not.
            vec![
                try_assign(0, &[R5], &[(0, 6, 1)]),
                try_assign(1, &[R2], &[(0, 6, 1)]),
                try_assign(2, &[R3], &[(0, 6, 1)]),
                try_assign(3, &[R0, R1], &[(0, 6, 1)]),
            ],
            // Spans one program point wide, and their immediate neighbors,
            // which must not conflict with them.
            vec![
                try_assign(0, &[R2], &[(2, 3, 1)]),
                try_assign(1, &[R5], &[(1, 2, 1), (3, 4, 1)]),
                try_assign(2, &[R5], &[(2, 3, 1)]),
            ],
            // A bundle of two spans with a hole between them, which something
            // else can be assigned to, and then a span covering the whole
            // thing, which cannot.
            vec![
                try_assign(0, &[R0], &[(0, 2, 1), (4, 6, 1)]),
                try_assign(1, &[R0], &[(2, 4, 1)]),
                try_assign(2, &[R0], &[(0, 6, 1)]),
            ],
            // Preference order: the first candidate is taken, so the second one
            // wins; and an empty candidate list assigns nothing at all.
            vec![
                try_assign(0, &[R0], &[(0, 6, 1)]),
                try_assign(1, &[R0, R1], &[(0, 6, 1)]),
                try_assign(2, &[R4, R2], &[(0, 6, 1)]),
                try_assign(3, &[], &[(0, 6, 1)]),
            ],
            // The register with no units, which has nothing to conflict with,
            // and so "succeeds" while recording nothing and standing in nobody
            // else's way.
            vec![
                try_assign(0, &[R6], &[(0, 6, 1)]),
                try_assign(1, &[R6], &[(0, 6, 1)]),
                try_assign(2, &[R6, R4], &[(0, 6, 1)]),
            ],
            // Reset and start over: what was taken is free again.
            vec![
                try_assign(0, &[R4], &[(0, 6, 1)]),
                Op::Reset,
                try_assign(0, &[R4], &[(0, 6, 1)]),
            ],
            // A register blocks every group that contains it, but leaves a
            // group whose members are all disjoint from it alone.
            vec![
                try_assign(0, &[R0], &[(0, 6, 1)]),
                try_assign_group(1, &[G0], &[(0, 6, 1)]),
                try_assign_group(2, &[G1], &[(0, 6, 1)]),
            ],
            // And the other way around: a group blocks each of its members and
            // the wide register that covers them, but nothing else.
            vec![
                try_assign_group(0, &[G0], &[(0, 6, 1)]),
                try_assign(1, &[R0], &[(0, 6, 1)]),
                try_assign(2, &[R1], &[(0, 6, 1)]),
                try_assign(3, &[R4], &[(0, 6, 1)]),
                try_assign(0, &[R2], &[(0, 6, 1)]),
            ],
            // Only the *second* member of the group is taken, so the group as a
            // whole is unusable and we fall through to the next candidate.
            vec![
                try_assign(0, &[R1], &[(0, 6, 1)]),
                try_assign_group(1, &[G0, G1], &[(0, 6, 1)]),
            ],
            // Aliasing through the wide registers: r4 covers exactly g0's
            // units, so it blocks g0 and g4, but leaves g1 alone.
            vec![
                try_assign(0, &[R4], &[(0, 6, 1)]),
                try_assign_group(1, &[G0], &[(0, 6, 1)]),
                try_assign_group(2, &[G4], &[(0, 6, 1)]),
                try_assign_group(3, &[G1], &[(0, 6, 1)]),
            ],
            // A group whose members are out of unit order and not adjacent,
            // against the registers it covers and the ones it leaves between
            // them.
            vec![
                try_assign_group(0, &[G3], &[(0, 6, 1)]),
                try_assign(1, &[R0], &[(0, 6, 1)]),
                try_assign(2, &[R3], &[(0, 6, 1)]),
                try_assign_group(3, &[G2], &[(0, 6, 1)]),
            ],
            // A group with a member that covers no units. Unlike the bare
            // register r6, which never conflicts with anything, g5 records r0's
            // unit and so conflicts with itself the second time around.
            vec![
                try_assign_group(0, &[G5], &[(0, 6, 1)]),
                try_assign_group(1, &[G5], &[(0, 6, 1)]),
                try_assign(2, &[R6], &[(0, 6, 1)]),
                try_assign(3, &[R1], &[(0, 6, 1)]),
            ],
            // Exact-boundary abutment, for groups: `[0, 3)` ends where `[3, 6)`
            // begins, so both fit in g0; the span that reaches one point
            // further does conflict.
            vec![
                try_assign_group(0, &[G0], &[(0, 3, 1)]),
                try_assign_group(1, &[G0], &[(3, 6, 1)]),
                try_assign_group(2, &[G0], &[(2, 4, 1)]),
            ],
            // A group assignment that *encloses* the queried span -- the case a
            // forward range query cannot see -- probed on the group itself, on
            // one of its members, and on a group that overlaps it in part.
            vec![
                try_assign_group(0, &[G0], &[(0, 6, 1)]),
                try_assign_group(1, &[G0], &[(2, 4, 1)]),
                try_assign(2, &[R1], &[(2, 4, 1)]),
                try_assign_group(3, &[G2], &[(2, 4, 1)]),
            ],
            // A group bundle with a hole between its spans, which a register
            // can slot into, and then a span covering the whole thing, which
            // cannot.
            vec![
                try_assign_group(0, &[G1], &[(0, 2, 1), (4, 6, 1)]),
                try_assign(1, &[R2], &[(2, 4, 1)]),
                try_assign_group(2, &[G1], &[(0, 6, 1)]),
            ],
            // Preference order for groups: the first candidate is taken, so the
            // second one wins; and an empty candidate list assigns nothing.
            vec![
                try_assign_group(0, &[G0], &[(0, 6, 1)]),
                try_assign_group(1, &[G0, G1], &[(0, 6, 1)]),
                try_assign_group(2, &[], &[(0, 6, 1)]),
                try_assign(3, &[R3], &[(0, 6, 1)]),
            ],
            // A three-member group, and what it does and does not leave free.
            vec![
                try_assign_group(0, &[G6], &[(0, 6, 1)]),
                try_assign(1, &[R3], &[(0, 6, 1)]),
                try_assign_group(2, &[G1], &[(0, 6, 1)]),
                try_assign_group(3, &[G4], &[(0, 6, 1)]),
            ],
            // Two three-member groups.
            vec![
                try_assign_group(0, &[G6, G7], &[(0, 3, 1)]),
                try_assign(1, &[R0, R1, R2, R3], &[(0, 4, 1)]),
                try_assign_group(2, &[G6, G7], &[(3, 6, 1)]),
                try_assign(3, &[R0, R1, R2, R3], &[(4, 6, 1)]),
            ],
            // Reset frees a group's units again, just as it does a register's.
            vec![
                try_assign_group(0, &[G4], &[(0, 6, 1)]),
                try_assign(1, &[R0], &[(0, 6, 1)]),
                Op::Reset,
                try_assign_group(0, &[G4], &[(0, 6, 1)]),
            ],
            // The whole point: a bundle worth more than the one in its way
            // takes the register, and one worth less does not.
            vec![
                try_assign(0, &[R0], &[(0, 6, 1)]),
                try_evict(1, &[R0], &[(0, 6, 1)], &[1, 2], &[]),
            ],
            vec![
                try_assign(0, &[R0], &[(0, 6, 1)]),
                try_evict(1, &[R0], &[(0, 6, 1)], &[3, 2], &[]),
            ],
            // Two bundles are in the way, so evicting either one still leaves
            // the other and this register is no candidate at all, no matter how
            // cheap they both are.
            vec![
                try_assign(0, &[R0], &[(0, 2, 1)]),
                try_assign(1, &[R0], &[(2, 4, 1)]),
                try_evict(2, &[R0], &[(0, 4, 1)], &[1, 1, 5], &[]),
            ],
            // Given a choice, we evict the cheaper of the two victims, even
            // though the more expensive one is in the earlier candidate.
            vec![
                try_assign(0, &[R0], &[(0, 6, 1)]),
                try_assign(1, &[R1], &[(0, 6, 1)]),
                try_evict(2, &[R0, R1], &[(0, 6, 1)], &[3, 1, 5], &[]),
            ],
            // Equally cheap victims go to the earlier candidate.
            vec![
                try_assign(0, &[R0], &[(0, 6, 1)]),
                try_assign(1, &[R1], &[(0, 6, 1)]),
                try_evict(2, &[R1, R0], &[(0, 6, 1)], &[1, 1, 5], &[]),
            ],
            // Broken hints outweigh spill weight: the cheap victim sits in the
            // register it prefers, so we take the expensive one instead.
            vec![
                try_assign(0, &[R0], &[(0, 6, 1)]),
                try_assign(1, &[R1], &[(0, 6, 1)]),
                try_evict(2, &[R0, R1], &[(0, 6, 1)], &[1, 3, 5], &[R0]),
            ],
            // And when breaking a hint is the only option, we do not take it,
            // however light the victim.
            vec![
                try_assign(0, &[R0], &[(0, 6, 1)]),
                try_evict(1, &[R0], &[(0, 6, 1)], &[1, 5], &[R0]),
            ],
            // A hint only counts against the register it actually names, so
            // evicting this bundle from a *different* register is free.
            vec![
                try_assign(0, &[R1], &[(0, 6, 1)]),
                try_evict(1, &[R1], &[(0, 6, 1)], &[1, 2], &[R0]),
            ],
            // The victim holds a wide register, so evicting it has to free
            // every one of its units, not just the one we wanted.
            vec![
                try_assign(0, &[R4], &[(0, 6, 1)]),
                try_evict(1, &[R0], &[(0, 6, 1)], &[1, 2], &[]),
                try_assign(2, &[R1], &[(0, 6, 1)]),
            ],
            // Likewise, evicting a victim has to free every one of its spans,
            // not just the one that was in the way.
            vec![
                try_assign(0, &[R0], &[(0, 2, 1), (4, 6, 1)]),
                try_evict(1, &[R0], &[(1, 3, 1)], &[1, 2], &[]),
                try_assign(2, &[R0], &[(4, 6, 1)]),
            ],
            // A bundle can never evict itself, however the weights fall.
            vec![
                try_assign(0, &[R0], &[(0, 6, 1)]),
                try_evict(0, &[R0], &[(0, 6, 1)], &[1], &[]),
            ],
            // The bundle doing the evicting already holds a register of its
            // own, and keeps it.
            vec![
                try_assign(0, &[R0], &[(0, 6, 1)]),
                try_assign(1, &[R1], &[(0, 6, 1)]),
                try_evict(1, &[R0], &[(0, 6, 1)], &[1, 2], &[]),
            ],
            // A victim can in turn be evicted by the next bundle along.
            vec![
                try_assign(0, &[R0], &[(0, 6, 1)]),
                try_evict(1, &[R0], &[(0, 6, 1)], &[1, 2], &[]),
                try_evict(2, &[R0], &[(0, 6, 1)], &[1, 2, 3], &[]),
            ],
            // Reset after an eviction: everything is free again.
            vec![
                try_assign(0, &[R0], &[(0, 6, 1)]),
                try_evict(1, &[R0], &[(0, 6, 1)], &[1, 2], &[]),
                Op::Reset,
                try_assign(0, &[R0], &[(0, 6, 1)]),
            ],
            // A register in the way of a group, and the group's other member
            // left free.
            vec![
                try_assign(0, &[R1], &[(0, 6, 1)]),
                try_evict_group(1, &[G0], &[(0, 6, 1)], &[1, 2], &[]),
                try_assign(2, &[R2], &[(0, 6, 1)]),
            ],
            // A group victim spanning every unit, evicted for a group that
            // needs only half of them.
            vec![
                try_assign_group(0, &[G4], &[(0, 6, 1)]),
                try_evict_group(1, &[G1], &[(0, 6, 1)], &[1, 2], &[]),
                try_assign(2, &[R0], &[(0, 6, 1)]),
            ],
            // A group victim evicted by a plain register assignment.
            vec![
                try_assign_group(0, &[G0], &[(0, 6, 1)]),
                try_evict(1, &[R0], &[(0, 6, 1)], &[1, 2], &[]),
                try_assign(2, &[R1], &[(0, 6, 1)]),
            ],
            // Two different bundles in one group's way, so no single eviction
            // frees it, but each of them alone frees a group of its own.
            vec![
                try_assign(0, &[R0], &[(0, 6, 1)]),
                try_assign(1, &[R1], &[(0, 6, 1)]),
                try_evict_group(2, &[G0], &[(0, 6, 1)], &[1, 1, 5], &[]),
                try_evict_group(3, &[G2], &[(0, 6, 1)], &[1, 1, 5, 5], &[]),
            ],
            // Broken hints for groups: the cheap victim prefers the first
            // group, so the expensive one in the second group goes instead.
            vec![
                try_assign_group(0, &[G0], &[(0, 6, 1)]),
                try_assign_group(1, &[G1], &[(0, 6, 1)]),
                try_evict_group(2, &[G0, G1], &[(0, 6, 1)], &[1, 3, 5], &[G0]),
            ],
            // A hard reservation keeps every value out of the register it
            // holds and the ones that alias it, but not out of abutting spans
            // or disjoint registers.
            vec![
                reserve(R0, (2, 4, 0)),
                try_assign(0, &[R0], &[(2, 4, 1)]),
                try_assign(1, &[R4], &[(2, 4, 2)]),
                try_assign(2, &[R0], &[(0, 2, 1)]),
                try_assign(3, &[R1], &[(2, 4, 1)]),
            ],
            // A porous reservation lets exactly one value through: the one it
            // was made to deliver.
            vec![
                reserve(R0, (2, 4, 1)),
                try_assign(0, &[R0], &[(2, 4, 2)]),
                try_assign(1, &[R0], &[(2, 4, 1)]),
                try_assign(2, &[R0], &[(2, 4, 0)]),
            ],
            // Porosity is per span, not per bundle: the overlapping span is
            // the one that has to carry the reserved value.
            vec![
                reserve(R0, (4, 6, 1)),
                try_assign(0, &[R0], &[(0, 2, 1), (4, 6, 2)]),
                try_assign(1, &[R0], &[(0, 2, 2), (4, 6, 1)]),
            ],
            // Nothing evicts a reservation; the second candidate, holding
            // only a bundle, is taken instead.
            vec![
                reserve(R0, (0, 6, 0)),
                try_assign(0, &[R1], &[(0, 6, 1)]),
                try_evict(1, &[R0, R1], &[(0, 6, 1)], &[1, 5], &[]),
            ],
            // A reservation and an assignment overlap when the value matches,
            // and the reservation still blocks evicting a different value in.
            vec![
                reserve(R0, (0, 6, 1)),
                try_assign(0, &[R0], &[(0, 6, 1)]),
                try_evict(1, &[R0], &[(0, 6, 2)], &[1, 5], &[]),
            ],
            // Abutting reservations, the shape a fixed use and fixed def of
            // one register take: the register is unusable across both.
            vec![
                reserve(R0, (2, 3, 1)),
                reserve(R0, (3, 4, 0)),
                try_assign(0, &[R0], &[(2, 4, 1)]),
                try_assign(1, &[R0], &[(2, 3, 1)]),
                try_assign(2, &[R0], &[(3, 4, 1)]),
            ],
            // Reset clears reservations too.
            vec![
                reserve(R0, (0, 6, 0)),
                try_assign(0, &[R0], &[(0, 6, 1)]),
                Op::Reset,
                try_assign(0, &[R0], &[(0, 6, 1)]),
            ],
            // A group reservation holds all its members' units, so it blocks
            // each member, the wide register over them, and any overlapping
            // group.
            vec![
                reserve_group(G0, (0, 6, 1)),
                try_assign(0, &[R0], &[(0, 6, 2)]),
                try_assign(1, &[R4], &[(0, 6, 2)]),
                try_assign_group(2, &[G2], &[(0, 6, 2)]),
                try_assign_group(3, &[G0], &[(0, 6, 1)]),
            ],
            // The register with no units reserves nothing and stands in
            // nobody's way, just as assigning it records nothing.
            vec![
                reserve(R6, (0, 6, 0)),
                try_assign(0, &[R6], &[(0, 6, 1)]),
                try_assign(1, &[R0], &[(0, 6, 1)]),
            ],
            // A reservation made *after* the register is already assigned:
            // legal when the value matches, and the two coexist.
            vec![
                try_assign(0, &[R0], &[(0, 6, 1)]),
                reserve(R0, (2, 4, 1)),
                try_assign(1, &[R0], &[(0, 6, 2)]),
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

        Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run_with(mutator, seeds(), |ops: &Vec<Op>| -> Result<(), String> {
                let mut assignments = Assignments::<u32>::new();
                let mut oracle = Oracle::default();

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
                            let spans = query_spans(spans);
                            let units: Vec<Vec<Range<RegUnit>>> =
                                candidates.iter().map(|&r| vec![reg_units(r)]).collect();

                            let expected = oracle_try_assign(&mut oracle, b, &units, &spans);
                            let actual = assignments
                                .try_assign_to_reg(
                                    b,
                                    candidates.iter().copied(),
                                    reg_units,
                                    spans.iter().cloned(),
                                )
                                .map(|r| candidate_index(&candidates, r));
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
                            let spans = query_spans(spans);
                            let units: Vec<Vec<Range<RegUnit>>> = candidates
                                .iter()
                                .map(|&g| group_units(g).collect())
                                .collect();

                            let expected = oracle_try_assign(&mut oracle, b, &units, &spans);
                            let actual = assignments
                                .try_assign_to_reg_group(
                                    b,
                                    candidates.iter().copied(),
                                    group_units,
                                    spans.iter().cloned(),
                                )
                                .map(|g| candidate_index(&candidates, g));
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
                            let spans = query_spans(spans);

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
                                // Stickiness and minimality are the
                                // bundle-shaped half of the cost, and this
                                // test has no bundle shapes: the fields'
                                // ordering is covered where they are defined.
                                EvictionCost::new(
                                    0,
                                    false,
                                    broken_hints,
                                    SpillWeight::new(f32::from(weights[victim.index()])),
                                )
                            };
                            let max_cost = EvictionCost::new(
                                0,
                                false,
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
                            let actual = assignments
                                .try_evict_reg_and_assign(
                                    b,
                                    candidates.iter().copied(),
                                    reg_units,
                                    max_cost,
                                    cost,
                                    bundle_spans,
                                )
                                .map(|(r, victim)| (victim, candidate_index(&candidates, r)));
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
                            let spans = query_spans(spans);

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
                                // Stickiness and minimality are the
                                // bundle-shaped half of the cost, and this
                                // test has no bundle shapes: the fields'
                                // ordering is covered where they are defined.
                                EvictionCost::new(
                                    0,
                                    false,
                                    broken_hints,
                                    SpillWeight::new(f32::from(weights[victim.index()])),
                                )
                            };
                            let max_cost = EvictionCost::new(
                                0,
                                false,
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
                            let actual = assignments
                                .try_evict_reg_group_and_assign(
                                    b,
                                    candidates.iter().copied(),
                                    group_units,
                                    max_cost,
                                    cost,
                                    bundle_spans,
                                )
                                .map(|(g, victim)| (victim, candidate_index(&candidates, g)));
                            check_try_evict(
                                &assignments,
                                &format!("{b:?} to one of {candidates:?}"),
                                &units,
                                &spans,
                                actual,
                                expected,
                            )?;
                        }

                        Op::Reserve {
                            candidate,
                            span: sp,
                        } => {
                            let r = reg(*candidate);
                            let units = vec![reg_units(r)];
                            let q = query_span(sp);
                            let (porous_to, sp) = (q.val(), q.range());

                            // Two reservations may never overlap on a unit, so
                            // decline to make a call that is not allowed.
                            if oracle_reservation_would_overlap(&oracle, &units, &sp) {
                                continue;
                            }

                            assignments.insert_reservation(
                                units.iter().cloned(),
                                sp.clone(),
                                RegAllocation::Reg(r),
                                porous_to,
                            );
                            oracle_insert_reservation(&mut oracle, &units, &sp, porous_to);
                        }

                        Op::ReserveGroup {
                            candidate,
                            span: sp,
                        } => {
                            let g = group(*candidate);
                            let units: Vec<Range<RegUnit>> = group_units(g).collect();
                            let q = query_span(sp);
                            let (porous_to, sp) = (q.val(), q.range());

                            if oracle_reservation_would_overlap(&oracle, &units, &sp) {
                                continue;
                            }

                            assignments.insert_reservation(
                                units.iter().cloned(),
                                sp.clone(),
                                RegAllocation::RegGroup(g),
                                porous_to,
                            );
                            oracle_insert_reservation(&mut oracle, &units, &sp, porous_to);
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
                    check_span_interference_agrees(&assignments)?;

                    // Merging this state into an empty set of assignments must
                    // reproduce it exactly, so the oracle we already have
                    // describes the result as well.
                    let mut merged = Assignments::<u32>::new();
                    merged.merge(&assignments);
                    check_agree(&merged, &oracle)?;
                    check_no_overlaps(&merged)?;
                    check_conflicts_agree(&merged, &oracle)?;

                    // And merging an empty set of assignments in must leave
                    // this state alone.
                    assignments.merge(&Assignments::new());
                    check_agree(&assignments, &oracle)?;
                }

                Ok(())
            })
    }

    /// A reservation is porous to its own value only in the register order it
    /// holds.
    #[test]
    fn a_reservation_is_porous_only_in_its_own_register_order() {
        let mut assignments = Assignments::<u32>::new();
        let reserved = val(0);
        assignments.insert_reservation(
            group_units(group(G3)),
            span(2, 4),
            RegAllocation::RegGroup(group(G3)),
            Some(reserved),
        );

        // The reserved group itself: every piece lines up.
        assert!(
            !assignments.conflicts(group_units(group(G3)), [qspan(2, 4, 1)].into_iter()),
            "the reserved value may sit in the order the reservation holds",
        );

        // The other order of the same two registers: `r0` is this span's first
        // piece and the reservation's second.
        assert!(
            assignments.conflicts(group_units(group(G0)), [qspan(2, 4, 1)].into_iter()),
            "and may not sit in the other order, which wants a different \
             piece of it in `r0`",
        );

        // Unit by unit, not group by group: `r0` alone is this span's first
        // piece and the reservation's second.
        assert!(
            assignments.conflicts(
                core::iter::once(reg_units(reg(R0))),
                [qspan(2, 4, 1)].into_iter()
            ),
            "nor alone in a register the reservation holds a later piece in",
        );
        assert!(
            !assignments.conflicts(
                core::iter::once(reg_units(reg(R3))),
                [qspan(2, 4, 1)].into_iter()
            ),
            "and may sit alone in the register holding its first piece",
        );

        // Another value is refused everywhere the reservation reaches, and the
        // reservation reaches nothing outside its own span.
        assert!(
            assignments.conflicts(group_units(group(G3)), [qspan(2, 4, 2)].into_iter()),
            "another value may not share the reservation at all",
        );
        assert!(
            !assignments.conflicts(group_units(group(G3)), [qspan(0, 2, 2)].into_iter()),
            "and the reservation holds nothing before it starts",
        );

        // The oracle agrees on all of it.
        let mut oracle = Oracle::default();
        oracle_insert_reservation(
            &mut oracle,
            &group_units(group(G3)).collect::<Vec<_>>(),
            &span(2, 4),
            Some(reserved),
        );
        check_agree(&assignments, &oracle).unwrap();
        check_no_overlaps(&assignments).unwrap();
        check_conflicts_agree(&assignments, &oracle).unwrap();
    }

    #[test]
    fn merge_disjoint() {
        let mut a = Assignments::<u32>::new();
        let mut b = Assignments::<u32>::new();

        assert!(
            a.try_assign_to_reg(
                bundle(0),
                [reg(R0)],
                reg_units,
                [qspan(0, 2, 1)].into_iter()
            )
            .is_some()
        );
        assert!(
            b.try_assign_to_reg(
                bundle(1),
                [reg(R0)],
                reg_units,
                [qspan(2, 4, 1)].into_iter()
            )
            .is_some()
        );
        assert!(
            b.try_assign_to_reg_group(
                bundle(2),
                [group(G1)],
                group_units,
                [qspan(0, 6, 1)].into_iter(),
            )
            .is_some()
        );

        a.merge(&b);

        // `a` now holds exactly the union of what the two of them held.
        let mut oracle = Oracle::default();
        oracle_insert(
            &mut oracle,
            bundle(0),
            &[reg_units(reg(R0))],
            &[qspan(0, 2, 1)],
        );
        oracle_insert(
            &mut oracle,
            bundle(1),
            &[reg_units(reg(R0))],
            &[qspan(2, 4, 1)],
        );
        oracle_insert(
            &mut oracle,
            bundle(2),
            &group_units(group(G1)).collect::<Vec<_>>(),
            &[qspan(0, 6, 1)],
        );
        check_agree(&a, &oracle).unwrap();
        check_no_overlaps(&a).unwrap();
        check_conflicts_agree(&a, &oracle).unwrap();

        // The merge left `b` alone.
        let mut b_oracle = Oracle::default();
        oracle_insert(
            &mut b_oracle,
            bundle(1),
            &[reg_units(reg(R0))],
            &[qspan(2, 4, 1)],
        );
        oracle_insert(
            &mut b_oracle,
            bundle(2),
            &group_units(group(G1)).collect::<Vec<_>>(),
            &[qspan(0, 6, 1)],
        );
        check_agree(&b, &b_oracle).unwrap();
    }

    #[test]
    fn merge_interleaved() {
        let mut a = Assignments::<u32>::new();
        let mut b = Assignments::<u32>::new();
        let mut oracle = Oracle::default();

        // Each side ends up with spans both before and after the other's.
        for (i, start) in [0, 2, 4, 6].into_iter().enumerate() {
            let side = if i % 3 == 0 { &mut a } else { &mut b };
            let span = qspan(start, start + 2, 1);
            assert!(
                side.try_assign_to_reg(bundle(i), [reg(R0)], reg_units, [span.clone()].into_iter())
                    .is_some()
            );
            oracle_insert(&mut oracle, bundle(i), &[reg_units(reg(R0))], &[span]);
        }

        a.merge(&b);
        check_agree(&a, &oracle).unwrap();
        check_no_overlaps(&a).unwrap();
        check_conflicts_agree(&a, &oracle).unwrap();
    }

    /// Merging assignments that are in the way of each other is a bug in the
    /// caller, and debug builds catch it. The two registers here are different
    /// but alias the same unit, so this is a conflict that only the units, not
    /// the registers, reveal.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic = "conflicts with an existing assignment"]
    fn merge_conflicting() {
        let mut a = Assignments::<u32>::new();
        let mut b = Assignments::<u32>::new();

        assert!(
            a.try_assign_to_reg(
                bundle(0),
                [reg(R4)],
                reg_units,
                [qspan(0, 6, 1)].into_iter()
            )
            .is_some()
        );
        assert!(
            b.try_assign_to_reg(
                bundle(1),
                [reg(R1)],
                reg_units,
                [qspan(2, 4, 1)].into_iter()
            )
            .is_some()
        );

        a.merge(&b);
    }
}
