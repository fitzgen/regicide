//! Choosing where to split a bundle.

use crate::{
    entity::EntityRepr,
    input::Position,
    live_ranges::{LivePoint, touch_mid_inst},
};
use core::{cmp::Ordering, ops::Range};

/// One use of a bundle being split.
#[derive(Clone, Copy, Debug)]
pub struct SplitUse<E>
where
    E: EntityRepr,
{
    /// Where the use is.
    pub point: LivePoint<E>,

    /// What keeping it in a register is worth.
    pub weight: f32,

    /// May a cut be placed immediately before this use?
    ///
    /// Always true for a use at `Position::Early`, which is an instruction
    /// boundary and so always somewhere a move can go. A use at
    /// `Position::Late` is another matter: a cut there would have to put its
    /// move in the middle of the instruction.
    ///
    /// See `LiveSpan::is_tied_to` for details.
    pub cut_before_allowed: bool,
}

/// How good a split is, for one candidate register.
#[derive(Clone, Copy, Debug)]
pub struct SplitScore {
    max_interference: f32,
    min_use_weight: f32,
}

impl SplitScore {
    /// Score a split.
    ///
    /// `max_interference` is the worst interference of its parts, and
    /// `min_use_weight` is the least use weight of its parts.
    ///
    /// Neither may be NaN and both must be at least `0.0`. `max_interference`
    /// may be infinite: a register held for a fixed operand cannot be vacated
    /// at any price.
    pub fn new(max_interference: f32, min_use_weight: f32) -> Self {
        debug_assert!(!max_interference.is_nan());
        debug_assert!(min_use_weight.is_finite());
        debug_assert!(max_interference >= 0.0);
        debug_assert!(min_use_weight >= 0.0);
        // `total_cmp` ranks `-0.0` below `0.0`.
        SplitScore {
            max_interference: max_interference + 0.0,
            min_use_weight: min_use_weight + 0.0,
        }
    }

    #[cfg(test)]
    fn normalized(self) -> Self {
        SplitScore {
            max_interference: self.max_interference + 0.0,
            min_use_weight: self.min_use_weight + 0.0,
        }
    }
}

impl Ord for SplitScore {
    fn cmp(&self, other: &Self) -> Ordering {
        // Less interference is better.
        other
            .max_interference
            .total_cmp(&self.max_interference)
            // Greater use-weight balance the better.
            .then_with(|| self.min_use_weight.total_cmp(&other.min_use_weight))
    }
}

impl PartialOrd for SplitScore {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for SplitScore {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for SplitScore {}

/// The cut to make, and the register to aim the halves at.
#[derive(Clone, Copy, Debug)]
pub struct SplitChoice<C, K> {
    /// Where to cut.
    pub cut: K,

    /// The candidate the cut was scored against.
    pub candidate: C,

    /// The split's score.
    pub score: SplitScore,
}

/// Where to cut a bundle within one of its spans.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WithinSpanCut<E>
where
    E: EntityRepr,
{
    /// The index into `spans` of the span being divided.
    pub index: usize,

    /// The program point to cut at.
    ///
    /// Always at [`Position::Early`], and always strictly inside
    /// `spans[index]`, so neither piece of the divided span is ever empty.
    pub at: LivePoint<E>,
}

/// A cut either between spans or within a span.
///
/// These cuts are relative to the original `spans` given.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cut<E>
where
    E: EntityRepr,
{
    /// Cut between two spans, resulting in `spans[..i]` and `spans[i..]`.
    ///
    /// Always `1 <= i < spans.len()`, so neither half is ever empty.
    ///
    /// `spans[i]` may begin in the middle of an instruction, when the two spans
    /// touch there and nothing ties their uses together. Applying such a cut
    /// obliges the caller to widen the suffix back to the instruction boundary,
    /// however.
    BetweenSpans(usize),

    /// Cut within a span.
    WithinSpan(WithinSpanCut<E>),
}

/// One half of a within-span split.
///
/// This exists so that the splitting kernel can hand its caller both halves
/// without allocating or materializing the split span.
#[derive(Clone, Copy, Debug)]
pub struct HalfSpan<'a, E>
where
    E: EntityRepr,
{
    /// The spans on this side of the cut that the cut did not touch.
    whole: &'a [Range<LivePoint<E>>],

    /// The piece of the divided span that fell on this side.
    ///
    /// Held unpacked rather than as a `Range`, which is not `Copy`.
    clipped_start: LivePoint<E>,
    clipped_end: LivePoint<E>,

    /// Whether `clipped` comes before `whole` (suffix) or after it (prefix).
    clipped_first: bool,

    /// Where the divided span sat in the slice this half was carved from.
    clipped_index: usize,
}

impl<'a, E> HalfSpan<'a, E>
where
    E: EntityRepr,
{
    /// Get the prefix and suffix of the given split.
    fn split(spans: &'a [Range<LivePoint<E>>], index: usize, at: LivePoint<E>) -> (Self, Self) {
        (
            Self::prefix(spans, index, at),
            Self::suffix(spans, index, at),
        )
    }

    /// The half before a cut at `at` inside `spans[index]`.
    fn prefix(spans: &'a [Range<LivePoint<E>>], index: usize, at: LivePoint<E>) -> Self {
        HalfSpan {
            whole: &spans[..index],
            clipped_start: spans[index].start,
            clipped_end: at,
            clipped_first: false,
            clipped_index: index,
        }
    }

    /// The half after a cut at `at` inside `spans[index]`.
    fn suffix(spans: &'a [Range<LivePoint<E>>], index: usize, at: LivePoint<E>) -> Self {
        HalfSpan {
            whole: &spans[index + 1..],
            clipped_start: at,
            clipped_end: spans[index].end,
            clipped_first: true,
            clipped_index: index,
        }
    }

    /// How many spans this half holds.
    ///
    /// Never zero.
    pub fn len(&self) -> usize {
        self.whole.len() + 1
    }

    /// Get this half's `i`th span, in ascending program order.
    pub fn get(&self, i: usize) -> Range<LivePoint<E>> {
        debug_assert!(i < self.len());
        let clipped = self.clipped_start..self.clipped_end;
        match (self.clipped_first, i) {
            (true, 0) => clipped,
            (true, i) => self.whole[i - 1].clone(),
            (false, i) if i < self.whole.len() => self.whole[i].clone(),
            (false, _) => clipped,
        }
    }

    /// This half's spans, in ascending program order.
    #[cfg(test)]
    pub fn iter(&self) -> impl ExactSizeIterator<Item = Range<LivePoint<E>>> + Clone + '_ {
        (0..self.len()).map(|i| self.get(i))
    }

    /// Where this half's `i`th span sat in the slice the half was carved from.
    fn original_index(&self, i: usize) -> usize {
        debug_assert!(i < self.len());
        if self.clipped_first {
            self.clipped_index + i
        } else {
            i
        }
    }

    /// This half's spans, each paired with its index in the slice the half was
    /// carved from, in ascending program order.
    pub fn iter_indexed(
        &self,
    ) -> impl ExactSizeIterator<Item = (usize, Range<LivePoint<E>>)> + Clone + '_ {
        (0..self.len()).map(|i| (self.original_index(i), self.get(i)))
    }
}

/// Walks `uses` in ascending order alongside ascending cut points, tracking the
/// total weight of the uses that fall strictly before the current cut.
struct UseWeightCursor<'a, E>
where
    E: EntityRepr,
{
    uses: &'a [SplitUse<E>],
    cursor: usize,
    prefix_weight: f32,
    total_weight: f32,
}

impl<'a, E> UseWeightCursor<'a, E>
where
    E: EntityRepr,
{
    /// `uses` must be sorted by program point.
    fn new(uses: &'a [SplitUse<E>]) -> Self {
        debug_assert!(uses.windows(2).all(|pair| pair[0].point <= pair[1].point));
        UseWeightCursor {
            uses,
            cursor: 0,
            prefix_weight: 0.0,
            total_weight: uses.iter().map(|u| u.weight).sum(),
        }
    }

    /// Move to a cut at `at`, folding every use strictly before it into the
    /// prefix's weight.
    ///
    /// `at` must be greater than or equal to every point already passed.
    fn advance_to(&mut self, at: LivePoint<E>) {
        while self.cursor < self.uses.len() && self.uses[self.cursor].point < at {
            self.prefix_weight += self.uses[self.cursor].weight;
            self.cursor += 1;
        }
    }

    /// The lesser of the two halves' use weights.
    fn min_use_weight(&self) -> f32 {
        let suffix_weight = self.total_weight - self.prefix_weight;
        self.prefix_weight.min(suffix_weight)
    }
}

/// The places we could divide `spans` into two halves, without cutting any
/// span.
///
/// This filters out splits that would leave one half empty as well as splits
/// that do not fall on an instruction boundary (which can create demands for
/// moves that are unsatisfiable).
fn between_span_cuts<'a, E>(
    spans: &'a [Range<LivePoint<E>>],
    uses: &'a [SplitUse<E>],
) -> impl Iterator<Item = usize> + Clone + 'a
where
    E: EntityRepr,
{
    spans
        .windows(2)
        .enumerate()
        .filter(move |(_i, pair)| gap_admits_a_cut(&pair[0], &pair[1], uses))
        .map(|(i, _pair)| i + 1)
}

/// Can a cut go in the gap between `before` and `after`?
///
/// Either an instruction boundary falls in the gap, so any move the cut demands
/// has somewhere to go, or the two spans touch in the middle of an instruction
/// and the cut demands no move at all.
fn gap_admits_a_cut<E>(
    before: &Range<LivePoint<E>>,
    after: &Range<LivePoint<E>>,
    uses: &[SplitUse<E>],
) -> bool
where
    E: EntityRepr,
{
    debug_assert!(before.end <= after.start);
    !touch_mid_inst(before.end, after.start) || cut_is_allowed_at(uses, after.start)
}

/// Do all of the uses at `at`, if any, allow a cut immediately before them?
///
/// `uses` must be sorted by program point.
fn cut_is_allowed_at<E>(uses: &[SplitUse<E>], at: LivePoint<E>) -> bool
where
    E: EntityRepr,
{
    let first = uses.partition_point(|u| u.point < at);
    uses[first..]
        .iter()
        .take_while(|u| u.point == at)
        .all(|u| u.cut_before_allowed)
}

/// All the places we could cut any span within `spans` in two.
///
/// For each pair of uses within the same span, we offer a potential cut just
/// after the first use, and just before the second use, deduplicating when
/// those two points are the same. We also filter out any illegal
/// mid-instruction cut, as those can require unsatisfiable moves.
///
/// Potential cuts are yielded in ascending program order.
fn within_span_cuts<'a, E>(
    spans: &'a [Range<LivePoint<E>>],
    uses: &'a [SplitUse<E>],
) -> impl Iterator<Item = WithinSpanCut<E>> + Clone + 'a
where
    E: EntityRepr,
{
    spans.iter().enumerate().flat_map(move |(index, span)| {
        let first = uses.partition_point(|u| u.point < span.start);
        let last = uses.partition_point(|u| u.point < span.end);

        uses[first..last].windows(2).flat_map(move |pair| {
            debug_assert!(pair[0].point <= pair[1].point);
            let earliest = pair[0].point.inst_boundary_after();
            let latest = pair[1].point.inst_boundary_at_or_before();

            (earliest <= latest)
                .then_some(earliest)
                .into_iter()
                .chain((earliest < latest).then_some(latest))
                .map(move |at| WithinSpanCut { index, at })
        })
    })
}

/// Find the best boundary between the given `spans` to split at, or return
/// `None` if there is no valid place to split between spans.
///
/// `uses` must be sorted by program point.
///
/// `candidates` is the set of `Reg`s or `RegGroup`s that the associated bundle
/// could be assigned to.
///
/// `interference` is a function that calculates how much making room for one
/// half of a proposed split would cost: that is, the weight of the other
/// bundles that would need to be displaced.
///
/// Returns an index `cut` where `1 <= cut < spans.len()` describing how `spans`
/// should be split: `spans[..cut]` and `spans[cut..]`.
///
/// Ties go to the lower middle of the first run of tied cuts, halving rather
/// than peeling the bundle, then to the earliest candidate. This avoids
/// `O(n^2)` complexity in certain edge cases.
pub fn best_split_between_spans<E, C>(
    spans: &[Range<LivePoint<E>>],
    uses: &[SplitUse<E>],
    candidates: impl IntoIterator<Item = C> + Clone,
    mut interference: impl FnMut(C, HalfSpan<'_, E>) -> f32,
) -> Option<SplitChoice<C, usize>>
where
    E: EntityRepr,
    C: Copy,
{
    middle_of_best_run(
        between_span_cuts(spans, uses),
        uses,
        |&k| spans[k].start,
        |k, min_use_weight| {
            best_candidate_between_spans(
                spans,
                k,
                min_use_weight,
                candidates.clone(),
                &mut interference,
            )
        },
    )
}

/// The lower middle of the first run of consecutive `cuts` tied for the best
/// score.
///
/// `at` gives where each cut falls among `uses`, and `best_at` scores a cut's
/// best candidate given its `min_use_weight`.
fn middle_of_best_run<E, C, K>(
    cuts: impl Iterator<Item = K> + Clone,
    uses: &[SplitUse<E>],
    at: impl Fn(&K) -> LivePoint<E>,
    mut best_at: impl FnMut(K, f32) -> Option<SplitChoice<C, K>>,
) -> Option<SplitChoice<C, K>>
where
    E: EntityRepr,
    C: Copy,
    K: Copy,
{
    let mut cursor = UseWeightCursor::new(uses);

    // The best run's first cut and length.
    let mut best: Option<(SplitChoice<C, K>, usize)> = None;
    let mut run_start = 0;
    let mut run_open = false;

    for (i, cut) in cuts.clone().enumerate() {
        cursor.advance_to(at(&cut));
        let Some(choice) = best_at(cut, cursor.min_use_weight()) else {
            continue;
        };

        match &mut best {
            Some((best, len)) if choice.score == best.score => {
                if run_open {
                    *len += 1;
                }
            }
            Some((best, _)) if choice.score < best.score => run_open = false,
            _ => {
                best = Some((choice, 1));
                run_start = i;
                run_open = true;
            }
        }
    }

    let (first, len) = best?;
    let middle = (len - 1) / 2;
    if middle == 0 {
        return Some(first);
    }

    // Ties share `min_use_weight`.
    let cut = cuts.clone().nth(run_start + middle).unwrap();
    let choice = best_at(cut, first.score.min_use_weight).unwrap();
    debug_assert!(choice.score == first.score);
    Some(choice)
}

/// The best candidate for cutting before `spans[k]`.
fn best_candidate_between_spans<E, C>(
    spans: &[Range<LivePoint<E>>],
    k: usize,
    min_use_weight: f32,
    candidates: impl IntoIterator<Item = C>,
    interference: &mut impl FnMut(C, HalfSpan<'_, E>) -> f32,
) -> Option<SplitChoice<C, usize>>
where
    E: EntityRepr,
    C: Copy,
{
    debug_assert!(1 <= k && k < spans.len());

    // The prefix keeps its spans exactly; the suffix gains the first half of
    // the instruction it starts inside of, if it starts inside one.
    let prefix = HalfSpan::prefix(spans, k - 1, spans[k - 1].end);
    let suffix = HalfSpan::suffix(spans, k, spans[k].start.inst_boundary_at_or_before());

    let mut best: Option<SplitChoice<C, usize>> = None;
    for candidate in candidates {
        let prefix_interference = interference(candidate, prefix);
        let suffix_interference = interference(candidate, suffix);
        let max_interference = prefix_interference.max(suffix_interference);
        let score = SplitScore::new(max_interference, min_use_weight);
        if best.is_none_or(|best| score > best.score) {
            best = Some(SplitChoice {
                cut: k,
                candidate,
                score,
            });
        }
    }
    best
}

/// Find the best point within a span in `spans` to split at, or return `None`
/// if no span holds two uses that a cut could come between.
///
/// `uses` must be sorted by program point, and every use must lie within a span
/// in `spans`.
///
/// `spans` must be sorted and disjoint.
///
/// `candidates`, `interference`, and the tie-break are the same as with
/// `best_split_between_spans`.
pub fn best_split_within_span<E, C>(
    spans: &[Range<LivePoint<E>>],
    uses: &[SplitUse<E>],
    candidates: impl IntoIterator<Item = C> + Clone,
    mut interference: impl FnMut(C, HalfSpan<'_, E>) -> f32,
) -> Option<SplitChoice<C, WithinSpanCut<E>>>
where
    E: EntityRepr,
    C: Copy,
{
    middle_of_best_run(
        within_span_cuts(spans, uses),
        uses,
        |cut| cut.at,
        |cut, min_use_weight| {
            debug_assert_eq!(cut.at.pos(), Position::Early);
            debug_assert!(spans[cut.index].start < cut.at);
            debug_assert!(cut.at < spans[cut.index].end);

            let (prefix, suffix) = HalfSpan::split(spans, cut.index, cut.at);

            let mut best: Option<SplitChoice<C, WithinSpanCut<E>>> = None;
            for candidate in candidates.clone() {
                let prefix_interference = interference(candidate, prefix);
                let suffix_interference = interference(candidate, suffix);
                let max_interference = prefix_interference.max(suffix_interference);
                let score = SplitScore::new(max_interference, min_use_weight);
                if best.is_none_or(|best| score > best.score) {
                    best = Some(SplitChoice {
                        cut,
                        candidate,
                        score,
                    });
                }
            }
            best
        },
    )
}

/// Get every cut necessary to split the given `spans` into minimal pieces.
///
/// The cuts are yielded in ascending program order.
///
/// `uses` must be sorted by program point, and fall within a span in `spans`.
///
/// `spans` must be sorted and disjoint.
pub fn minimal_cuts<'a, E>(
    spans: &'a [Range<LivePoint<E>>],
    uses: &'a [SplitUse<E>],
) -> impl Iterator<Item = Cut<E>> + Clone + 'a
where
    E: EntityRepr,
{
    debug_assert!(uses.windows(2).all(|u| u[0].point <= u[1].point));
    debug_assert!(spans.windows(2).all(|s| s[0].end <= s[1].start));

    spans.iter().enumerate().flat_map(move |(index, span)| {
        let gap = (index > 0 && gap_admits_a_cut(&spans[index - 1], span, uses))
            .then_some(Cut::BetweenSpans(index));
        gap.into_iter()
            .chain(minimal_cuts_within_span(index, span, uses))
    })
}

/// Cut `span` into minimal pieces around each use in `uses`.
///
/// Cuts are in ascending program order.
fn minimal_cuts_within_span<'a, E>(
    index: usize,
    span: &Range<LivePoint<E>>,
    uses: &'a [SplitUse<E>],
) -> impl Iterator<Item = Cut<E>> + Clone + 'a
where
    E: EntityRepr,
{
    debug_assert!(uses.windows(2).all(|u| u[0].point <= u[1].point));
    let first = uses.partition_point(|u| u.point.inst_boundary_after() <= span.start);
    let last = uses.partition_point(|u| u.point.inst_boundary_at_or_before() < span.end);
    let in_span = &uses[first..last];

    let start = span.start;
    let end = span.end;

    in_span
        .iter()
        .enumerate()
        // Filter out uses at the same instruction as the last one, since they
        // result in the same cut point.
        .filter(move |(i, u)| {
            *i == 0
                || in_span[i - 1].point.inst_boundary_at_or_before()
                    != u.point.inst_boundary_at_or_before()
        })
        .flat_map(move |(i, u)| {
            let before = u.point.inst_boundary_at_or_before();
            let after = u.point.inst_boundary_after();

            // If this instruction is immediately following the last one, then
            // the last `after` is identical to this `before`, and we can skip
            // it.
            let before_is_new = i == 0 || in_span[i - 1].point.inst_boundary_after() != before;

            // A cut at or outside a span doesn't split it.
            let should_cut_before = before_is_new && start < before && before < end;
            let should_cut_after = start < after && after < end;

            should_cut_before
                .then_some(before)
                .into_iter()
                .chain(should_cut_after.then_some(after))
                .map(move |at| Cut::WithinSpan(WithinSpanCut { index, at }))
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Inst, entity::Entity as _, live_ranges::is_minimal_bundle};
    use mutatis::{
        Mutate,
        check::{Check, CheckResult},
        mutators as m,
    };
    use std::{format, string::String, vec, vec::Vec};

    /// The toy program this module's decisions are checked against.
    ///
    /// Bigger than one bundle could plausibly fill, so that a bundle has room to
    /// have holes, and partitioned into blocks, which the kernel never sees.
    /// The blocks are here because spans never cross one (`live_ranges.rs`'s
    /// invariant 1), so clipping every generated span at the boundaries is what
    /// makes multi-span bundles — and therefore any cuts at all — arise the way
    /// they really do rather than only where a seed puts them.
    ///
    /// ```text
    ///  inst:    0    1  |  2    3    4  |  5  |  6    7
    ///         +---------+---------------+-----+---------+
    /// block:  |   b0    |      b1       | b2  |   b3    |
    ///         +---------+---------------+-----+---------+
    /// ```
    const NUM_INSTS: u8 = 8;

    const NUM_POINTS: u8 = NUM_INSTS * 2;

    /// The default block partition above, one bit per instruction: bit `i` is
    /// set when a block starts at instruction `i`.
    const BLOCKS: u16 = (1 << 0) | (1 << 2) | (1 << 5) | (1 << 6);

    /// Three is enough to tell "the best" from "the first" and from "the last".
    const NUM_CANDIDATES: u8 = 3;

    const MAX_OPS: usize = 12;
    const MAX_SPANS: usize = 6;
    const MAX_USES: usize = 8;

    fn point(index: u8) -> LivePoint<u32> {
        debug_assert!(index <= NUM_POINTS);
        let index = usize::from(index);
        let pos = if index % 2 == 0 {
            Position::Early
        } else {
            Position::Late
        };
        LivePoint::new(Inst::try_new(index / 2).unwrap(), pos)
    }

    fn span(start: u8, end: u8) -> Range<LivePoint<u32>> {
        debug_assert!(start < end);
        point(start)..point(end)
    }

    fn overlaps(a: &Range<LivePoint<u32>>, b: &Range<LivePoint<u32>>) -> bool {
        a.start < b.end && b.start < a.end
    }

    /// A bundle already parked in a candidate, standing in the way.
    ///
    /// Weights are distinct powers of two, so every subset sums to a distinct
    /// exactly-representable `f32` and a double count or an omission names its
    /// own culprit rather than blending in.
    #[derive(Clone, Debug)]
    struct Parked {
        candidate: u8,
        spans: Vec<Range<LivePoint<u32>>>,
        weight: f32,
    }

    /// What it would cost to make room for `half` in `candidate`.
    ///
    /// Each parked bundle is priced **once**, if it overlaps *any* span of the
    /// half. That is `Assignments::interference_weight`'s contract stated
    /// without reference to how it is implemented, and it is what turns being
    /// charged for a hole into a test failure: a half's hole is not part of the
    /// half, so a bundle sitting entirely inside one costs nothing.
    fn interference(parked: &[Parked], candidate: u8, half: &[Range<LivePoint<u32>>]) -> f32 {
        parked
            .iter()
            .filter(|p| p.candidate == candidate)
            .filter(|p| {
                p.spans
                    .iter()
                    .any(|theirs| half.iter().any(|ours| overlaps(theirs, ours)))
            })
            .map(|p| p.weight)
            .sum()
    }

    /// One bundle: the spans it covers and the uses inside them.
    #[derive(Clone, Debug)]
    struct Piece {
        spans: Vec<Range<LivePoint<u32>>>,
        uses: Vec<SplitUse<u32>>,
    }

    impl Piece {
        fn len_insts(&self) -> usize {
            self.spans
                .iter()
                .map(|s| s.end.prev_point().inst().index() - s.start.inst().index() + 1)
                .sum()
        }

        /// How many distinct instructions this piece touches.
        ///
        /// Unlike `len_insts`, which sums over the spans, an instruction that
        /// two of the piece's spans both touch is counted once. That is what
        /// `is_minimal_bundle` wants: a bundle reaching one instruction through
        /// two spans is as small as a bundle can get.
        fn len_distinct_insts(&self) -> usize {
            let mut n = 0;
            let mut prev: Option<usize> = None;
            for s in &self.spans {
                let first = s.start.inst().index();
                let last = s.end.prev_point().inst().index();
                let first = match prev {
                    Some(prev) if prev >= first => prev + 1,
                    _ => first,
                };
                if first <= last {
                    n += last - first + 1;
                }
                prev = Some(last);
            }
            n
        }

        /// The instructions this piece reaches into, as an inclusive range of
        /// indices.
        ///
        /// Unlike `len_insts`, which sums over the spans, this counts an
        /// instruction that two of the piece's spans both touch only once.
        fn inst_range(&self) -> (usize, usize) {
            let first = self.spans.first().unwrap().start.inst().index();
            let last = self.spans.last().unwrap().end.prev_point().inst().index();
            (first, last)
        }
    }

    struct State {
        /// The block partition, which the kernel never sees but which decides
        /// where the spans are cut and therefore which cuts exist.
        blocks: u16,

        /// Which instructions a tie crosses the middle of, one bit per
        /// instruction.
        ///
        /// When bit `i` is set, no cut may go immediately before a use at
        /// `(i, Late)`: separating that use from the rest of instruction `i`
        /// would demand a move in the middle of the instruction, and there is
        /// nowhere to put one. The allocator works this out from reuse
        /// constraints and value identity (see
        /// `crate::live_ranges::LiveSpan::is_tied_to`); the kernel only ever
        /// sees the answer, as `SplitUse::cut_before_allowed`, so a bitmask is
        /// all the model needs.
        tied: u16,

        /// The bundle as generated, before clipping.
        source_spans: Vec<(u8, u8)>,
        source_uses: Vec<(u8, u8)>,

        /// The bundle after clipping: what splitting starts from.
        whole: Piece,

        /// What splitting has produced so far, in program order. Starts as
        /// `[whole]`, and every `Split` replaces one entry with two.
        pieces: Vec<Piece>,

        /// The bundles standing in the way.
        parked: Vec<Parked>,

        /// The exponent the next parked bundle's weight takes.
        next_weight: u32,
    }

    impl State {
        fn new() -> Self {
            let mut state = State {
                blocks: BLOCKS,
                tied: 0,
                source_spans: vec![(0, NUM_POINTS)],
                source_uses: vec![(1, 4), (5, 1), (11, 2), (13, 8)],
                whole: Piece {
                    spans: Vec::new(),
                    uses: Vec::new(),
                },
                pieces: Vec::new(),
                parked: Vec::new(),
                next_weight: 0,
            };
            state.rebuild();
            state
        }

        /// Re-clip the source bundle at the block boundaries and throw away
        /// whatever splitting had done to it.
        fn rebuild(&mut self) {
            let spans = clip_to_blocks(&self.source_spans, self.blocks);
            self.whole = Piece {
                spans: spans.iter().map(|&(s, e)| span(s, e)).collect(),
                uses: self
                    .source_uses
                    .iter()
                    .map(|&(p, w)| SplitUse {
                        point: point(p),
                        weight: f32::from(w),
                        cut_before_allowed: oracle_cut_before_allowed(point(p), self.tied),
                    })
                    .collect(),
            };
            self.pieces = vec![self.whole.clone()];
        }
    }

    /// Cut every span at the block boundaries that fall strictly inside it.
    ///
    /// A block starting at instruction `i` puts a boundary at point `2 * i`.
    fn clip_to_blocks(spans: &[(u8, u8)], blocks: u16) -> Vec<(u8, u8)> {
        let mut out = Vec::new();
        for &(start, end) in spans {
            let mut at = start;
            for i in 0..NUM_INSTS {
                if blocks & (1 << i) == 0 {
                    continue;
                }
                let boundary = 2 * i;
                if at < boundary && boundary < end {
                    out.push((at, boundary));
                    at = boundary;
                }
            }
            out.push((at, end));
        }
        out
    }

    /// The cuts `spans` admits, computed the dumb way.
    ///
    /// This ignores rounding entirely: for each adjacent pair it walks every
    /// instruction boundary in the whole program and asks whether that one lies
    /// in the gap.
    fn oracle_between_span_cuts(
        spans: &[Range<LivePoint<u32>>],
        uses: &[SplitUse<u32>],
    ) -> Vec<usize> {
        (1..spans.len())
            .filter(|&k| oracle_gap_admits_a_cut(&spans[k - 1], &spans[k], uses))
            .collect()
    }

    /// May a cut go immediately before a use at `at`?
    ///
    /// This is the rule the allocator applies when it fills in
    /// `SplitUse::cut_before_allowed`, restated over the model's tie bitmask.
    fn oracle_cut_before_allowed(at: LivePoint<u32>, tied: u16) -> bool {
        at.pos() == Position::Early || tied & (1 << at.inst().index()) == 0
    }

    /// Can a cut go in the gap between `before` and `after`, computed the dumb
    /// way?
    ///
    /// Either some instruction boundary falls in the gap, so a move has
    /// somewhere to go, or the gap sits inside an instruction and every use
    /// starting where `after` does says a cut there needs no move.
    fn oracle_gap_admits_a_cut(
        before: &Range<LivePoint<u32>>,
        after: &Range<LivePoint<u32>>,
        uses: &[SplitUse<u32>],
    ) -> bool {
        let boundary_in_gap = (0..=NUM_INSTS).any(|i| {
            let boundary = LivePoint::new(Inst::try_new(usize::from(i)).unwrap(), Position::Early);
            before.end <= boundary && boundary <= after.start
        });
        boundary_in_gap
            || uses
                .iter()
                .filter(|u| u.point == after.start)
                .all(|u| u.cut_before_allowed)
    }

    /// What cutting `piece` at `k` scores in `candidate`, computed the dumb way.
    fn oracle_score(piece: &Piece, parked: &[Parked], candidate: u8, k: usize) -> SplitScore {
        let (before, after) = piece.spans.split_at(k);
        let cut = after[0].start;

        // The suffix as it will really exist: `LiveBundle::split_at_span`
        // widens a suffix that starts mid-instruction back to the instruction
        // boundary, so that is the extent whose interference we must price.
        let mut after = after.to_vec();
        after[0].start = cut.inst_boundary_at_or_before();

        let prefix: f32 = piece
            .uses
            .iter()
            .filter(|u| u.point < cut)
            .map(|u| u.weight)
            .sum();
        let total: f32 = piece.uses.iter().map(|u| u.weight).sum();

        SplitScore::new(
            interference(parked, candidate, before).max(interference(parked, candidate, &after)),
            prefix.min(total - prefix),
        )
    }

    /// The within-span cuts `spans` admits, computed the dumb way.
    ///
    /// For every span, and every adjacent pair of uses inside it, this collects
    /// *all* the points a cut could legally land on by walking every point in
    /// the whole program and asking of each one whether it separates the pair,
    /// then keeps the two ends of that set. The kernel instead rounds each use
    /// to the nearest boundary and never enumerates the middle.
    fn oracle_within_span_cuts(
        spans: &[Range<LivePoint<u32>>],
        uses: &[SplitUse<u32>],
    ) -> Vec<WithinSpanCut<u32>> {
        let mut out = Vec::new();
        for (index, span) in spans.iter().enumerate() {
            let inside: Vec<_> = uses
                .iter()
                .filter(|u| span.start <= u.point && u.point < span.end)
                .collect();
            for pair in inside.windows(2) {
                let (u, v) = (pair[0], pair[1]);
                let legal: Vec<_> = (0..=NUM_POINTS)
                    .map(point)
                    .filter(|at| at.pos() == Position::Early)
                    // Strictly inside the span, so neither piece is empty...
                    .filter(|at| span.start < *at && *at < span.end)
                    // ...and separating the pair, so each piece keeps a use.
                    .filter(|at| u.point < *at && *at <= v.point)
                    .collect();
                if let (Some(&first), Some(&last)) = (legal.first(), legal.last()) {
                    out.push(WithinSpanCut { index, at: first });
                    if last != first {
                        out.push(WithinSpanCut { index, at: last });
                    }
                }
            }
        }
        out
    }

    /// The two halves cutting `spans[index]` at `at` leaves, as plain span lists.
    fn oracle_halves(
        spans: &[Range<LivePoint<u32>>],
        index: usize,
        at: LivePoint<u32>,
    ) -> (Vec<Range<LivePoint<u32>>>, Vec<Range<LivePoint<u32>>>) {
        let mut prefix = spans[..index].to_vec();
        prefix.push(spans[index].start..at);

        let mut suffix = vec![at..spans[index].end];
        suffix.extend(spans[index + 1..].iter().cloned());

        (prefix, suffix)
    }

    /// What cutting `piece` inside a span at `at` scores in `candidate`,
    /// computed the dumb way.
    fn oracle_within_span_score(
        piece: &Piece,
        parked: &[Parked],
        candidate: u8,
        cut: WithinSpanCut<u32>,
    ) -> SplitScore {
        let (before, after) = oracle_halves(&piece.spans, cut.index, cut.at);

        let prefix: f32 = piece
            .uses
            .iter()
            .filter(|u| u.point < cut.at)
            .map(|u| u.weight)
            .sum();
        let total: f32 = piece.uses.iter().map(|u| u.weight).sum();

        SplitScore::new(
            interference(parked, candidate, &before).max(interference(parked, candidate, &after)),
            prefix.min(total - prefix),
        )
    }

    /// Dispatch to the checker for the rung being exercised.
    fn check_split(
        piece: &Piece,
        parked: &[Parked],
        within_span: bool,
    ) -> Result<Option<(Piece, Piece)>, String> {
        if within_span {
            check_split_within_span(piece, parked)
        } else {
            check_split_between_spans(piece, parked)
        }
    }

    /// Check that nothing scores better than `choice`, and that it won the
    /// tie-break documented on `best_split_between_spans`.
    fn check_tie_break<K: Copy + PartialEq + core::fmt::Debug>(
        func: &str,
        spans: &[Range<LivePoint<u32>>],
        expected: &[K],
        choice: SplitChoice<u8, K>,
        score: impl Fn(u8, K) -> SplitScore,
    ) -> Result<(), String> {
        for &cut in expected {
            for candidate in 0..NUM_CANDIDATES {
                let other = score(candidate, cut);
                if other > choice.score {
                    return Err(format!(
                        "`{func}` chose {choice:?} for {spans:?}, but cutting at {cut:?} for \
                         candidate {candidate} scores {other:?}, which is better",
                    ));
                }
            }
        }

        let cut_score = |cut| (0..NUM_CANDIDATES).map(|c| score(c, cut)).max().unwrap();
        let run_start = expected
            .iter()
            .position(|&cut| cut_score(cut) == choice.score)
            .unwrap();
        let run_len = expected[run_start..]
            .iter()
            .take_while(|&&cut| cut_score(cut) == choice.score)
            .count();
        let middle = expected[run_start + (run_len - 1) / 2];
        if choice.cut != middle {
            return Err(format!(
                "`{func}` chose {choice:?} for {spans:?}, but the middle of the first run of tied \
                 cuts, {:?}, is {middle:?}",
                &expected[run_start..run_start + run_len],
            ));
        }
        let earliest = (0..NUM_CANDIDATES)
            .find(|&candidate| score(candidate, middle) == choice.score)
            .unwrap();
        if choice.candidate != earliest {
            return Err(format!(
                "`{func}` chose {choice:?} for {spans:?}, but candidate {earliest} ties it at the \
                 same cut and comes first",
            ));
        }
        Ok(())
    }

    /// Check everything `best_split_within_span` promises about `piece`, and
    /// return the two halves it chose, if it chose any.
    fn check_split_within_span(
        piece: &Piece,
        parked: &[Parked],
    ) -> Result<Option<(Piece, Piece)>, String> {
        let spans = &piece.spans;
        let uses = &piece.uses;

        let actual: Vec<_> = within_span_cuts(spans, uses).collect();
        let expected = oracle_within_span_cuts(spans, uses);
        if actual != expected {
            return Err(format!(
                "`within_span_cuts({spans:?}, {uses:?})` gives {actual:?} but should give \
                 {expected:?}",
            ));
        }

        for cut in &actual {
            // Every cut lands on an instruction boundary, because a move cannot
            // go between an instruction's uses and its defs.
            if cut.at.pos() != Position::Early {
                return Err(format!(
                    "`within_span_cuts({spans:?}, {uses:?})` gives {cut:?}, which is not on an \
                     instruction boundary",
                ));
            }
            // And strictly inside its span, so neither piece comes out empty.
            let span = &spans[cut.index];
            if !(span.start < cut.at && cut.at < span.end) {
                return Err(format!(
                    "`within_span_cuts({spans:?}, {uses:?})` gives {cut:?}, which is not inside \
                     {span:?}",
                ));
            }
        }
        for pair in actual.windows(2) {
            if (pair[0].index, pair[0].at) >= (pair[1].index, pair[1].at) {
                return Err(format!(
                    "`within_span_cuts({spans:?}, {uses:?})` gives {actual:?}, unordered",
                ));
            }
        }

        // There is a cut exactly when some span holds two uses on distinct
        // instructions -- nothing further can rule one out, because the
        // boundary just after the first of the two and the one just before the
        // second both land inside the span. `split_within_span` rejects a
        // bundle up front on precisely this test rather than filling its
        // scratch buffers to be told the same thing, so the two have to agree.
        let two_uses_apart = spans.iter().any(|span| {
            let mut inside = uses
                .iter()
                .filter(|u| span.start <= u.point && u.point < span.end);
            match (inside.next(), inside.next_back()) {
                (Some(first), Some(last)) => first.point.inst() != last.point.inst(),
                _ => false,
            }
        });
        if two_uses_apart != !actual.is_empty() {
            return Err(format!(
                "`within_span_cuts({spans:?}, {uses:?})` gives {actual:?}, but a span holding \
                 two uses on distinct instructions is {two_uses_apart}",
            ));
        }

        // `HalfSpan` presents the clipped span in its place among the whole
        // ones, and presents all of them.
        for cut in &actual {
            let (want_prefix, want_suffix) = oracle_halves(spans, cut.index, cut.at);
            let halves = [
                (
                    "prefix",
                    HalfSpan::prefix(spans, cut.index, cut.at),
                    want_prefix,
                ),
                (
                    "suffix",
                    HalfSpan::suffix(spans, cut.index, cut.at),
                    want_suffix,
                ),
            ];
            for (which, half, want) in halves {
                let got: Vec<_> = half.iter().collect();
                if got != want || half.len() != want.len() {
                    return Err(format!(
                        "the {which} `HalfSpan` of {cut:?} over {spans:?} is {got:?} with length \
                         {}, but should be {want:?}",
                        half.len(),
                    ));
                }
            }
        }

        let choice = best_split_within_span(spans, uses, 0..NUM_CANDIDATES, |candidate, half| {
            let half: Vec<_> = half.iter().collect();
            interference(parked, candidate, &half)
        });

        let choice = match choice {
            None => {
                if !expected.is_empty() {
                    return Err(format!(
                        "`best_split_within_span` found no cut of {spans:?}, but {expected:?} \
                         are all admissible",
                    ));
                }
                return Ok(None);
            }
            Some(choice) => {
                if expected.is_empty() {
                    return Err(format!(
                        "`best_split_within_span` chose {choice:?} for {spans:?}, which admits \
                         no cut",
                    ));
                }
                choice
            }
        };

        if !expected.contains(&choice.cut) {
            return Err(format!(
                "`best_split_within_span` chose {:?} for {spans:?}, which is not one of the \
                 admissible {expected:?}",
                choice.cut,
            ));
        }
        if choice.candidate >= NUM_CANDIDATES {
            return Err(format!(
                "`best_split_within_span` chose candidate {}, which does not exist",
                choice.candidate,
            ));
        }

        // The score is what the oracle computes for that same cut and
        // candidate.
        let scored = oracle_within_span_score(piece, parked, choice.candidate, choice.cut);
        if choice.score.normalized() != scored.normalized() {
            return Err(format!(
                "`best_split_within_span` scored {:?} at {choice:?}, but the oracle scores {:?}",
                choice.score.normalized(),
                scored.normalized(),
            ));
        }

        check_tie_break(
            "best_split_within_span",
            spans,
            &expected,
            choice,
            |candidate, cut| oracle_within_span_score(piece, parked, candidate, cut),
        )?;

        // The halves partition the piece. They hold one more span between them
        // than the piece did, because one span was divided, but the same
        // instructions and the same uses -- and each half strictly fewer
        // instructions than the piece, which is what makes splitting terminate.
        let (before, after) = oracle_halves(spans, choice.cut.index, choice.cut.at);
        let at = choice.cut.at;
        let prefix = Piece {
            spans: before,
            uses: uses.iter().filter(|u| u.point < at).copied().collect(),
        };
        let suffix = Piece {
            spans: after,
            uses: uses.iter().filter(|u| u.point >= at).copied().collect(),
        };

        for half in [&prefix, &suffix] {
            if half.len_insts() >= piece.len_insts() {
                return Err(format!(
                    "cutting {spans:?} at {:?} leaves a half covering {} of its {} \
                     instructions, so splitting would not terminate",
                    choice.cut,
                    half.len_insts(),
                    piece.len_insts(),
                ));
            }
            if half.uses.is_empty() {
                return Err(format!(
                    "cutting {spans:?} at {:?} leaves a half with no uses, so it was not cut \
                     between two uses",
                    choice.cut,
                ));
            }
        }
        if prefix.spans.len() + suffix.spans.len() != spans.len() + 1 {
            return Err(format!(
                "cutting {spans:?} at {:?} creates or loses a span",
                choice.cut,
            ));
        }
        if prefix.uses.len() + suffix.uses.len() != uses.len() {
            return Err(format!(
                "cutting {spans:?} at {:?} creates or loses a use",
                choice.cut,
            ));
        }
        if prefix.len_insts() + suffix.len_insts() != piece.len_insts() {
            return Err(format!(
                "cutting {spans:?} at {:?} creates or loses an instruction",
                choice.cut,
            ));
        }

        Ok(Some((prefix, suffix)))
    }

    /// Check everything `best_split_between_spans` promises about `piece`, and return
    /// the two halves it chose, if it chose any.
    fn check_split_between_spans(
        piece: &Piece,
        parked: &[Parked],
    ) -> Result<Option<(Piece, Piece)>, String> {
        let spans = &piece.spans;

        // The admissible cuts are exactly the ones the oracle finds, in
        // ascending order, and neither half of any of them is span-less.
        let uses = &piece.uses;
        let actual: Vec<usize> = between_span_cuts(spans, uses).collect();
        let expected = oracle_between_span_cuts(spans, uses);
        if actual != expected {
            return Err(format!(
                "`between_span_cuts({spans:?}, {uses:?})` gives {actual:?} but should give \
                 {expected:?}",
            ));
        }
        for pair in actual.windows(2) {
            if pair[0] >= pair[1] {
                return Err(format!(
                    "`between_span_cuts({spans:?}, {uses:?})` gives {actual:?}, unordered"
                ));
            }
        }
        for &cut in &actual {
            if !(1 <= cut && cut < spans.len()) {
                return Err(format!(
                    "`between_span_cuts({spans:?}, {uses:?})` gives {cut}, which leaves a half \
                     span-less",
                ));
            }
        }

        let choice =
            best_split_between_spans(spans, &piece.uses, 0..NUM_CANDIDATES, |candidate, half| {
                let half: Vec<_> = half.iter().collect();
                interference(parked, candidate, &half)
            });

        let choice = match choice {
            None => {
                if !expected.is_empty() {
                    return Err(format!(
                        "`best_split_between_spans` found no cut of {spans:?}, but {expected:?} are all \
                         admissible",
                    ));
                }
                return Ok(None);
            }
            Some(choice) => {
                if expected.is_empty() {
                    return Err(format!(
                        "`best_split_between_spans` chose {choice:?} for {spans:?}, which admits no cut",
                    ));
                }
                choice
            }
        };

        if !expected.contains(&choice.cut) {
            return Err(format!(
                "`best_split_between_spans` chose {:?} for {spans:?}, which is not one of the admissible \
                 {expected:?}",
                choice.cut,
            ));
        }
        if choice.candidate >= NUM_CANDIDATES {
            return Err(format!(
                "`best_split_between_spans` chose candidate {}, which does not exist",
                choice.candidate,
            ));
        }

        // The score is what the oracle computes for that same cut and
        // candidate.
        let scored = oracle_score(piece, parked, choice.candidate, choice.cut);
        if choice.score.normalized() != scored.normalized() {
            return Err(format!(
                "`best_split_between_spans` scored {:?} at {choice:?}, but the oracle scores {:?}",
                choice.score.normalized(),
                scored.normalized(),
            ));
        }

        check_tie_break(
            "best_split_between_spans",
            spans,
            &expected,
            choice,
            |candidate, cut| oracle_score(piece, parked, candidate, cut),
        )?;

        // The halves partition the piece: every span in exactly one, order
        // preserved, both non-empty and each strictly smaller than the piece.
        let k = choice.cut;
        let (before, after) = spans.split_at(k);
        let cut = after[0].start;
        let prefix = Piece {
            spans: before.to_vec(),
            uses: piece
                .uses
                .iter()
                .filter(|u| u.point < cut)
                .copied()
                .collect(),
        };
        let suffix = Piece {
            spans: after.to_vec(),
            uses: piece
                .uses
                .iter()
                .filter(|u| u.point >= cut)
                .copied()
                .collect(),
        };

        for half in [&prefix, &suffix] {
            if half.spans.is_empty() {
                return Err(format!(
                    "cutting {spans:?} at {k} leaves a half with no spans"
                ));
            }
            if half.spans.len() >= spans.len() {
                return Err(format!(
                    "cutting {spans:?} at {k} leaves a half with {} of its {} spans, so \
                     splitting would not terminate",
                    half.spans.len(),
                    spans.len(),
                ));
            }
        }
        if prefix.spans.len() + suffix.spans.len() != spans.len() {
            return Err(format!("cutting {spans:?} at {k} creates or loses a span"));
        }
        if prefix.uses.len() + suffix.uses.len() != piece.uses.len() {
            return Err(format!("cutting {spans:?} at {k} creates or loses a use"));
        }
        if prefix.len_insts() + suffix.len_insts() != piece.len_insts() {
            return Err(format!(
                "cutting {spans:?} at {k} creates or loses an instruction"
            ));
        }

        Ok(Some((prefix, suffix)))
    }

    /// The cuts shredding `spans` into minimal pieces, computed the dumb way.
    ///
    /// Where the kernel works forwards from each use to the two boundaries
    /// around it, this walks every point in the whole program and asks of each
    /// one whether it is a boundary of some use's instruction. Ascending order
    /// and the absence of duplicates fall out of the enumeration rather than
    /// being arranged, which is exactly what makes it worth comparing against.
    fn oracle_minimal_cuts(
        spans: &[Range<LivePoint<u32>>],
        uses: &[SplitUse<u32>],
    ) -> Vec<Cut<u32>> {
        let mut out = Vec::new();
        for (index, span) in spans.iter().enumerate() {
            if index > 0 && oracle_gap_admits_a_cut(&spans[index - 1], span, uses) {
                out.push(Cut::BetweenSpans(index));
            }

            for at in (0..=NUM_POINTS).map(point) {
                if at.pos() != Position::Early {
                    continue;
                }
                // Strictly inside the span, so neither piece comes out empty.
                if !(span.start < at && at < span.end) {
                    continue;
                }
                // And bounding the instruction of some use of the bundle, so
                // that it carves that use out into an instruction of its own.
                // Note that the use need not be one of this span's own: see
                // `minimal_cuts_within_span`.
                let bounds_a_use = uses.iter().any(|u| {
                    u.point.inst_boundary_at_or_before() == at
                        || u.point.inst_boundary_after() == at
                });
                if bounds_a_use {
                    out.push(Cut::WithinSpan(WithinSpanCut { index, at }));
                }
            }
        }
        out
    }

    /// A sort key placing a cut in program order.
    ///
    /// The gap before span `k` comes after everything inside span `k - 1` and
    /// before everything inside span `k`, which the odd and even halves of the
    /// first component arrange; `None` sorting before `Some` puts a gap ahead
    /// of the points within the span that follows it.
    fn minimal_cut_key(cut: Cut<u32>) -> (usize, Option<LivePoint<u32>>) {
        match cut {
            Cut::BetweenSpans(k) => (2 * k, None),
            Cut::WithinSpan(WithinSpanCut { index, at }) => (2 * index + 1, Some(at)),
        }
    }

    /// Cut `piece` into the pieces `cuts` describes.
    ///
    /// Works back to front, exactly as `split_into_minimal_or_spill` does, so
    /// that this exercises the same index arithmetic the allocator relies on.
    fn apply_minimal_cuts(piece: &Piece, cuts: &[Cut<u32>]) -> Vec<Piece> {
        let mut spans = piece.spans.clone();
        let mut pieces = Vec::new();

        for cut in cuts.iter().rev() {
            let suffix = match *cut {
                Cut::BetweenSpans(k) => spans.split_off(k),
                Cut::WithinSpan(WithinSpanCut { index, at }) => {
                    let end = spans[index].end;
                    spans[index].end = at;
                    let mut suffix = vec![at..end];
                    suffix.extend(spans.drain(index + 1..));
                    suffix
                }
            };
            pieces.push(suffix);
        }
        pieces.push(spans);
        pieces.reverse();

        pieces
            .into_iter()
            .map(|spans| Piece {
                uses: piece
                    .uses
                    .iter()
                    .filter(|u| spans.iter().any(|s| s.start <= u.point && u.point < s.end))
                    .copied()
                    .collect(),
                spans,
            })
            .collect()
    }

    /// Check everything `minimal_cuts` promises about `piece`, and return the
    /// pieces it shreds it into.
    fn check_split_into_minimal(piece: &Piece) -> Result<Vec<Piece>, String> {
        let spans = &piece.spans;
        let uses = &piece.uses;

        let actual: Vec<_> = minimal_cuts(spans, uses).collect();
        let expected = oracle_minimal_cuts(spans, uses);
        if actual != expected {
            return Err(format!(
                "`minimal_cuts({spans:?}, {uses:?})` gives {actual:?} but should give \
                 {expected:?}",
            ));
        }

        for pair in actual.windows(2) {
            if minimal_cut_key(pair[0]) >= minimal_cut_key(pair[1]) {
                return Err(format!(
                    "`minimal_cuts({spans:?}, {uses:?})` gives {actual:?}, which is not in \
                     ascending order without duplicates",
                ));
            }
        }

        // Every cut satisfies the preconditions of the split primitive that
        // will be handed it.
        for &cut in &actual {
            match cut {
                Cut::BetweenSpans(k) => {
                    if !(1 <= k && k < spans.len()) {
                        return Err(format!(
                            "`minimal_cuts({spans:?}, {uses:?})` gives {cut:?}, which leaves a \
                             piece span-less",
                        ));
                    }
                }
                Cut::WithinSpan(WithinSpanCut { index, at }) => {
                    // A move cannot go between an instruction's uses and its
                    // defs, so a cut has to land on an instruction boundary...
                    if at.pos() != Position::Early {
                        return Err(format!(
                            "`minimal_cuts({spans:?}, {uses:?})` gives {cut:?}, which is not on \
                             an instruction boundary",
                        ));
                    }
                    // ...and strictly inside its span, or a piece comes out
                    // empty.
                    let span = &spans[index];
                    if !(span.start < at && at < span.end) {
                        return Err(format!(
                            "`minimal_cuts({spans:?}, {uses:?})` gives {cut:?}, which is not \
                             inside {span:?}",
                        ));
                    }
                }
            }
        }

        // `is_minimal_bundle` calls a bundle minimal exactly when there is
        // nothing left to cut, which is what lets the allocator ask the cheap
        // question instead of running `minimal_cuts` to find out. Both
        // directions matter: calling a cuttable bundle minimal spills something
        // that could have been split, and calling an uncuttable one splittable
        // sends it around the loop forever.
        let len_cuttable_gaps = oracle_between_span_cuts(spans, uses).len();
        let is_minimal =
            is_minimal_bundle(len_cuttable_gaps, uses.len(), piece.len_distinct_insts());
        if is_minimal != actual.is_empty() {
            return Err(format!(
                "`is_minimal_bundle` says {spans:?} with {uses:?} is minimal = {is_minimal}, but \
                 `minimal_cuts` gives {actual:?}",
            ));
        }

        let pieces = apply_minimal_cuts(piece, &actual);

        // The pieces partition the bundle: one more piece than there were cuts,
        // holding one more span between them for each span that was divided,
        // and the same uses over the same instructions.
        if pieces.len() != actual.len() + 1 {
            return Err(format!(
                "cutting {spans:?} at {actual:?} gives {} pieces, not {}",
                pieces.len(),
                actual.len() + 1,
            ));
        }
        let divided = actual
            .iter()
            .filter(|c| matches!(c, Cut::WithinSpan(_)))
            .count();
        let num_spans: usize = pieces.iter().map(|p| p.spans.len()).sum();
        if num_spans != spans.len() + divided {
            return Err(format!(
                "cutting {spans:?} at {actual:?} gives {num_spans} spans, not {}",
                spans.len() + divided,
            ));
        }
        let num_uses: usize = pieces.iter().map(|p| p.uses.len()).sum();
        if num_uses != uses.len() {
            return Err(format!(
                "cutting {spans:?} at {actual:?} creates or loses a use",
            ));
        }
        let num_insts: usize = pieces.iter().map(|p| p.len_insts()).sum();
        if num_insts != piece.len_insts() {
            return Err(format!(
                "cutting {spans:?} at {actual:?} creates or loses an instruction",
            ));
        }

        for p in &pieces {
            if p.spans.is_empty() || p.spans.iter().any(|s| s.start >= s.end) {
                return Err(format!(
                    "cutting {spans:?} at {actual:?} leaves an empty piece {:?}",
                    p.spans,
                ));
            }

            // One pass already reaches a fixed point, which is what lets the
            // allocator hand every piece straight back to the same rung and
            // know it will spill rather than split again.
            let again: Vec<_> = minimal_cuts(&p.spans, &p.uses).collect();
            if !again.is_empty() {
                return Err(format!(
                    "cutting {spans:?} at {actual:?} leaves {:?}, which `minimal_cuts` would \
                     cut again at {again:?}",
                    p.spans,
                ));
            }

            // A piece that holds a use holds it alone, in an instruction of its
            // own: that is what "minimal" is for. Note that a piece can still
            // reach that one instruction through two spans, when they touch at
            // a `Late` point that nothing can be cut at.
            if !p.uses.is_empty() {
                let (first, last) = p.inst_range();
                if first != last {
                    return Err(format!(
                        "cutting {spans:?} at {actual:?} leaves {:?}, which holds uses across \
                         instructions {first} through {last}",
                        p.spans,
                    ));
                }
            }
        }

        Ok(pieces)
    }

    /// Fuse spans that touch, so that a span and the two pieces it was divided
    /// into compare equal.
    fn merge_adjacent(spans: &[Range<LivePoint<u32>>]) -> Vec<Range<LivePoint<u32>>> {
        let mut out: Vec<Range<LivePoint<u32>>> = Vec::new();
        for span in spans {
            match out.last_mut() {
                Some(last) if last.end == span.start => last.end = span.end,
                _ => out.push(span.clone()),
            }
        }
        out
    }

    /// The pieces still cover exactly the bundle splitting started from.
    ///
    /// Compared after fusing touching spans, because a within-span split leaves
    /// two spans where the bundle had one; every other way of creating or
    /// losing coverage still shows up here.
    fn check_pieces_partition(state: &State) -> Result<(), String> {
        let spans: Vec<_> = state
            .pieces
            .iter()
            .flat_map(|p| p.spans.iter().cloned())
            .collect();
        let (spans, whole) = (merge_adjacent(&spans), merge_adjacent(&state.whole.spans));
        if spans != whole {
            return Err(format!(
                "the pieces cover {spans:?}, but the bundle they came from covers {whole:?}",
            ));
        }
        let num_uses: usize = state.pieces.iter().map(|p| p.uses.len()).sum();
        if num_uses != state.whole.uses.len() {
            return Err(format!(
                "the pieces hold {num_uses} uses, but the bundle they came from holds {}",
                state.whole.uses.len(),
            ));
        }
        Ok(())
    }

    #[derive(Clone, Debug, Mutate)]
    enum Op {
        /// Cut a piece at the best point, replacing it with its two halves.
        Split {
            piece: u8,

            /// Which rung to cut on: within one of the piece's spans, or
            /// between two of them.
            within_span: bool,
        },

        /// Shred a piece into every minimal piece its shape allows, replacing
        /// it with all of them. The bottom rung, which unlike the two above it
        /// makes every cut it can rather than picking the best one.
        SplitIntoMinimal {
            piece: u8,
        },

        /// Park a copy of a piece in a candidate, so that it stands in the way.
        Assign {
            piece: u8,
            candidate: u8,
        },

        /// Free a candidate. The landscape must revert to what it was.
        Evict {
            candidate: u8,
        },

        /// Re-clip the spans, reshaping the list of admissible cuts under an
        /// otherwise identical bundle.
        SetBlockBoundaries {
            mask: u16,
        },

        /// Retie the bundle, taking gaps that sit inside an instruction in and
        /// out of play without moving a single span or use.
        SetTies {
            mask: u16,
        },

        /// Start over from a different bundle, keeping the landscape.
        Rebuild {
            spans: Vec<(u8, u8)>,
            uses: Vec<(u8, u8)>,
        },

        Reset,
    }

    impl Default for Op {
        fn default() -> Self {
            Op::Split {
                piece: 0,
                within_span: false,
            }
        }
    }

    /// Ensure the spans are ascending, non-overlapping, non-empty and in range.
    fn fixup_spans(spans: &mut Vec<(u8, u8)>) {
        spans.truncate(MAX_SPANS);

        for (start, end) in spans.iter_mut() {
            *start %= NUM_POINTS;
            if !(*start < *end && *end <= NUM_POINTS) {
                *end = *start + 1 + (*end % (NUM_POINTS - *start));
            }
        }

        spans.sort_unstable();

        let mut previous_end = 0;
        spans.retain(|&(start, end)| {
            let keep = start >= previous_end;
            if keep {
                previous_end = end;
            }
            keep
        });

        if spans.is_empty() {
            spans.push((0, 1));
        }
    }

    /// Ensure every use lies within some span, and that they are sorted.
    ///
    /// Placing them against the *unclipped* spans is enough: clipping only
    /// subdivides, so a point inside a span before it is inside one after it.
    fn fixup_uses(uses: &mut Vec<(u8, u8)>, spans: &[(u8, u8)]) {
        uses.truncate(MAX_USES);

        let covered: u8 = spans.iter().map(|&(start, end)| end - start).sum();
        for (at, _weight) in uses.iter_mut() {
            if spans.iter().any(|&(start, end)| (start..end).contains(at)) {
                continue;
            }
            let mut offset = *at % covered;
            for &(start, end) in spans {
                if offset < end - start {
                    *at = start + offset;
                    break;
                }
                offset -= end - start;
            }
        }

        uses.sort_unstable();
    }

    fn fixup_ops(ops: &mut Vec<Op>) {
        ops.truncate(MAX_OPS);
        for op in ops.iter_mut() {
            match op {
                Op::Split { .. } | Op::SplitIntoMinimal { .. } | Op::Reset => {}
                Op::Assign { candidate, .. } | Op::Evict { candidate } => {
                    *candidate %= NUM_CANDIDATES;
                }
                Op::SetBlockBoundaries { mask } => {
                    // Instruction zero always starts a block, and nothing past
                    // the end of the program starts one.
                    *mask = (*mask | 1) & ((1 << NUM_INSTS) - 1);
                }
                Op::SetTies { mask } => {
                    *mask &= (1 << NUM_INSTS) - 1;
                }
                Op::Rebuild { spans, uses } => {
                    fixup_spans(spans);
                    fixup_uses(uses, spans);
                }
            }
        }
    }

    fn rebuild(spans: &[(u8, u8)], uses: &[(u8, u8)]) -> Op {
        Op::Rebuild {
            spans: spans.to_vec(),
            uses: uses.to_vec(),
        }
    }

    fn blocks(insts: &[u8]) -> Op {
        Op::SetBlockBoundaries {
            mask: insts.iter().fold(1, |mask, &i| mask | (1 << i)),
        }
    }

    fn ties(insts: &[u8]) -> Op {
        Op::SetTies {
            mask: insts.iter().fold(0, |mask, &i| mask | (1 << i)),
        }
    }

    fn split(piece: u8) -> Op {
        Op::Split {
            piece,
            within_span: false,
        }
    }

    fn split_within(piece: u8) -> Op {
        Op::Split {
            piece,
            within_span: true,
        }
    }

    fn assign(piece: u8, candidate: u8) -> Op {
        Op::Assign { piece, candidate }
    }

    fn split_minimal(piece: u8) -> Op {
        Op::SplitIntoMinimal { piece }
    }

    fn seeds() -> Vec<Vec<Op>> {
        // Every seed pins the block partition first, because clipping decides
        // which cuts exist and the default partition would cut most of these
        // bundles into a different shape than the one they are about.
        let one_block = blocks(&[]);

        let mut seeds = vec![
            // One span and no gap, so there is nothing to cut. The bail-out
            // `split_between_spans` depends on to terminate.
            vec![one_block.clone(), rebuild(&[(0, 6)], &[(1, 3)]), split(0)],
            // Two spans that merely touch at `(i, Late)`, with the use that
            // starts the second tied to the first. A cut there would demand a
            // move in the middle of the instruction, so there is none: the
            // known gap that `split_into_minimal_or_spill` has to cover.
            vec![
                one_block.clone(),
                ties(&[3]),
                rebuild(&[(5, 7), (7, 9)], &[(5, 1), (7, 1)]),
                split(0),
            ],
            // The very same shape untied, which *does* admit a cut. The caller
            // widens the suffix back to `(3, Early)` afterwards.
            vec![
                one_block.clone(),
                rebuild(&[(5, 7), (7, 9)], &[(5, 1), (7, 1)]),
                split(0),
            ],
            // Two spans meeting exactly at an `Early` point, as they do at a
            // block boundary. There *is* a cut here.
            vec![
                one_block.clone(),
                rebuild(&[(4, 6), (6, 9)], &[(4, 1), (7, 1)]),
                split(0),
            ],
            // The same bundle, arrived at by clipping rather than by hand: a
            // block boundary lands inside one span and cuts it in two.
            vec![
                blocks(&[3]),
                rebuild(&[(4, 9)], &[(4, 1), (7, 1)]),
                split(0),
            ],
            // A gap of exactly one instruction, and a gap running from
            // `(i, Late)` to `(i + 1, Late)`: the two ends of the admission
            // test, one just wide enough and one that skips a boundary.
            vec![
                one_block.clone(),
                rebuild(&[(2, 4), (6, 8)], &[(2, 1), (6, 1)]),
                split(0),
            ],
            vec![
                one_block.clone(),
                rebuild(&[(2, 3), (5, 7)], &[(2, 1), (5, 1)]),
                split(0),
            ],
            // Three spans whose first and third gaps admit a cut but whose
            // middle one does not, so an index has to stay attached to its own
            // gap across a skip. The tie is what closes the middle gap; without
            // it all three would be cuttable and there would be no skip.
            vec![
                one_block.clone(),
                ties(&[2]),
                rebuild(
                    &[(0, 2), (4, 5), (5, 7), (9, 11)],
                    &[(0, 1), (4, 1), (5, 1), (9, 1)],
                ),
                split(0),
            ],
            // A half with a hole, and one bundle parked in that hole for every
            // candidate. The hole is not part of the half, so none of them is
            // in the way and the cut that opens the hole is free; pricing the
            // half by the range enclosing it would charge for all three and
            // send splitting to the worse-balanced cut instead.
            vec![
                one_block.clone(),
                rebuild(&[(3, 5)], &[(3, 1)]),
                assign(0, 0),
                assign(0, 1),
                assign(0, 2),
                rebuild(&[(0, 2), (6, 8), (12, 14)], &[(6, 4), (12, 4)]),
                split(0),
            ],
            // One parked bundle overlapping two spans of the same half. It is
            // one bundle to displace, so it is charged once.
            vec![
                one_block.clone(),
                rebuild(&[(0, 3), (5, 8), (12, 14)], &[(0, 1), (5, 1), (12, 1)]),
                assign(0, 1),
                rebuild(&[(0, 3), (5, 8), (12, 14)], &[(0, 1), (5, 1), (12, 1)]),
                split(0),
            ],
            // One candidate congested only in the prefix and another only in
            // the suffix. Taking the `max` over the halves is what makes the
            // uncongested one win; a sum would rank them the same.
            vec![
                one_block.clone(),
                rebuild(&[(0, 4)], &[(0, 1)]),
                assign(0, 0),
                rebuild(&[(10, 14)], &[(10, 1)]),
                assign(0, 1),
                rebuild(&[(0, 4), (10, 14)], &[(0, 1), (10, 1)]),
                split(0),
            ],
            // Every candidate blanketed by one bundle of its own, so all three
            // are in the way of both halves at every cut and none of them can
            // score zero. Taking the `max` over the halves rather than the sum
            // is what keeps the winner's score the weight of one bundle.
            vec![
                one_block.clone(),
                rebuild(&[(0, 16)], &[(0, 1)]),
                assign(0, 2),
                assign(0, 0),
                assign(0, 1),
                rebuild(&[(0, 2), (4, 6), (8, 10), (12, 14)], &[(0, 1), (8, 1)]),
                split(0),
            ],
            // Every use in one span, so the other half comes out use-less.
            // That is a legal cut and must be chosen when it prices best, not
            // filtered out as degenerate.
            vec![
                one_block.clone(),
                rebuild(&[(0, 2), (4, 6), (8, 10)], &[(0, 5), (1, 5)]),
                split(0),
            ],
            // No interference anywhere, so every candidate ties on the primary
            // key and `balance` alone decides. Without it the earliest-wins
            // tie-break would peel off just the first span, round after round.
            vec![
                one_block.clone(),
                rebuild(
                    &[(0, 2), (4, 6), (8, 10), (12, 14)],
                    &[(0, 1), (4, 1), (8, 1), (12, 1)],
                ),
                split(0),
                split(0),
                split(1),
            ],
            // A tie on both keys: the earliest cut has to win.
            vec![
                one_block.clone(),
                rebuild(&[(0, 2), (4, 6), (8, 10)], &[]),
                split(0),
            ],
            // Parking and then freeing: the landscape must revert, so the same
            // bundle splits the same way before and after.
            vec![
                one_block.clone(),
                rebuild(&[(0, 4)], &[(0, 1)]),
                assign(0, 0),
                rebuild(&[(0, 4), (8, 12)], &[(0, 1), (8, 1)]),
                split(0),
                Op::Evict { candidate: 0 },
                rebuild(&[(0, 4), (8, 12)], &[(0, 1), (8, 1)]),
                split(0),
            ],
            // Repeated splitting down to uncuttable pieces, under the default
            // block partition, with something in the way the whole time.
            vec![
                rebuild(&[(0, NUM_POINTS)], &[(1, 3), (5, 1), (11, 2), (13, 8)]),
                assign(0, 0),
                split(0),
                split(0),
                split(1),
                split(2),
            ],
            // One span holding a single use. Nothing to cut between: the
            // bail-out `split_within_span` depends on to fall through.
            vec![
                one_block.clone(),
                rebuild(&[(0, 6)], &[(2, 1)]),
                split_within(0),
            ],
            // Two uses on the same instruction, one at each position. No move
            // can go between an instruction's uses and its defs, so there is
            // still no cut even though there are two uses.
            vec![
                one_block.clone(),
                rebuild(&[(0, 8)], &[(4, 1), (5, 1)]),
                split_within(0),
            ],
            // Two uses on adjacent instructions. The two ends of the gap are
            // the same point, so it yields exactly one cut, not a duplicate.
            vec![
                one_block.clone(),
                rebuild(&[(2, 10)], &[(4, 1), (6, 1)]),
                split_within(0),
            ],
            // A use at `(i, Late)` and one at `(j, Early)`: both ends have to
            // round outward, away from the use, to reach a boundary.
            vec![
                one_block.clone(),
                rebuild(&[(0, 12)], &[(3, 1), (8, 1)]),
                split_within(0),
            ],
            // A use sitting exactly on the span's first point and another on
            // its last. The earliest cut may not land on `span.start` and the
            // latest may not land on `span.end`, or a piece comes out empty.
            vec![
                one_block.clone(),
                rebuild(&[(4, 11)], &[(4, 1), (10, 1)]),
                split_within(0),
            ],
            // Three uses, so two gaps, so up to four cuts -- and the middle use
            // belongs to both gaps. The running use-weight cursor has to stay
            // in step as the cuts sweep across it.
            vec![
                one_block.clone(),
                rebuild(&[(0, 14)], &[(1, 1), (6, 4), (12, 1)]),
                split_within(0),
            ],
            // Uses spread over several spans. Only the pairs *within* a span
            // count; the gap between the last use of one span and the first of
            // the next is `split_between_spans`' business.
            vec![
                one_block.clone(),
                rebuild(
                    &[(0, 4), (6, 8), (10, 15)],
                    &[(0, 1), (2, 1), (6, 1), (11, 1), (14, 1)],
                ),
                split_within(0),
            ],
            // Uses only in the last span, so the first spans contribute no
            // cuts at all and the contiguous run of uses belonging to the
            // divided span does not start at zero.
            vec![
                one_block.clone(),
                rebuild(&[(0, 2), (4, 6), (8, 15)], &[(8, 1), (14, 1)]),
                split_within(0),
            ],
            // A bundle parked across the middle of the span, in one candidate
            // only. Cutting around it is the whole point of this rung: the
            // clipped half must not be charged for the part of the span it no
            // longer covers, or every candidate prices the same.
            vec![
                one_block.clone(),
                rebuild(&[(6, 10)], &[(6, 1)]),
                assign(0, 1),
                rebuild(&[(0, 16)], &[(1, 4), (14, 4)]),
                split_within(0),
            ],
            // The same, but with the obstruction covering the whole span in
            // every candidate: no cut escapes it, so `max` over the halves
            // keeps the score at one bundle's weight rather than doubling it.
            vec![
                one_block.clone(),
                rebuild(&[(0, 16)], &[(0, 1)]),
                assign(0, 2),
                assign(0, 0),
                assign(0, 1),
                rebuild(&[(0, 16)], &[(1, 1), (14, 1)]),
                split_within(0),
            ],
            // All the weight on one side, so `balance` is the same at every
            // cut and interference alone decides.
            vec![
                one_block.clone(),
                rebuild(&[(0, 16)], &[(1, 8), (2, 8), (14, 1)]),
                split_within(0),
            ],
            // Cutting within a span and then between spans, and the reverse:
            // the two rungs have to compose, since a bundle reaching the
            // second one has already been through the first.
            vec![
                one_block.clone(),
                rebuild(&[(0, 6), (8, 16)], &[(0, 1), (4, 1), (8, 1), (14, 1)]),
                split_within(0),
                split(1),
            ],
            vec![
                one_block.clone(),
                rebuild(&[(0, 6), (8, 16)], &[(0, 1), (4, 1), (8, 1), (14, 1)]),
                split(0),
                split_within(1),
                split_within(0),
            ],
            // Repeated within-span splitting down to uncuttable pieces, under
            // the default block partition, with something in the way.
            vec![
                rebuild(&[(0, NUM_POINTS)], &[(1, 3), (5, 1), (11, 2), (13, 8)]),
                assign(0, 0),
                split_within(0),
                split_within(0),
                split_within(1),
                split_within(2),
            ],
            // The bottom rung on its own, against the same bundle: one pass
            // shreds what the rung above it took four to get through.
            vec![
                rebuild(&[(0, NUM_POINTS)], &[(1, 3), (5, 1), (11, 2), (13, 8)]),
                split_minimal(0),
            ],
            // Two spans touching at `(i, Late)`, the case the rungs above
            // cannot cut. The bottom rung carves the uses out but leaves the
            // two spans that meet inside instruction three together, because
            // no move can go there.
            vec![
                one_block.clone(),
                rebuild(&[(5, 7), (7, 9)], &[(5, 1), (7, 1)]),
                split_minimal(0),
                split_minimal(0),
                split_minimal(1),
                split_minimal(2),
            ],
            // A use-free span, and a span of one instruction: the two shapes
            // the bottom rung leaves alone, which is what sends them to the
            // stack.
            vec![
                one_block.clone(),
                rebuild(&[(2, 12)], &[]),
                split_minimal(0),
            ],
            vec![
                one_block.clone(),
                rebuild(&[(4, 6)], &[(4, 1), (5, 1)]),
                split_minimal(0),
            ],
            // Gaps of every kind at once: one wide enough for a cut, one that
            // falls inside a single instruction and so admits none.
            vec![
                one_block.clone(),
                rebuild(
                    &[(1, 3), (3, 5), (8, 14)],
                    &[(1, 1), (4, 1), (9, 1), (12, 1)],
                ),
                split_minimal(0),
            ],
            // Uses in adjacent instructions, and two uses of one instruction:
            // the two ways the same boundary gets asked for twice.
            vec![
                one_block.clone(),
                rebuild(&[(0, NUM_POINTS)], &[(4, 1), (6, 1), (8, 1)]),
                split_minimal(0),
            ],
            vec![
                one_block.clone(),
                rebuild(&[(0, NUM_POINTS)], &[(6, 1), (7, 1)]),
                split_minimal(0),
            ],
            // The bottom rung after the rungs above it, which is the order the
            // allocator reaches it in.
            vec![
                one_block.clone(),
                rebuild(&[(0, 6), (8, 16)], &[(0, 1), (4, 1), (8, 1), (14, 1)]),
                split(0),
                split_within(0),
                split_minimal(1),
                split_minimal(0),
            ],
        ];
        for ops in seeds.iter_mut() {
            fixup_ops(ops);
        }
        seeds
    }

    /// Run `ops` against a fresh state, checking every promise at every step.
    fn run(ops: &[Op]) -> Result<State, String> {
        let mut state = State::new();
        check_pieces_partition(&state)?;

        for op in ops {
            match op {
                Op::Split { piece, within_span } => {
                    let index = usize::from(*piece) % state.pieces.len();
                    if let Some((prefix, suffix)) =
                        check_split(&state.pieces[index], &state.parked, *within_span)?
                    {
                        state.pieces[index] = prefix;
                        state.pieces.insert(index + 1, suffix);
                    }
                }

                Op::SplitIntoMinimal { piece } => {
                    let index = usize::from(*piece) % state.pieces.len();
                    let pieces = check_split_into_minimal(&state.pieces[index])?;
                    state.pieces.splice(index..index + 1, pieces);
                }

                Op::Assign { piece, candidate } => {
                    let index = usize::from(*piece) % state.pieces.len();
                    let weight = f32::from(u16::try_from(1u32 << state.next_weight).unwrap());
                    state.next_weight += 1;
                    state.parked.push(Parked {
                        candidate: *candidate,
                        spans: state.pieces[index].spans.clone(),
                        weight,
                    });
                }

                Op::Evict { candidate } => {
                    state.parked.retain(|p| p.candidate != *candidate);
                }

                Op::SetBlockBoundaries { mask } => {
                    state.blocks = *mask;
                    state.rebuild();
                }

                Op::SetTies { mask } => {
                    state.tied = *mask;
                    state.rebuild();
                }

                Op::Rebuild { spans, uses } => {
                    state.source_spans.clone_from(spans);
                    state.source_uses.clone_from(uses);
                    state.rebuild();
                }

                Op::Reset => {
                    state = State::new();
                }
            }

            check_pieces_partition(&state)?;
        }

        Ok(state)
    }

    #[test]
    fn splitting_properties() -> CheckResult<Vec<Op>> {
        let mutator = m::default::<Vec<Op>>().map(|_ctx, ops| {
            fixup_ops(ops);
            Ok(())
        });

        Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run_with(mutator, seeds(), |ops: &Vec<Op>| -> Result<(), String> {
                run(ops)?;
                Ok(())
            })
    }

    /// Splitting bottoms out.
    ///
    /// Cut whatever is still cuttable, on either rung, until nothing is,
    /// checking at every step that nothing is created and nothing is lost.
    ///
    /// The budget is counted in instructions rather than in spans, because a
    /// within-span split leaves *more* spans than it found. Every piece covers
    /// at least one instruction and the pieces partition the bundle's
    /// instructions, so there can never be more pieces than the bundle has
    /// instructions; every split makes exactly one more piece, so that is also
    /// a bound on how many splits there can be.
    #[test]
    fn splitting_terminates() -> CheckResult<Vec<Op>> {
        let mutator = m::default::<Vec<Op>>().map(|_ctx, ops| {
            fixup_ops(ops);
            Ok(())
        });

        Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run_with(mutator, seeds(), |ops: &Vec<Op>| -> Result<(), String> {
                let mut state = run(ops)?;

                let budget = state.whole.len_insts();
                for _ in 0..=budget {
                    // Cut the first piece that will still take a cut, trying
                    // both rungs in the order the allocator does.
                    let mut cut = None;
                    for index in 0..state.pieces.len() {
                        for within_span in [false, true] {
                            let halves =
                                check_split(&state.pieces[index], &state.parked, within_span)?;
                            if let Some(halves) = halves {
                                cut = Some((index, halves));
                                break;
                            }
                        }
                        if cut.is_some() {
                            break;
                        }
                    }

                    let (index, (prefix, suffix)) = match cut {
                        Some(cut) => cut,
                        // Neither of the first two rungs will cut anything
                        // more. The last one shreds whatever they left, and
                        // after it nothing at all is cuttable, which is where
                        // splitting has to end up: the allocator has no rung
                        // after that one but spilling.
                        None => {
                            let mut shredded = Vec::new();
                            for piece in &state.pieces {
                                shredded.extend(check_split_into_minimal(piece)?);
                            }
                            state.pieces = shredded;
                            check_pieces_partition(&state)?;

                            for piece in &state.pieces {
                                // `check_split_into_minimal` already made sure
                                // the bottom rung has nothing more to say about
                                // each piece; the two rungs above it must be
                                // just as done, since the bottom one cuts
                                // everywhere they would have.
                                for within_span in [false, true] {
                                    if check_split(piece, &state.parked, within_span)?.is_some() {
                                        return Err(format!(
                                            "{:?} came out of splitting into minimal pieces, but \
                                             is still cuttable with within_span = {within_span}",
                                            piece.spans,
                                        ));
                                    }
                                }
                            }

                            return Ok(());
                        }
                    };

                    state.pieces[index] = prefix;
                    state.pieces.insert(index + 1, suffix);
                    check_pieces_partition(&state)?;
                }

                Err(format!(
                    "still cutting after {budget} steps, but the bundle only ever covered \
                     {budget} instructions, so it can hold at most that many pieces",
                ))
            })
    }

    /// The hand-written cases behind the seeds above, stated as what
    /// `within_span_cuts` yields rather than as what splitting does with it.
    fn cuts(spans: &[(u8, u8)], uses: &[u8]) -> Vec<(usize, u8)> {
        let spans: Vec<_> = spans.iter().map(|&(s, e)| span(s, e)).collect();
        let uses: Vec<_> = uses
            .iter()
            .map(|&p| SplitUse {
                point: point(p),
                weight: 1.0,
                cut_before_allowed: true,
            })
            .collect();

        // The oracle agrees, on every one of these, with the kernel.
        assert_eq!(
            within_span_cuts(&spans, &uses).collect::<Vec<_>>(),
            oracle_within_span_cuts(&spans, &uses),
        );

        within_span_cuts(&spans, &uses)
            .map(|cut| {
                let at = u8::try_from(cut.at.inst().index() * 2).unwrap();
                debug_assert_eq!(cut.at.pos(), Position::Early);
                (cut.index, at)
            })
            .collect()
    }

    #[test]
    fn no_cut_without_two_uses() {
        assert!(cuts(&[(0, 6)], &[]).is_empty());
        assert!(cuts(&[(0, 6)], &[2]).is_empty());
        // Two uses, but in different spans: that is the other rung's job.
        assert!(cuts(&[(0, 4), (8, 12)], &[2, 8]).is_empty());
    }

    #[test]
    fn no_cut_within_an_instruction() {
        // Both positions of instruction two. A move cannot be inserted between
        // an instruction's uses and its defs, so there is nowhere to cut.
        assert!(cuts(&[(0, 8)], &[4, 5]).is_empty());
    }

    #[test]
    fn one_cut_between_adjacent_instructions() {
        // Instructions two and three: the earliest legal cut after the first
        // use and the latest before the second are the same point, and it is
        // reported once.
        assert_eq!(cuts(&[(2, 10)], &[4, 6]), [(0, 6)]);
        // The same when the first use is at `(2, Late)`.
        assert_eq!(cuts(&[(2, 10)], &[5, 6]), [(0, 6)]);
    }

    #[test]
    fn both_ends_of_a_wide_gap() {
        // Instructions one and six, so the two ends are distinct: cut as late
        // as possible while keeping the first use, or as early as possible
        // while keeping the second.
        assert_eq!(cuts(&[(0, 14)], &[2, 12]), [(0, 4), (0, 12)]);
        // Rounding outward from `(1, Late)` and `(5, Late)` reaches the same
        // pair of boundaries.
        assert_eq!(cuts(&[(0, 14)], &[3, 11]), [(0, 4), (0, 10)]);
    }

    #[test]
    fn cuts_stay_inside_their_span() {
        // Uses on the span's first and last points. Cutting at `span.start`
        // or at `span.end` would leave an empty piece.
        assert_eq!(cuts(&[(4, 11)], &[4, 10]), [(0, 6), (0, 10)]);
    }

    #[test]
    fn cuts_are_grouped_by_span() {
        // Every span is offered its own cuts, indexed by its own position, and
        // a span whose uses share an instruction contributes none.
        assert_eq!(
            cuts(&[(0, 6), (8, 14), (14, 16)], &[0, 4, 8, 12, 14, 15]),
            [(0, 2), (0, 4), (1, 10), (1, 12)],
        );
    }

    #[test]
    fn three_uses_give_two_gaps() {
        assert_eq!(
            cuts(&[(0, 14)], &[1, 6, 12]),
            [(0, 2), (0, 6), (0, 8), (0, 12)]
        );
    }
    /// The same, for `minimal_cuts`, with nothing tied.
    ///
    /// A cut between spans comes out as `(index, None)`, and a cut within one
    /// as `(index, Some(point))`.
    fn minimal(spans: &[(u8, u8)], uses: &[u8]) -> Vec<(usize, Option<u8>)> {
        minimal_tied(spans, uses, 0)
    }

    /// The same, with `tied` naming the instructions a tie crosses the middle
    /// of, as in [`State::tied`].
    fn minimal_tied(spans: &[(u8, u8)], uses: &[u8], tied: u16) -> Vec<(usize, Option<u8>)> {
        let spans: Vec<_> = spans.iter().map(|&(s, e)| span(s, e)).collect();
        let uses: Vec<_> = uses
            .iter()
            .map(|&p| SplitUse {
                point: point(p),
                weight: 1.0,
                cut_before_allowed: oracle_cut_before_allowed(point(p), tied),
            })
            .collect();

        // The oracle agrees, on every one of these, with the kernel, and so do
        // all the other promises the kernel makes.
        check_split_into_minimal(&Piece {
            spans: spans.clone(),
            uses: uses.clone(),
        })
        .unwrap();

        minimal_cuts(&spans, &uses)
            .map(|cut| match cut {
                Cut::BetweenSpans(index) => (index, None),
                Cut::WithinSpan(WithinSpanCut { index, at }) => {
                    debug_assert_eq!(at.pos(), Position::Early);
                    (index, Some(u8::try_from(at.inst().index() * 2).unwrap()))
                }
            })
            .collect()
    }

    #[test]
    fn no_minimal_cuts_for_a_single_instruction_span() {
        // Instruction two, at both positions. There is no boundary inside it
        // to cut at, which is what makes one instruction the floor.
        assert!(minimal(&[(4, 6)], &[4]).is_empty());
        assert!(minimal(&[(4, 6)], &[5]).is_empty());
        assert!(minimal(&[(4, 6)], &[4, 5]).is_empty());
        // A span running from one `Late` point to the next reaches into two
        // instructions, so it does have a boundary inside it to cut at.
        assert_eq!(minimal(&[(5, 7)], &[5, 6]), [(0, Some(6))]);
    }

    #[test]
    fn no_minimal_cuts_for_a_use_free_span() {
        // Nothing wants any particular part of this, so cutting it up would
        // only make more bundles to place, all of them equally happy anywhere.
        assert!(minimal(&[(0, NUM_POINTS)], &[]).is_empty());
        assert!(minimal(&[(2, 6), (8, 12)], &[]) == [(1, None)]);
    }

    #[test]
    fn a_use_carves_out_its_own_instruction() {
        // The use is in instruction three, so the two boundaries around it are
        // `(3, Early)` and `(4, Early)`: this allocator's `minimal_range_for_use`.
        assert_eq!(minimal(&[(0, 16)], &[6]), [(0, Some(6)), (0, Some(8))]);
        assert_eq!(minimal(&[(0, 16)], &[7]), [(0, Some(6)), (0, Some(8))]);

        // A boundary at the span's own end does not divide it, so a use in the
        // first or last instruction of a span asks for only one cut.
        assert_eq!(minimal(&[(6, 16)], &[6]), [(0, Some(8))]);
        assert_eq!(minimal(&[(0, 8)], &[6]), [(0, Some(6))]);
    }

    #[test]
    fn uses_in_adjacent_instructions_share_a_boundary() {
        // Instructions three and four. The boundary between them is the second
        // use's `before` and the first use's `after`, and it is reported once.
        assert_eq!(
            minimal(&[(0, 16)], &[6, 8]),
            [(0, Some(6)), (0, Some(8)), (0, Some(10))],
        );
        assert_eq!(
            minimal(&[(0, 16)], &[7, 9]),
            [(0, Some(6)), (0, Some(8)), (0, Some(10))],
        );
    }

    #[test]
    fn two_uses_in_one_instruction_are_not_separated() {
        // Both positions of instruction three ask for the very same pair of
        // boundaries, and nothing can go between them anyway.
        assert_eq!(minimal(&[(0, 16)], &[6, 7]), [(0, Some(6)), (0, Some(8))]);
    }

    #[test]
    fn abutting_spans_at_a_late_point_need_a_tie_to_stay_together() {
        // Two spans meeting at `(3, Late)`, which is inside instruction three:
        // any move a cut there demands has nowhere to go. When the use starting
        // the second span is tied to the first -- it reuses that operand's
        // allocation, or it is another piece of the same value -- the cut would
        // demand one, so the gap admits none and shredding leaves the two spans
        // together.
        assert_eq!(
            minimal_tied(&[(5, 7), (7, 9)], &[5, 7], 1 << 3),
            [(0, Some(6)), (1, Some(8))],
        );

        // Cutting at those two points leaves the middle piece holding both
        // spans, and it cannot be cut any further even though it is two spans.
        assert!(minimal_tied(&[(6, 7), (7, 8)], &[7], 1 << 3).is_empty());
        assert!(is_minimal_bundle(0, 1, 1));

        // Untie them -- two unrelated values that coalescing happened to put in
        // one bundle -- and the same gap takes a cut after all, because neither
        // half needs anything moved across it. The caller widens the suffix back
        // to `(3, Early)` afterwards; that is
        // `LiveBundle::split_at_span`'s job, not the kernel's.
        assert_eq!(
            minimal(&[(5, 7), (7, 9)], &[5, 7]),
            [(0, Some(6)), (1, None), (1, Some(8))],
        );
        assert_eq!(minimal(&[(6, 7), (7, 8)], &[7]), [(1, None)]);
        assert!(!is_minimal_bundle(1, 1, 1));
    }

    #[test]
    fn every_admissible_gap_is_cut() {
        // The first gap is empty, sitting at the boundary `(6, Early)`, and
        // the second is wide. Both take a cut; a gap inside an instruction,
        // like the one in `abutting_spans_at_a_late_point_admit_no_cut`, does
        // not.
        assert_eq!(
            minimal(&[(2, 12), (12, 14), (15, 16)], &[]),
            [(1, None), (2, None)],
        );
    }

    /// A suffix that begins in the middle of an instruction is priced as the
    /// caller will actually build it: widened back to the instruction boundary.
    ///
    /// The layout, with instruction three the one the cut lands inside of:
    ///
    /// ```text
    ///   point:  2   3   4   5   6   7   8   9  10  11
    ///   spans:  [--A--) [-----B-----) [-------C------ ...
    ///   parked:                 [-p1-)     [--p2--)
    /// ```
    ///
    /// `p1` sits in exactly the half-instruction that the widening adds to `C`,
    /// so cutting before `C` costs `p1` even though the unwidened `C` clears it.
    /// Charging for it is what stops the mid-instruction cut from winning on an
    /// estimate that applying it would immediately invalidate.
    #[test]
    fn a_mid_instruction_cut_is_priced_widened() {
        let spans = [span(2, 4), span(4, 7), span(7, 10)];

        // Uses that leave both cuts equally balanced, so that the interference
        // is the only thing telling them apart. Nothing ties the use at
        // `(3, Late)` to the span before it, so the gap there takes a cut.
        let uses = [
            SplitUse {
                point: point(2),
                weight: 2.0,
                cut_before_allowed: true,
            },
            SplitUse {
                point: point(7),
                weight: 2.0,
                cut_before_allowed: true,
            },
        ];
        assert_eq!(between_span_cuts(&spans, &uses).collect::<Vec<_>>(), [1, 2]);

        let parked = [
            Parked {
                candidate: 0,
                spans: vec![span(6, 7)],
                weight: 1.0,
            },
            Parked {
                candidate: 0,
                spans: vec![span(9, 11)],
                weight: 1.0,
            },
        ];

        let mut halves: Vec<Vec<Range<LivePoint<u32>>>> = Vec::new();
        let best = best_split_between_spans(&spans, &uses, [0u8], |candidate, half| {
            let half: Vec<_> = half.iter().collect();
            let weight = interference(&parked, candidate, &half);
            halves.push(half);
            weight
        })
        .unwrap();

        // Every half is one of the four the two cuts produce, and the one after
        // the mid-instruction cut reaches back to `(3, Early)`.
        assert_eq!(
            halves,
            [
                vec![span(2, 4)],
                vec![span(4, 7), span(7, 10)],
                vec![span(2, 4), span(4, 7)],
                vec![span(6, 10)],
            ],
        );

        // Cutting between `B` and `C` displaces `p1` and `p2` on one side, for
        // 2.0, which is what cutting between `A` and `B` already costs; the tie
        // goes to the earlier cut. Were the suffix priced unwidened it would
        // clear `p1` and score 1.0, and win.
        assert_eq!(best.cut, 1);
        assert_eq!(best.score.normalized().max_interference, 2.0);
    }

    #[test]
    fn equal_cuts_split_in_the_middle() {
        // Every cut ties.
        for len in 2..=6 {
            let spans: Vec<_> = (0..len).map(|i| span(2 * i, 2 * i + 2)).collect();
            let best = best_split_between_spans(&spans, &[], [0u8, 1], |_, _| 0.0).unwrap();
            assert_eq!(best.cut, usize::from(len) / 2, "{len} spans");
            assert_eq!(best.candidate, 0);
        }

        // Cut 4 splits the tied cuts into runs `1..=3` and `5`.
        let spans: Vec<_> = (0..6).map(|i| span(2 * i, 2 * i + 2)).collect();
        let best = best_split_between_spans(&spans, &[], [0u8], |_, half| {
            let is_prefix = half.get(0).start == point(0);
            if is_prefix && half.len() == 4 {
                1.0
            } else {
                0.0
            }
        })
        .unwrap();
        assert_eq!(best.cut, 2);
    }

    #[test]
    fn equal_within_span_cuts_split_in_the_middle() {
        // Every cut ties.
        let spans = [span(0, 16)];
        let uses: Vec<_> = (0..8)
            .map(|i| SplitUse {
                point: point(2 * i),
                weight: 0.0,
                cut_before_allowed: true,
            })
            .collect();
        let cuts: Vec<_> = within_span_cuts(&spans, &uses).collect();
        assert_eq!(cuts.len(), 7);
        let best = best_split_within_span(&spans, &uses, [0u8, 1], |_, _| 0.0).unwrap();
        assert_eq!(best.cut, cuts[3]);
        assert_eq!(best.candidate, 0);
    }

    #[test]
    fn minimal_cuts_are_ascending_and_deduplicated() {
        // Gaps and interior cuts interleave in program order, each span's cuts
        // indexed by its own position.
        assert_eq!(
            minimal(&[(0, 6), (8, 14), (14, 16)], &[0, 4, 8, 12, 14, 15]),
            [
                (0, Some(2)),
                (0, Some(4)),
                (1, None),
                (1, Some(10)),
                (1, Some(12)),
                (2, None),
            ],
        );
    }
}
