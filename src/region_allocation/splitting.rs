//! Choosing where to split a bundle.

use crate::{
    entity::{Entity, EntityRepr},
    input::Position,
    live_ranges::LivePoint,
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
    /// Both must be finite and greater than or equal to `0.0`.
    pub fn new(max_interference: f32, min_use_weight: f32) -> Self {
        debug_assert!(max_interference.is_finite());
        debug_assert!(min_use_weight.is_finite());
        debug_assert!(max_interference >= 0.0);
        debug_assert!(min_use_weight >= 0.0);
        SplitScore {
            max_interference,
            min_use_weight,
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
pub struct SplitChoice<C> {
    /// Where to split: `spans[..index]` lie before it and `spans[index..]` after
    /// it.
    ///
    /// Always `1 <= index < spans.len()`, so neither half is ever left without
    /// a span.
    pub index: usize,

    /// The candidate the cut was scored against.
    pub candidate: C,

    /// The split's score.
    pub score: SplitScore,
}

/// The places we could divide `spans` into two halves.
///
/// This filters out splits that would leave one half empty as well as splits
/// that do not fall on an instruction boundary (which can create demands for
/// moves that are unsatisfiable).
fn split_points<E>(spans: &[Range<LivePoint<E>>]) -> impl Iterator<Item = usize> + Clone + '_
where
    E: EntityRepr,
{
    spans
        .windows(2)
        .enumerate()
        .filter(|(_i, pair)| gap_admits_a_cut(&pair[0], &pair[1]))
        .map(|(i, _pair)| i + 1)
}

/// Does an instruction boundary fall in the gap between `before` and `after`?
fn gap_admits_a_cut<E>(before: &Range<LivePoint<E>>, after: &Range<LivePoint<E>>) -> bool
where
    E: EntityRepr,
{
    debug_assert!(before.end <= after.start);

    match before.end.pos() {
        Position::Early => true,
        Position::Late => after.start.inst().index() > before.end.inst().index(),
    }
}

/// Find the best point to split `spans` at, or return `None` if there is no
/// valid place to split between spans.
///
/// `uses` must be sorted by program point.
///
/// `candidates` is the set of `Reg`s or `RegGroup`s that the associated bundle
/// could be assigned to.
///
/// `interference` is a function that calculates how much making room for one
/// half of a proposed split would cost: that is, the weight of the other
/// bundles that would need to be displaced.
pub fn best_split_point<E, C>(
    spans: &[Range<LivePoint<E>>],
    uses: &[SplitUse<E>],
    candidates: impl IntoIterator<Item = C> + Clone,
    mut interference: impl FnMut(C, &[Range<LivePoint<E>>]) -> f32,
) -> Option<SplitChoice<C>>
where
    E: EntityRepr,
    C: Copy,
{
    debug_assert!(uses.windows(2).all(|pair| pair[0].point <= pair[1].point));

    let total_use_weight: f32 = uses.iter().map(|u| u.weight).sum();

    let mut best: Option<SplitChoice<C>> = None;
    let mut uses_cursor = 0;
    let mut prefix_use_weight = 0.0;

    for k in split_points(spans) {
        debug_assert!(1 <= k && k < spans.len());

        let (prefix, suffix) = spans.split_at(k);

        // Advance `uses_cursor` to the new split point and update the prefix's
        // use weight.
        let suffix_start = suffix[0].start;
        while uses_cursor < uses.len() && uses[uses_cursor].point < suffix_start {
            prefix_use_weight += uses[uses_cursor].weight;
            uses_cursor += 1;
        }

        let suffix_use_weight = total_use_weight - prefix_use_weight;
        let min_use_weight = prefix_use_weight.min(suffix_use_weight);

        for candidate in candidates.clone() {
            let prefix_interference = interference(candidate, prefix);
            let suffix_interference = interference(candidate, suffix);
            let max_interference = prefix_interference.max(suffix_interference);
            let score = SplitScore::new(max_interference, min_use_weight);
            if best.is_none_or(|best| score > best.score) {
                best = Some(SplitChoice {
                    index: k,
                    candidate,
                    score,
                });
            }
        }
    }

    best
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Inst;
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
    }

    struct State {
        /// The block partition, which the kernel never sees but which decides
        /// where the spans are cut and therefore which cuts exist.
        blocks: u16,

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
    fn oracle_points(spans: &[Range<LivePoint<u32>>]) -> Vec<usize> {
        let mut out = Vec::new();
        for k in 1..spans.len() {
            let (before, after) = (&spans[k - 1], &spans[k]);
            let admits = (0..=NUM_INSTS).any(|i| {
                let boundary =
                    LivePoint::new(Inst::try_new(usize::from(i)).unwrap(), Position::Early);
                before.end <= boundary && boundary <= after.start
            });
            if admits {
                out.push(k);
            }
        }
        out
    }

    /// What cutting `piece` at `k` scores in `candidate`, computed the dumb way.
    fn oracle_score(piece: &Piece, parked: &[Parked], candidate: u8, k: usize) -> SplitScore {
        let (before, after) = piece.spans.split_at(k);
        let cut = after[0].start;

        let prefix: f32 = piece
            .uses
            .iter()
            .filter(|u| u.point < cut)
            .map(|u| u.weight)
            .sum();
        let total: f32 = piece.uses.iter().map(|u| u.weight).sum();

        SplitScore::new(
            interference(parked, candidate, before).max(interference(parked, candidate, after)),
            prefix.min(total - prefix),
        )
    }

    /// Check everything `best_split_point` promises about `piece`, and return
    /// the two halves it chose, if it chose any.
    fn check_split(piece: &Piece, parked: &[Parked]) -> Result<Option<(Piece, Piece)>, String> {
        let spans = &piece.spans;

        // The admissible cuts are exactly the ones the oracle finds, in
        // ascending order, and neither half of any of them is span-less.
        let actual: Vec<usize> = split_points(spans).collect();
        let expected = oracle_points(spans);
        if actual != expected {
            return Err(format!(
                "`split_points({spans:?})` gives {actual:?} but should give {expected:?}",
            ));
        }
        for pair in actual.windows(2) {
            if pair[0] >= pair[1] {
                return Err(format!(
                    "`split_points({spans:?})` gives {actual:?}, unordered"
                ));
            }
        }
        for &cut in &actual {
            if !(1 <= cut && cut < spans.len()) {
                return Err(format!(
                    "`split_points({spans:?})` gives {cut}, which leaves a half span-less",
                ));
            }
        }

        let choice = best_split_point(spans, &piece.uses, 0..NUM_CANDIDATES, |candidate, half| {
            interference(parked, candidate, half)
        });

        let choice = match choice {
            None => {
                if !expected.is_empty() {
                    return Err(format!(
                        "`best_split_point` found no cut of {spans:?}, but {expected:?} are all \
                         admissible",
                    ));
                }
                return Ok(None);
            }
            Some(choice) => {
                if expected.is_empty() {
                    return Err(format!(
                        "`best_split_point` chose {choice:?} for {spans:?}, which admits no cut",
                    ));
                }
                choice
            }
        };

        if !expected.contains(&choice.index) {
            return Err(format!(
                "`best_split_point` chose {:?} for {spans:?}, which is not one of the admissible \
                 {expected:?}",
                choice.index,
            ));
        }
        if choice.candidate >= NUM_CANDIDATES {
            return Err(format!(
                "`best_split_point` chose candidate {}, which does not exist",
                choice.candidate,
            ));
        }

        // The score is what the oracle computes for that same cut and
        // candidate.
        let scored = oracle_score(piece, parked, choice.candidate, choice.index);
        if choice.score.normalized() != scored.normalized() {
            return Err(format!(
                "`best_split_point` scored {:?} at {choice:?}, but the oracle scores {:?}",
                choice.score.normalized(),
                scored.normalized(),
            ));
        }

        // Nothing scores strictly better, and among equals the earliest cut won
        // and, within a cut, the earliest candidate.
        for &cut in &expected {
            for candidate in 0..NUM_CANDIDATES {
                let other = oracle_score(piece, parked, candidate, cut);
                if other > choice.score {
                    return Err(format!(
                        "`best_split_point` chose {choice:?} for {spans:?}, but cutting at \
                         {cut} for candidate {candidate} scores {other:?}, which is better",
                    ));
                }
                let tied = choice.score <= other;
                if tied && (cut, candidate) < (choice.index, choice.candidate) {
                    return Err(format!(
                        "`best_split_point` chose {choice:?} for {spans:?}, but cutting at \
                         {cut} for candidate {candidate} ties it and comes first",
                    ));
                }
            }
        }

        // The halves partition the piece: every span in exactly one, order
        // preserved, both non-empty and each strictly smaller than the piece.
        let k = choice.index;
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

    /// The pieces are still exactly the bundle splitting started from.
    fn check_pieces_partition(state: &State) -> Result<(), String> {
        let spans: Vec<_> = state
            .pieces
            .iter()
            .flat_map(|p| p.spans.iter().cloned())
            .collect();
        if spans != state.whole.spans {
            return Err(format!(
                "the pieces cover {spans:?}, but the bundle they came from covers {:?}",
                state.whole.spans,
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

        /// Start over from a different bundle, keeping the landscape.
        Rebuild {
            spans: Vec<(u8, u8)>,
            uses: Vec<(u8, u8)>,
        },

        Reset,
    }

    impl Default for Op {
        fn default() -> Self {
            Op::Split { piece: 0 }
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
                Op::Split { .. } | Op::Reset => {}
                Op::Assign { candidate, .. } | Op::Evict { candidate } => {
                    *candidate %= NUM_CANDIDATES;
                }
                Op::SetBlockBoundaries { mask } => {
                    // Instruction zero always starts a block, and nothing past
                    // the end of the program starts one.
                    *mask = (*mask | 1) & ((1 << NUM_INSTS) - 1);
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

    fn split(piece: u8) -> Op {
        Op::Split { piece }
    }

    fn assign(piece: u8, candidate: u8) -> Op {
        Op::Assign { piece, candidate }
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
            // Two spans that merely touch at `(i, Late)`. Nothing separates
            // them, so there is no cut: the known gap that
            // `split_into_minimal_or_spill` has to cover.
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
            // gap across a skip.
            vec![
                one_block.clone(),
                rebuild(
                    &[(0, 2), (4, 5), (5, 7), (9, 11)],
                    &[(0, 1), (4, 1), (9, 1)],
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
                Op::Split { piece } => {
                    let index = usize::from(*piece) % state.pieces.len();
                    if let Some((prefix, suffix)) =
                        check_split(&state.pieces[index], &state.parked)?
                    {
                        state.pieces[index] = prefix;
                        state.pieces.insert(index + 1, suffix);
                    }
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

        Check::new().iters(10_000).run_with(
            mutator,
            seeds(),
            |ops: &Vec<Op>| -> Result<(), String> {
                run(ops)?;
                Ok(())
            },
        )
    }

    /// Splitting bottoms out.
    ///
    /// Drive the piece with the most spans to a fixed point, checking at every
    /// step that nothing is created and nothing is lost. Each half is strictly
    /// smaller than the piece it came from, so `len(spans)` steps must be
    /// enough to leave every piece uncuttable.
    #[test]
    fn splitting_terminates() -> CheckResult<Vec<Op>> {
        let mutator = m::default::<Vec<Op>>().map(|_ctx, ops| {
            fixup_ops(ops);
            Ok(())
        });

        Check::new().iters(1_000).run_with(
            mutator,
            seeds(),
            |ops: &Vec<Op>| -> Result<(), String> {
                let mut state = run(ops)?;

                let budget = state.whole.spans.len();
                for step in 0..=budget {
                    let (index, _) = state
                        .pieces
                        .iter()
                        .enumerate()
                        .max_by_key(|(_, piece)| piece.spans.len())
                        .expect("there is always at least one piece");

                    match check_split(&state.pieces[index], &state.parked)? {
                        Some((prefix, suffix)) => {
                            if step == budget {
                                return Err(format!(
                                    "still cutting {:?} after {budget} steps, but the bundle \
                                     only ever held {budget} spans",
                                    state.pieces[index].spans,
                                ));
                            }
                            state.pieces[index] = prefix;
                            state.pieces.insert(index + 1, suffix);
                            check_pieces_partition(&state)?;
                        }
                        None => {
                            // The largest piece is uncuttable, so every piece
                            // is: a smaller one has no more gaps to try.
                            for piece in &state.pieces {
                                if !oracle_points(&piece.spans).is_empty() {
                                    return Err(format!(
                                        "{:?} still admits a cut, but the largest piece does \
                                         not",
                                        piece.spans,
                                    ));
                                }
                            }
                            return Ok(());
                        }
                    }
                }

                Ok(())
            },
        )
    }
}
