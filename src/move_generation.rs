//! Move generation.
//!
//! After we've allocated every bundle, we must insert moves whenever data flows
//! between two different allocations. For example:
//!
//! * A value is allocated in register R in one span and then in register S in
//!   the next span
//!
//! * A block-call argument is allocated in a spill slot but the associated
//!   block parameter is allocated in register R
//!
//! ## Half Moves
//!
//! Within a block, it is pretty easy to connect a move from some source
//! allocation to its destination allocation: we have both the source and
//! destination spans right there. Across control-flow edges, however, both
//! sides are not colocated. Rather than perform random-access lookups of other,
//! far away spans, imposing poor cache locality, we follow the implementation
//! approach of `regalloc2` (and then, also, `regalloc3`): we use "half moves".
//!
//! We scan the spans and emit the source half of a move at the end of a span,
//! recording the value's current allocation, and the destination half of a move
//! at the start of a span, recording the value's desired location. Then we sort
//! the half moves and pair sources with destinations to create a full
//! move. This is essentially a deferred relational join.
//!
//! It can be the case that a destination half has no matching source: this
//! means either that the value is not live here at all, or that we decided to
//! rematerialize it at the destination instead of moving it there.
//!
//! It can also be the case that a source half has no matching destination: this
//! means that the move is unnecessary.
//!
//! ## Moves on Edges
//!
//! A move on the edge `P -> S` goes in one of three places:
//!
//! 1. At the top of `S`, when `S` has one predecessor, so no other path reaches
//!    that code (as it would otherwise perform a move that doesn't apply to its
//!    spans and their allocations).
//!
//! 2. Before `P`'s terminator, when `P` has one successor and that terminator
//!    has no operands, so the move can neither run on another edge nor clobber
//!    a register the terminator reads or defines. It goes last in that gap,
//!    after `P`'s own moves, since it reads what they leave behind.
//!
//! 3. Otherwise the edge is *critical* and the move goes on the edge itself, as
//!    an `Edit::CriticalEdge`. This delays critical-edge splitting until
//!    if/when it is necessary.

use crate::{
    Block, Entity as _, Inst, Val,
    context::ContextInner,
    counts::Counts,
    entity::{EntityRange, EntityRepr, PrimaryMap, SecondaryMap},
    error::{Error, IResult, InternalError},
    events::{EventsLog, ScratchReason},
    hash_map::{Entry, FxHashMap},
    input::{
        DefUse, Input, InputBlock, InputFunction, InputInst as _, InputValue as _, Position,
        RematCost,
    },
    live_ranges::{LivePoint, LiveRanges, LiveSpan},
    liveness::{Liveness, block_last_inst},
    machine::{Interfere, Machine, Reg, RegBank},
    output::{
        Allocation, CriticalEdgeEdit, EdgeEdit, Edit, Move, OutputInner, RegAllocation, Remat,
        ScalarAllocation,
    },
    parallel_moves::{ParallelMove, ParallelMoveSolver, SolveError},
    region_allocation::RegionAllocation,
    rpo::Rpo,
    spill_placement::SpillPlacement,
    spill_slot_allocation::{SpillSlot, SpillSlots},
    timing::Timing,
};
use alloc::vec::Vec;
use core::{marker::PhantomData, ops::Range};

/// Run the move generation pass.
pub(crate) fn generate_moves<E>(
    context: &mut ContextInner<E>,
    input: &Input<'_, impl InputFunction>,
) -> IResult<()>
where
    E: EntityRepr,
{
    let _timing = Timing::new("generate moves");

    let ContextInner {
        counts,
        events,
        rpo,
        liveness,
        live_ranges,
        region_allocation,
        spill_slots,
        spill_placement,
        move_generation,
        output,
        ..
    } = context;

    move_generation.generate(
        input,
        counts,
        events,
        rpo,
        liveness,
        live_ranges,
        region_allocation,
        spill_slots,
        spill_placement,
        output,
    )
}

define_entities! {
    /// One control-flow edge of the function, as seen from its successor.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct Edge = "edge";
}

/// Where a move can occur.
///
/// This is the un-bitpacked version of `PackedMovePosition`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "serialize", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "serialize", serde(bound = ""))]
pub(crate) enum MovePosition<E>
where
    E: EntityRepr,
{
    /// At `point`: before `point.inst()` when the point is that instruction's
    /// early half, and after it when the point is its late half.
    Point(LivePoint<E>),

    /// In the same gap between instructions as `Point(point)`, but these moves
    /// happen after `Point` moves. This is used to resolve inter-block moves
    /// just before the terminator without conflicting with intra-block moves.
    Departure(LivePoint<E>),

    /// On the critical edge that is `pred`'s `succ`th outgoing edge.
    CriticalEdge {
        /// The block the edge leaves.
        pred: Block<E>,

        /// Which of `pred`'s outgoing edges this is.
        succ: usize,
    },
}

/// The bitpacked version of `MovePosition`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct PackedMovePosition<E>
where
    E: EntityRepr,
{
    /// +--------+--------+--------+
    /// | tag: 1 | hi: 32 | lo: 31 |
    /// +--------+--------+--------+
    ///
    /// `tag = 0` is a point inside a block: `hi` is a `LivePoint`'s bits and
    /// `lo` orders the batches sharing that point, `IN_THE_GAP` before
    /// `DEPARTING`.
    ///
    /// `tag = 1` is a critical edge: `hi` is the predecessor's index and `lo`
    /// is which of the predecessor's outgoing edges it is. The predecessor
    /// comes first so that sorting groups every edge edit by the block it
    /// leaves, which is how `Output::block_insts_and_edits` finds a block's
    /// edge edits as one contiguous slice.
    bits: u64,

    _marker: PhantomData<E>,
}

/// A position serializes as the unpacked form, never as its bits: the bits are
/// an implementation detail and the visualizer needs the instruction.
#[cfg(feature = "serialize")]
impl<E> serde::Serialize for PackedMovePosition<E>
where
    E: EntityRepr,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.unpack().serialize(serializer)
    }
}

impl<E> PackedMovePosition<E>
where
    E: EntityRepr,
{
    const LO_SHIFT: u32 = 0;
    const LO_BITS: u32 = 31;
    const HI_SHIFT: u32 = Self::LO_SHIFT + Self::LO_BITS;
    const HI_BITS: u32 = 32;
    const TAG_SHIFT: u32 = Self::HI_SHIFT + Self::HI_BITS;
    const TAG_BITS: u32 = 1;

    /// A block's own moves at a point, which run first.
    const IN_THE_GAP: usize = 0;

    /// The moves for an edge leaving the block, which run last.
    const DEPARTING: usize = 1;

    /// Create a move in the gap at `point`.
    pub(crate) fn point(point: LivePoint<E>) -> Self {
        Self::pack(0, point.to_bits(), Self::IN_THE_GAP)
    }

    /// Create a move in the gap at `point` for an edge leaving the block, after
    /// everything else there.
    fn departure(point: LivePoint<E>) -> Self {
        Self::pack(0, point.to_bits(), Self::DEPARTING)
    }

    /// Create a move on `pred`'s `succ`th outgoing edge.
    fn critical_edge(pred: Block<E>, succ: u16) -> Self {
        Self::pack(1, pred.index(), succ.into())
    }

    fn pack(tag: usize, hi: usize, lo: usize) -> Self {
        let field = |x: usize, bits: u32, shift: u32| {
            let x = u64::try_from(x).unwrap();
            debug_assert_eq!(x >> bits, 0);
            x << shift
        };
        let bits = field(tag, Self::TAG_BITS, Self::TAG_SHIFT)
            | field(hi, Self::HI_BITS, Self::HI_SHIFT)
            | field(lo, Self::LO_BITS, Self::LO_SHIFT);
        let pos = PackedMovePosition {
            bits,
            _marker: PhantomData,
        };
        debug_assert_eq!(pos.field(Self::TAG_BITS, Self::TAG_SHIFT), tag);
        debug_assert_eq!(pos.field(Self::HI_BITS, Self::HI_SHIFT), hi);
        debug_assert_eq!(pos.field(Self::LO_BITS, Self::LO_SHIFT), lo);
        pos
    }

    fn field(self, bits: u32, shift: u32) -> usize {
        let mask = u64::MAX >> (u64::BITS - bits);
        usize::try_from((self.bits >> shift) & mask).unwrap()
    }

    fn lo(self) -> usize {
        self.field(Self::LO_BITS, Self::LO_SHIFT)
    }

    fn hi(self) -> usize {
        self.field(Self::HI_BITS, Self::HI_SHIFT)
    }

    fn is_point(self) -> bool {
        self.field(Self::TAG_BITS, Self::TAG_SHIFT) == 0
    }

    /// Is this a point position at or before `point`?
    ///
    /// A critical edge is never at or before a point: it is not anywhere in the
    /// block yet, which is the whole reason the client has to split it.
    pub(crate) fn is_at_or_before(self, point: LivePoint<E>) -> bool {
        self.is_point() && self.hi() <= point.to_bits()
    }

    pub(crate) fn unpack(self) -> MovePosition<E> {
        if self.is_point() {
            let point = LivePoint::from_bits(self.hi());
            if self.lo() == Self::IN_THE_GAP {
                MovePosition::Point(point)
            } else {
                debug_assert_eq!(self.lo(), Self::DEPARTING);
                MovePosition::Departure(point)
            }
        } else {
            let pred = Block::try_new(self.hi()).unwrap();
            let succ = self.lo();
            MovePosition::CriticalEdge { pred, succ }
        }
    }

    fn range(self, input: &Input<'_, impl InputFunction>) -> Range<LivePoint<E>> {
        self.unpack().range(input)
    }
}

impl<E> MovePosition<E>
where
    E: EntityRepr,
{
    /// The live range a scratch register borrowed at this position must be
    /// free over.
    pub(crate) fn range(self, input: &Input<'_, impl InputFunction>) -> Range<LivePoint<E>> {
        let point = match self {
            MovePosition::Point(point) | MovePosition::Departure(point) => point,
            MovePosition::CriticalEdge { pred, .. } => pred.end_point(input).prev_point(),
        };
        point..point.next_point()
    }
}

impl<E> core::fmt::Debug for PackedMovePosition<E>
where
    E: EntityRepr,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("PackedMovePosition")
            .field(&self.unpack())
            .finish()
    }
}

/// The key used to join source and destination halves together.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct HalfMoveKey<E>
where
    E: EntityRepr,
{
    // NB: The position comes first so that sorting keys groups everything at
    // one position together, for creating batches.
    pos: PackedMovePosition<E>,
    val: Val<E>,
}

impl<E> HalfMoveKey<E>
where
    E: EntityRepr,
{
    fn new(pos: PackedMovePosition<E>, val: Val<E>) -> Self {
        HalfMoveKey { pos, val }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct EdgeData<E>
where
    E: EntityRepr,
{
    /// The block the edge enters.
    succ: Block<E>,

    /// The block the edge leaves.
    pred: Block<E>,

    /// Which of `pred`'s outgoing edges this is; a block may branch to one
    /// target twice, so the target alone does not identify an edge.
    index: u16,
}

/// A move in a batch, before the source or destination is expanded into scalar
/// locations.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct BatchMove<E>
where
    E: EntityRepr,
{
    /// What the move reads.
    src: Allocation<E>,

    /// What the move writes.
    dst: Allocation<E>,

    /// The value that moves.
    val: Val<E>,
}

/// The move generation pass and its scratch space.
pub(crate) struct MoveGeneration<E>
where
    E: EntityRepr,
{
    /// Where each move reads from.
    sources: FxHashMap<HalfMoveKey<E>, Allocation<E>>,

    /// Where each move writes to.
    ///
    /// There may be multiple entries for the same key because a value may live
    /// (and may *need* to live, due to operand constraints) in multiple
    /// locations at once.
    ///
    /// Note: the destination can be associated with a different value than the
    /// corresponding source. For block parameters, we join the predecessor's
    /// block-call argument value with this block's parameter value.
    dests: Vec<(HalfMoveKey<E>, Allocation<E>)>,

    /// Every control-flow edge, sorted so that a block's incoming edges are
    /// contiguous.
    edges: PrimaryMap<Edge<E>, EdgeData<E>>,

    /// For a block parameter, the block it belongs to and its index in that
    /// block's parameter list.
    param_of: SecondaryMap<Val<E>, Option<(Block<E>, usize)>>,

    /// Scratch for the pass's walk over every value's spans.
    spans: Vec<LiveSpan<E>>,

    /// Every move to make, sorted by position.
    batch_moves: Vec<(PackedMovePosition<E>, BatchMove<E>)>,

    /// One position's worth of `batch`, with groups expanded into scalar
    /// locations.
    expanded: Vec<(ParallelMove<E>, Val<E>)>,

    /// Every rematerialization to perform, sorted by position.
    remats: Vec<(PackedMovePosition<E>, Remat<E>)>,

    /// One position's worth of sequentialized parallel moves.
    solved: Vec<ParallelMove<E>>,

    /// The parallel-move solver.
    solver: ParallelMoveSolver<E>,

    /// The result of this pass: every edit, sorted by position.
    edits: Vec<(PackedMovePosition<E>, Edit<E>)>,
}

impl<E> Default for MoveGeneration<E>
where
    E: EntityRepr,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<E> MoveGeneration<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        MoveGeneration {
            sources: FxHashMap::with_hasher(rustc_hash::FxBuildHasher),
            dests: Vec::new(),
            edges: PrimaryMap::new(),
            param_of: SecondaryMap::new(None),
            spans: Vec::new(),
            batch_moves: Vec::new(),
            expanded: Vec::new(),
            remats: Vec::new(),
            solved: Vec::new(),
            solver: ParallelMoveSolver::new(),
            edits: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            sources,
            dests,
            edges,
            param_of,
            spans,
            batch_moves: batch,
            expanded,
            remats,
            solved,
            solver,
            edits,
        } = self;
        sources.clear();
        dests.clear();
        edges.reset();
        param_of.reset();
        spans.clear();
        batch.clear();
        expanded.clear();
        remats.clear();
        solved.clear();
        solver.reset();
        edits.clear();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            sources,
            dests,
            edges,
            param_of,
            spans,
            batch_moves: batch,
            expanded,
            remats,
            solved,
            solver,
            edits,
        } = self;
        sources.is_empty()
            && dests.is_empty()
            && edges.is_reset()
            && param_of.is_reset()
            && spans.is_empty()
            && batch.is_empty()
            && expanded.is_empty()
            && remats.is_empty()
            && solved.is_empty()
            && solver.is_reset()
            && edits.is_empty()
    }

    /// Get the edits this pass generated, sorted by position and then moves
    /// before rematerializations.
    #[allow(dead_code, reason = "consumed by the phases that are still to come")]
    pub(crate) fn edits(&self) -> &[(PackedMovePosition<E>, Edit<E>)] {
        &self.edits
    }

    /// Those edits, mutably, so that a test can break a correct allocation and
    /// watch the checker notice.
    #[cfg(test)]
    pub(crate) fn edits_mut(&mut self) -> &mut Vec<(PackedMovePosition<E>, Edit<E>)> {
        &mut self.edits
    }

    /// The edits at program points inside the block whose instructions run from
    /// `first` to `last`, in program order.
    pub(crate) fn block_point_edits(
        &self,
        first: Inst<E>,
        last: Inst<E>,
    ) -> &[(PackedMovePosition<E>, Edit<E>)] {
        let start = PackedMovePosition::point(LivePoint::new(first, Position::Early));
        let end = PackedMovePosition::point(LivePoint::new(last, Position::Late).next_point());
        let lo = self.edits.partition_point(|&(pos, _)| pos < start);
        let hi = self.edits.partition_point(|&(pos, _)| pos < end);
        &self.edits[lo..hi]
    }

    /// The edits on critical edges leaving `pred`, in outgoing-edge order.
    pub(crate) fn block_edge_edits(&self, pred: Block<E>) -> &[(PackedMovePosition<E>, Edit<E>)] {
        let start = PackedMovePosition::<E>::pack(1, pred.index(), 0);
        let end = PackedMovePosition::<E>::pack(1, pred.index() + 1, 0);
        let lo = self.edits.partition_point(|&(pos, _)| pos < start);
        let hi = self.edits.partition_point(|&(pos, _)| pos < end);
        &self.edits[lo..hi]
    }

    fn generate(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        rpo: &Rpo<E>,
        liveness: &Liveness<E>,
        live_ranges: &LiveRanges<E>,
        region_allocation: &RegionAllocation<E>,
        spill_slots: &mut SpillSlots<E>,
        spill_placement: &SpillPlacement<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        debug_assert!(self.is_reset());

        self.index_function(input, rpo, output)?;
        self.emit_half_moves(
            input,
            counts,
            events,
            liveness,
            live_ranges,
            spill_slots,
            output,
        )?;
        self.emit_spills(
            input,
            counts,
            events,
            liveness,
            live_ranges,
            spill_slots,
            spill_placement,
            output,
        )?;
        self.resolve(input, counts, events);
        self.sequentialize(
            input,
            counts,
            events,
            region_allocation,
            spill_slots,
            output,
        )
    }

    /// Build the index of what we need in order to generate moves.
    fn index_function(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        rpo: &Rpo<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        let func = input.func;

        for block in rpo.iter() {
            let input_block = func.block(block.with_repr32());

            for (index, param) in input_block.params().enumerate() {
                let param = output.with_repr::<E, _>(param)?;
                self.param_of[param] = Some((block, index));
            }

            // Only reachable predecessors matter: an unreachable block has no
            // live ranges, and so nothing to move along its edges.
            for (index, succ) in input_block.successors().enumerate() {
                let index = u16::try_from(index).unwrap();
                let succ = output.with_repr::<E, _>(succ)?;
                self.edges.push(
                    output,
                    EdgeData {
                        succ,
                        pred: block,
                        index,
                    },
                )?;
            }
        }

        // `incoming_edges` hands out half-open ranges of edge keys, so the key
        // just after the last edge has to be representable as well.
        self.edges.next_key(output)?;

        self.edges.as_mut_slice().sort_unstable();
        Ok(())
    }

    /// The edges that enter `block`.
    fn incoming_edges(&self, block: Block<E>) -> EntityRange<Edge<E>> {
        let edges = self.edges.as_slice();
        let start = edges.partition_point(|e| e.succ < block);
        let end = edges.partition_point(|e| e.succ <= block);
        EntityRange {
            start: Edge::try_new(start).unwrap(),
            end: Edge::try_new(end).unwrap(),
        }
    }

    /// Get the `k`th block-call argument from the given `edge`'s predecessor.
    fn block_call_arg(
        &self,
        input: &Input<'_, impl InputFunction>,
        output: &mut OutputInner<E>,
        edge: EdgeData<E>,
        k: usize,
    ) -> IResult<Val<E>> {
        let pred = input.func.block(edge.pred.with_repr32());
        let arg = pred.successor_block_args(edge.index.into()).nth(k).unwrap();
        output.with_repr::<E, _>(arg)
    }

    /// Walk all spans and emit a half-move for each source and destination of
    /// all the span boundaries that any value flows across.
    fn emit_half_moves(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        liveness: &Liveness<E>,
        live_ranges: &LiveRanges<E>,
        spill_slots: &SpillSlots<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        let mut spans = core::mem::take(&mut self.spans);
        debug_assert!(spans.is_empty());

        spans.extend(live_ranges.spans());
        spans.sort_unstable_by_key(|&span| {
            (
                span.val(live_ranges),
                span.start(live_ranges),
                span.end(live_ranges),
            )
        });

        let result = (|| -> IResult<()> {
            for value_spans in spans.chunk_by(|a, b| a.val(live_ranges) == b.val(live_ranges)) {
                self.emit_value_half_moves(
                    input,
                    counts,
                    events,
                    liveness,
                    live_ranges,
                    spill_slots,
                    output,
                    value_spans,
                )?;
            }
            Ok(())
        })();

        spans.clear();
        self.spans = spans;
        result
    }

    fn emit_value_half_moves(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        liveness: &Liveness<E>,
        live_ranges: &LiveRanges<E>,
        spill_slots: &SpillSlots<E>,
        output: &mut OutputInner<E>,
        value_spans: &[LiveSpan<E>],
    ) -> IResult<()> {
        let func = input.func;
        let val = value_spans[0].val(live_ranges);

        self.emit_entry_param_fills(
            input,
            counts,
            events,
            live_ranges,
            spill_slots,
            output,
            value_spans,
        )?;

        for (i, span) in value_spans.iter().copied().enumerate() {
            let block = span.block(func, live_ranges);
            let start = span.start(live_ranges);
            let end = span.end(live_ranges);

            // A span that holds its value nowhere has no moves at all:
            // whoever wants the value next recomputes it.
            let Some(alloc) = span.allocation(live_ranges, spill_slots) else {
                debug_assert!(
                    span.bundle(live_ranges)
                        .unwrap()
                        .is_rematerialized(live_ranges)
                );
                continue;
            };

            // Handle live-in spans: spans for values that are either live upon
            // entering this block or this block's parameters.
            //
            // We need to emit the destination half of the moves for each
            // incoming edge to this block.
            if span_is_live_in_to_block(input, liveness, val, block, start) {
                // Check whether the value is a parameter of this block.
                let param = self.param_of[val].filter(|&(b, _)| b == block);

                for e in self.incoming_edges(block) {
                    let edge = self.edges[e];
                    let pos = edge_position(input, edge)?;

                    let incoming_val = match param {
                        // `val` is not a block param, so its value across the
                        // edge is the same.
                        None => val,
                        // `val` is a block parameter, which is defined on the
                        // edge by the block-call argument the predecessor
                        // passes.
                        Some((_, k)) => self.block_call_arg(input, output, edge, k)?,
                    };

                    match alloc {
                        Allocation::Reg(_) => {
                            self.emit_dest(counts, events, pos, incoming_val, alloc)
                        }
                        Allocation::Stack(_) => {
                            if incoming_val == val
                                // The gap atop the entry block is shared by
                                // every path in, including by callers,
                                // implicitly, so a store spill placement puts
                                // there moves the value out of the one place it
                                // arrives in, which is not where an edge
                                // delivers it. An edge into the entry block has
                                // to fill the slot itself, and we don't emit a
                                // destination there.
                                && block.with_repr32() != func.entry_block()
                            {
                                // Nothing to do here because either (1) this is
                                // a reg-to-stack move, which is handled by
                                // spill placement, or (2) this is
                                // stack-to-stack move, but values have a single
                                // spill slot for their entire lifetime
                                // regardless which span they are in, so the
                                // move must therefore have the same source and
                                // destination, and need not be emitted.
                            } else {
                                self.emit_dest(counts, events, pos, incoming_val, alloc)
                            }
                        }
                    }
                }
            }

            // Handle spans beginning within this block. Unless they begin with
            // a def, these need to get their value from a previous span within
            // this block.
            //
            // Look for a boundary between this value's spans within the same
            // block. Emit both the source and destination halves right now,
            // since we have everything we need.
            //
            // TODO: Investigate creating the whole `BatchMove` right now,
            // rather than let `resolve` join the halves together later. That
            // might be faster.
            if start != block.start_point(input) {
                let incoming = value_spans[..i]
                    .iter()
                    .rev()
                    .take_while(|prev| prev.block(func, live_ranges) == block)
                    .filter(|prev| prev.start(live_ranges) < start)
                    .find(|prev| {
                        let reaches = start <= prev.end(live_ranges);
                        debug_assert!(
                            reaches
                                || input.func.value(val.with_repr32()).remat_cost()
                                    == Some(RematCost::AlwaysRemat),
                            "{val:?}'s spans must overlap or abut, but {prev:?} ends at {:?}, \
                             before {start:?}",
                            prev.end(live_ranges),
                        );
                        reaches
                    })
                    .copied()
                    // A previous piece holding its value nowhere does not flow
                    // into this one: dropping it leaves the source-less
                    // destination below, which `resolve` fills by recomputing.
                    .and_then(|prev| prev.allocation(live_ranges, spill_slots));
                if let Some(prev_alloc) = incoming {
                    if prev_alloc != alloc {
                        debug_assert!(
                            start.pos().is_early(),
                            "{val:?} changes allocation at {start:?}, where there is no room for a \
                         move",
                        );
                        let pos = PackedMovePosition::point(start);
                        self.emit_source(counts, events, pos, val, prev_alloc);

                        match alloc {
                            Allocation::Reg(_) => self.emit_dest(counts, events, pos, val, alloc),
                            Allocation::Stack(_) => {
                                // Handled by spill placement.
                            }
                        }
                    }
                } else if defines_val_at(func, val, start) {
                    // This span defines its value, so the instruction it starts
                    // at puts the value in place. Nothing to do.
                } else {
                    // Otherwise nothing in this block flows into this span, and
                    // the value is not live-in either, so the only thing that
                    // can put it in place is recomputing it.
                    debug_assert!(input.func.value(val.with_repr32()).remat_cost().is_some());
                    debug_assert!(start.pos().is_early());
                    let pos = PackedMovePosition::point(start);

                    match alloc {
                        // No source: `resolve` sees a destination it cannot
                        // fill from anywhere and rematerializes it.
                        Allocation::Reg(_) => self.emit_dest(counts, events, pos, val, alloc),
                        Allocation::Stack(_) => {
                            // Handled by spill placement, as above: a value
                            // with any span on the stack has a slot, stored
                            // into once just after its definition.
                        }
                    }
                }
            }

            // Handle live-out spans: spans for values that are live after this
            // blocks execution, including block-call arguments.
            //
            // We need to emit the source half of the move for each of this
            // block's outgoing edges.
            if span_is_live_out_of_block(input, liveness, val, block, end) {
                let input_block = func.block(block.with_repr32());
                for (index, succ) in input_block.successors().enumerate() {
                    let index = u16::try_from(index).unwrap();
                    let succ = output.with_repr::<E, _>(succ)?;
                    let pos = edge_position(
                        input,
                        EdgeData {
                            succ,
                            pred: block,
                            index,
                        },
                    )?;
                    self.emit_source(counts, events, pos, val, alloc);
                }
            }
        }

        Ok(())
    }

    /// Fill the entry block's extra live-in pieces of a parameter from the one
    /// place it arrives in.
    ///
    /// Other blocks' parameters are filled by their incoming edges' moves; the
    /// entry block's edge from the caller is implicit, and has no incoming
    /// edge. The caller is responsible for placing its arguments in the
    /// parameter location `Output::block_param_allocs` reports. Every other
    /// span starting at the block's start point must read that location.
    fn emit_entry_param_fills(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        live_ranges: &LiveRanges<E>,
        spill_slots: &SpillSlots<E>,
        output: &mut OutputInner<E>,
        value_spans: &[LiveSpan<E>],
    ) -> IResult<()> {
        let val = value_spans[0].val(live_ranges);
        let entry = output.with_repr::<E, _>(input.func.entry_block())?;

        // Only the entry block's own parameters arrive from outside; anything
        // else beginning at the start point is defined there.
        if self.param_of[val].filter(|&(b, _)| b == entry).is_none() {
            return Ok(());
        }

        let start = entry.start_point(input);
        let entry_start_spans = || {
            value_spans
                .iter()
                .copied()
                .filter(|span| span.start(live_ranges) == start)
        };

        // The furthest-reaching span, ties broken by the span itself. This must
        // agree with `Output::block_param_allocs`, which tells the caller where
        // to place its arguments.
        let Some(arrival_span) =
            entry_start_spans().max_by_key(|span| (span.end(live_ranges), *span))
        else {
            return Ok(());
        };
        let arrival_alloc = arrival_span
            .allocation(live_ranges, spill_slots)
            .expect("a block parameter always has an allocation");

        let pos = PackedMovePosition::point(start);
        let mut emitted_source = false;
        for span in entry_start_spans() {
            let alloc = span
                .allocation(live_ranges, spill_slots)
                .expect("a block parameter always has an allocation");
            if alloc == arrival_alloc {
                continue;
            }

            // Lazily, so a parameter wanted only where it arrives gets no move.
            if !emitted_source {
                emitted_source = true;
                self.emit_source(counts, events, pos, val, arrival_alloc);
            }

            self.emit_dest(counts, events, pos, val, alloc);
        }

        Ok(())
    }

    /// Record that `val` is in `alloc` at `pos`.
    fn emit_source(
        &mut self,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        pos: PackedMovePosition<E>,
        val: Val<E>,
        alloc: Allocation<E>,
    ) {
        trace!("move generation: emit source {val:?} at {pos:?} is {alloc:?}");
        counts.half_move_sources.inc();
        match self.sources.entry(HalfMoveKey::new(pos, val)) {
            Entry::Occupied(mut entry) => {
                // A value can be in several places at once, any of which could
                // serve as the source of a move. We keep only the best source.
                if better_source(alloc, *entry.get()) {
                    let replaced = entry.insert(alloc);
                    event!(
                        events,
                        HalfMoveSource {
                            pos,
                            val,
                            alloc,
                            replaced: Some(replaced)
                        }
                    );
                }
            }
            Entry::Vacant(entry) => {
                entry.insert(alloc);
                event!(
                    events,
                    HalfMoveSource {
                        pos,
                        val,
                        alloc,
                        replaced: None
                    }
                );
            }
        }
    }

    /// Record that `val` is wanted at `pos` in `alloc`.
    fn emit_dest(
        &mut self,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        pos: PackedMovePosition<E>,
        val: Val<E>,
        alloc: Allocation<E>,
    ) {
        trace!("move generation: emit dest {val:?} at {pos:?} is {alloc:?}");
        counts.half_move_dests.inc();
        event!(events, HalfMoveDest { pos, val, alloc });
        self.dests.push((HalfMoveKey::new(pos, val), alloc));
    }

    /// Emit the half-moves for the spills created by spill placement.
    fn emit_spills(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        liveness: &Liveness<E>,
        live_ranges: &LiveRanges<E>,
        spill_slots: &SpillSlots<E>,
        spill_placement: &SpillPlacement<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        let func = input.func;

        for spill_site in spill_placement.spills().iter().copied() {
            let span = spill_site.span();
            let val = span.val(live_ranges);
            let block = span.block(func, live_ranges);
            let home = val.stack_home(spill_slots).unwrap();
            let dst = Allocation::Stack(home);
            let arrives_in = span
                .allocation(live_ranges, spill_slots)
                .expect("a span we spill from holds its value in a register");

            if spill_site.point() != block.end_point(input) {
                let pos = PackedMovePosition::point(spill_site.point());
                let key_val = self.val_for_spill_key(input, output, block, val, pos)?;
                self.emit_spill(counts, events, pos, key_val, arrives_in, dst);
                continue;
            }

            // The value is defined by the instruction that terminates the
            // block, so we can't place the move in the block itself. This means
            // the move is logically pushed to the block's successor edges, so
            // we handle this in the same way we handle block-call arguments,
            // which are also logically defined on the edge.
            let input_block = func.block(block.with_repr32());
            for (index, succ) in input_block.successors().enumerate() {
                let succ = output.with_repr::<E, _>(succ)?;

                // Don't bother emitting the move on edges where the value isn't
                // live.
                if !succ.is_live_in(liveness, val) {
                    continue;
                }

                let pos = edge_position(
                    input,
                    EdgeData {
                        succ,
                        pred: block,
                        index: u16::try_from(index).unwrap(),
                    },
                )?;
                self.emit_spill(counts, events, pos, val, arrives_in, dst);
            }
        }

        Ok(())
    }

    /// Get the value a spill at `pos` in `block` should be filed under.
    ///
    /// Normally this is the given `val` itself, but block parameters are keyed
    /// by their associated block-call arguments.
    fn val_for_spill_key(
        &self,
        input: &Input<'_, impl InputFunction>,
        output: &mut OutputInner<E>,
        block: Block<E>,
        val: Val<E>,
        pos: PackedMovePosition<E>,
    ) -> IResult<Val<E>> {
        let Some((_, k)) = self.param_of[val].filter(|&(b, _)| b == block) else {
            return Ok(val);
        };

        for e in self.incoming_edges(block) {
            let edge = self.edges[e];
            if edge_position(input, edge)? == pos {
                return self.block_call_arg(input, output, edge, k);
            }
        }

        Ok(val)
    }

    /// Record the half moves for a single spill.
    fn emit_spill(
        &mut self,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        pos: PackedMovePosition<E>,
        val: Val<E>,
        arrives_in: Allocation<E>,
        dst: Allocation<E>,
    ) {
        if let Entry::Vacant(entry) = self.sources.entry(HalfMoveKey::new(pos, val)) {
            trace!("move generation: emit source {val:?} at {pos:?} is {arrives_in:?}");
            counts.half_move_sources.inc();
            entry.insert(arrives_in);
            event!(
                events,
                HalfMoveSource {
                    pos,
                    val,
                    alloc: arrives_in,
                    replaced: None
                }
            );
        }
        self.emit_dest(counts, events, pos, val, dst);
    }

    /// Join the destination halves against the source halves, turning each pair
    /// into a full move.
    fn resolve(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
    ) {
        let mut dests = core::mem::take(&mut self.dests);

        // One destination can be asked for multiple times: two spans beginning
        // at one point can share an allocation, and a value can be both live
        // across an edge and passed as an argument on it. In either case, we
        // only need to move a value into the destination once.
        dests.sort_unstable();
        dests.dedup();

        for (key, dst) in dests.drain(..) {
            let src = self.sources.get(&key).copied();
            let HalfMoveKey { pos, val } = key;

            if Self::should_remat(input, dst, src, val) {
                let Allocation::Reg(RegAllocation::Reg(dest)) = dst else {
                    unreachable!("we only ever remat into single reg")
                };
                trace!("move generation: rematerialize {val:?} into {dest:?} at {pos:?}");
                counts.remats_emitted.inc();
                event!(events, RematEmitted { pos, val, dest });
                self.remats.push((pos, Remat { val, dest }));
                continue;
            }

            let Some(src) = src else {
                unreachable!(
                    "{val:?} is wanted in {dst:?} at {pos:?}, but it is neither available there \
                     nor rematerializable",
                );
            };

            event!(events, MoveResolved { pos, val, src, dst });
            self.batch_moves.push((pos, BatchMove { src, dst, val }));
        }

        debug_assert!(dests.is_empty());
        self.dests = dests;
    }

    /// Should we rematerialize `val` into `dst`, rather than move it from `src`?
    fn should_remat(
        input: &Input<'_, impl InputFunction>,
        dst: Allocation<E>,
        src: Option<Allocation<E>>,
        val: Val<E>,
    ) -> bool {
        // We only support rematerializing into a single register.
        if !matches!(dst, Allocation::Reg(RegAllocation::Reg(_))) {
            return false;
        }

        let Some(cost) = input.func.value(val.with_repr32()).remat_cost() else {
            return false;
        };

        // Without a source, our only option is rematerialization.
        let Some(src) = src else {
            return true;
        };

        // If we already have the value in place, don't rematerialize it.
        if src == dst {
            return false;
        }

        match src {
            Allocation::Reg(_) => cost <= RematCost::CheaperThanMove,
            Allocation::Stack(_) => cost <= RematCost::CheaperThanReload,
        }
    }

    /// Sequentialize each position's batch and turn it into edits.
    fn sequentialize(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        region_allocation: &RegionAllocation<E>,
        spill_slots: &mut SpillSlots<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        #[cfg(feature = "visualizer")]
        let events_start = events.len();

        self.batch_moves.sort_unstable_by_key(|&(pos, _)| pos);

        // Sequentialize each position's moves.
        let mut batch_moves = core::mem::take(&mut self.batch_moves);
        let result = (|| -> IResult<()> {
            for chunk in batch_moves.chunk_by(|a, b| a.0 == b.0) {
                self.sequentialize_batch(
                    input,
                    counts,
                    events,
                    region_allocation,
                    spill_slots,
                    output,
                    chunk,
                )?;
            }
            Ok(())
        })();
        batch_moves.clear();
        self.batch_moves = batch_moves;
        result?;

        // Rematerializations go after the moves at their position: they read
        // nothing themselves, but they might overwrite something that needed to
        // be read.
        let mut remats = core::mem::take(&mut self.remats);
        remats.sort_unstable_by_key(|&(pos, _)| pos);
        let result = (|| -> IResult<()> {
            for &(pos, remat) in remats.iter() {
                let edit =
                    edit_at_position(input, counts, events, output, pos, EdgeEdit::Remat(remat))?;
                self.edits.push((pos, edit));
            }
            Ok(())
        })();
        remats.clear();
        self.remats = remats;
        result?;

        self.edits.sort_by_key(|&(pos, _)| pos);

        // The sort just moved every move edit that a rematerialization landed
        // in front of, so the indices the events recorded as they went are
        // stale.
        #[cfg(feature = "visualizer")]
        remap_move_emitted_events(events, events_start, &self.edits);

        Ok(())
    }

    /// Sequentialize the batch of moves at a single position.
    fn sequentialize_batch(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        region_allocation: &RegionAllocation<E>,
        spill_slots: &mut SpillSlots<E>,
        output: &mut OutputInner<E>,
        chunk: &[(PackedMovePosition<E>, BatchMove<E>)],
    ) -> IResult<()> {
        let machine = input.machine;
        let pos = chunk[0].0;
        let span = pos.range(input);

        let mut expanded = core::mem::take(&mut self.expanded);
        let mut solved = core::mem::take(&mut self.solved);
        let mut solver = core::mem::replace(&mut self.solver, ParallelMoveSolver::new());
        debug_assert!(expanded.is_empty() && solved.is_empty());

        let result = (|| -> IResult<()> {
            for &(_, batch_move) in chunk {
                expand_groups(machine, spill_slots, output, batch_move, &mut expanded)?;
            }

            // Expanding batch moves into scalar moves can result in duplicates.
            expanded.sort_unstable();
            expanded.dedup_by_key(|&mut (move_, _)| move_);

            let overlaps = |a: ScalarAllocation<E>, b: ScalarAllocation<E>| {
                Interfere::interfere(machine, a, b)
            };

            let mut scratch_failed = false;
            let scratch = |mv: ParallelMove<E>,
                           avoid: &[ScalarAllocation<E>]|
             -> Option<ScalarAllocation<E>> {
                // Get the move's value's register bank
                let i = expanded.binary_search_by_key(&mv, |&(m, _)| m).unwrap();
                let bank = expanded[i].1.reg_bank(input);

                debug_assert!(
                    match (mv.src, mv.dst) {
                        (ScalarAllocation::Reg(reg), _) | (_, ScalarAllocation::Reg(reg)) =>
                            reg.with_repr32().bank(machine) == bank,
                        _ => true,
                    },
                    "{mv:?} names a register from a different bank than the value it moves",
                );

                // We are either breaking a move cycle or picking a temporary
                // register in a stack-to-stack move; select the appropriate
                // counter.
                let stack_to_stack = matches!(
                    (mv.src, mv.dst),
                    (ScalarAllocation::Stack(_), ScalarAllocation::Stack(_))
                );
                let (counter, reason) = if stack_to_stack {
                    (
                        &mut counts.stack_to_stack_moves,
                        ScratchReason::StackToStack,
                    )
                } else {
                    (&mut counts.move_cycles_broken, ScratchReason::CycleBreak)
                };

                // If we have a register available, then use it.
                if let Some(reg) = find_scratch_reg(
                    machine,
                    region_allocation,
                    span.clone(),
                    bank,
                    |reg: Reg<E>| {
                        avoid
                            .iter()
                            .any(|&a| ScalarAllocation::interfere(machine, reg.into(), a))
                            // TODO: investigate whether lazily caching a
                            // `RegSet` of all the registers used in this batch
                            // improves perf.
                            || batch_uses_reg(machine, &expanded, reg)
                    },
                ) {
                    counter.inc();
                    let scratch = ScalarAllocation::Reg(reg);
                    event!(
                        events,
                        ScratchRegChosen {
                            pos,
                            mv,
                            scratch,
                            reason
                        }
                    );
                    return Some(scratch);
                }

                // No register is available, so we have to do an emergency spill
                // to memory. But we cannot spill to memory if that would itself
                // introduce a stack-to-stack move, so in this case we simply
                // cannot solve the register constraints.
                if matches!(mv.src, ScalarAllocation::Stack(_))
                    || matches!(mv.dst, ScalarAllocation::Stack(_))
                {
                    scratch_failed = true;
                    event!(events, ScratchRegUnavailable { pos, mv });
                    return None;
                }

                let Ok(slot) = spill_slots.emergency_slot(
                    counts,
                    events,
                    output,
                    bank.size(machine),
                    |slot: SpillSlot<E>| avoid.contains(&ScalarAllocation::Stack(slot)),
                ) else {
                    scratch_failed = true;
                    event!(events, ScratchRegUnavailable { pos, mv });
                    return None;
                };

                let scratch = ScalarAllocation::Stack(slot);
                counts.move_cycles_broken.inc();
                // An emergency slot is only ever reached from a cycle: a
                // stack-to-stack move returned above.
                event!(
                    events,
                    ScratchRegChosen {
                        pos,
                        mv,
                        scratch,
                        reason: ScratchReason::CycleBreak
                    }
                );
                Some(scratch)
            };

            let moves = expanded.iter().map(|&(mv, _)| mv);
            match solver.solve(moves, overlaps, scratch, &mut solved) {
                Ok(()) => {}
                Err(SolveError::NoScratch) => {
                    debug_assert!(scratch_failed);
                    return output.error(Error::TooManyLiveRegs);
                }
                Err(SolveError::EntityReprTooSmall) => {
                    return output.error(InternalError::EntityReprTooSmall);
                }
            }

            event!(
                events,
                ParallelMoveBatchSolved {
                    pos,
                    num_input_moves: expanded.len(),
                    num_solved_moves: solved.len()
                }
            );

            for mv in &solved {
                self.emit_move(input, counts, events, output, pos, into_move(*mv))?;
            }

            Ok(())
        })();

        expanded.clear();
        solved.clear();
        self.expanded = expanded;
        self.solved = solved;
        self.solver = solver;
        result
    }

    /// Emit a whole, sequentialized move.
    fn emit_move(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        output: &mut OutputInner<E>,
        pos: PackedMovePosition<E>,
        move_: Move<E>,
    ) -> IResult<()> {
        trace!("move generation: emit {move_:?} at {pos:?}");
        counts.moves_emitted.inc();
        event!(
            events,
            MoveEmitted {
                pos,
                move_,
                index: self.edits.len()
            }
        );

        let edit = edit_at_position(input, counts, events, output, pos, EdgeEdit::Move(move_))?;
        self.edits.push((pos, edit));
        Ok(())
    }
}

/// Renumber each logged `MoveEmitted` to where its edit ended up after the
/// edits were sorted.
///
/// The sort is stable and the moves were already in position order, so the
/// moves keep their relative order and the nth move edit is the one the nth
/// `MoveEmitted` describes.
#[cfg(feature = "visualizer")]
fn remap_move_emitted_events<E>(
    events: &mut EventsLog<E>,
    events_start: usize,
    edits: &[(PackedMovePosition<E>, Edit<E>)],
) where
    E: EntityRepr,
{
    let is_move = |edit: &Edit<E>| match edit {
        Edit::Move(_) => true,
        Edit::Remat(_) => false,
        Edit::CriticalEdge(edge) => matches!(edge.edit, EdgeEdit::Move(_)),
    };

    let mut moves = edits
        .iter()
        .enumerate()
        .filter(|(_, (_, edit))| is_move(edit));

    for event in events.iter_mut_from(events_start) {
        if let crate::events::Event::MoveEmitted { index, .. } = event {
            let (i, _) = moves
                .next()
                .expect("every `MoveEmitted` event has its own move edit");
            *index = i;
        }
    }
}

/// Does the instruction at `start` define `val`, with `start` at the point the
/// definition takes effect or at that instruction's boundary?
fn defines_val_at<E>(func: &impl InputFunction, val: Val<E>, start: LivePoint<E>) -> bool
where
    E: EntityRepr,
{
    func.inst(start.inst().with_repr32())
        .operands()
        .filter(|op| op.kind() == DefUse::Def && op.val() == Some(val.with_repr32()))
        .any(|op| {
            let def = LivePoint::new(start.inst(), op.pos());
            start == def || start == def.inst_boundary_at_or_before()
        })
}

/// Is a span for `val` that ends at `end` live-out of the given `block`?
fn span_is_live_out_of_block<E>(
    input: &Input<'_, impl InputFunction>,
    liveness: &Liveness<E>,
    val: Val<E>,
    block: Block<E>,
    end: LivePoint<E>,
) -> bool
where
    E: EntityRepr,
{
    end == block.end_point(input) && block.is_live_out(liveness, val)
}

/// Is a span for `val` that begins at `start` live-in to the given `block`?
fn span_is_live_in_to_block<E>(
    input: &Input<'_, impl InputFunction>,
    liveness: &Liveness<E>,
    val: Val<E>,
    block: Block<E>,
    start: LivePoint<E>,
) -> bool
where
    E: EntityRepr,
{
    start == block.start_point(input) && block.is_live_in(liveness, val)
}

/// Is `a` a better source than `b` for a value that is in both places at once?
///
/// Prefer register sources over stack sources, and then low-numbered registers
/// to high-numbered registers for determinism.
fn better_source<E>(a: Allocation<E>, b: Allocation<E>) -> bool
where
    E: EntityRepr,
{
    let rank = |alloc| match alloc {
        Allocation::Reg(_) => 0,
        Allocation::Stack(_) => 1,
    };
    (rank(a), a) < (rank(b), b)
}

/// Get the edit that puts `edit` at `pos`.
///
/// This is generally `edit` itself, unless the position is a critical edge, in
/// which case we need to explicitly call that out for the client to split.
fn edit_at_position<E>(
    input: &Input<'_, impl InputFunction>,
    counts: &mut Counts,
    events: &mut EventsLog<E>,
    output: &mut OutputInner<E>,
    pos: PackedMovePosition<E>,
    edit: EdgeEdit<E>,
) -> IResult<Edit<E>>
where
    E: EntityRepr,
{
    match pos.unpack() {
        MovePosition::Point(_) | MovePosition::Departure(_) => Ok(match edit {
            EdgeEdit::Move(mv) => Edit::Move(mv),
            EdgeEdit::Remat(remat) => Edit::Remat(remat),
        }),
        MovePosition::CriticalEdge { pred, succ } => {
            counts.critical_edge_edits.inc();
            let target = input
                .func
                .block(pred.with_repr32())
                .successors()
                .nth(succ)
                .unwrap();
            let target = output.with_repr::<E, _>(target)?;
            event!(
                events,
                CriticalEdgeEdit {
                    pred,
                    succ,
                    target,
                    edit
                }
            );
            Ok(Edit::CriticalEdge(CriticalEdgeEdit { target, succ, edit }))
        }
    }
}

/// Get the position for moves on the edge `pred --[index]--> succ`.
fn edge_position<E>(
    input: &Input<'_, impl InputFunction>,
    edge: EdgeData<E>,
) -> IResult<PackedMovePosition<E>>
where
    E: EntityRepr,
{
    // Can we place the move at the start of the successor? This requires that
    // successor only has one incoming edge (or else our move might clobber
    // other edges' values) and that it is not the entry block, whose implicit
    // edge from outside the function delivers the function's parameters.
    let succ = edge.succ.with_repr32();
    let succ_block = input.func.block(succ);
    if succ_block.len_predecessors() == 1 && succ != input.func.entry_block() {
        return Ok(PackedMovePosition::point(edge.succ.start_point(input)));
    }

    // Can we place the move just before the predecessor's terminator? The
    // predecessor must have a single successor (or else we might clobber other
    // edges' values) and its terminator must not read or write a register (or
    // else the terminator could clobber our move or we could clobber one of its
    // operands).
    let pred_block = input.func.block(edge.pred.with_repr32());
    if pred_block.len_successors() == 1 {
        let last = block_last_inst(&pred_block);
        if input.func.inst(last).operands_len() == 0 {
            let last = last
                .with_repr::<E>()
                .expect("every instruction index already fit in `E` in the earlier passes");
            return Ok(PackedMovePosition::departure(LivePoint::new(
                last,
                // The move goes at the terminator's early point, i.e. before
                // the terminator, because control jumps away from this block
                // once the terminator executes.
                Position::Early,
            )));
        }
    }

    // The edge is critical (or close enough), so we need the client to split it
    // so the move has a place to live.
    Ok(PackedMovePosition::critical_edge(edge.pred, edge.index))
}

/// Does anything in `moves` read or write `reg`?
fn batch_uses_reg<E>(machine: &Machine, moves: &[(ParallelMove<E>, Val<E>)], reg: Reg<E>) -> bool
where
    E: EntityRepr,
{
    let reg = ScalarAllocation::Reg(reg);
    moves.iter().any(|(m, _)| {
        Interfere::interfere(machine, m.src, reg) || Interfere::interfere(machine, m.dst, reg)
    })
}

/// Find an allocatable register of `bank` that holds nothing over `range` and
/// that `is_used` does not object to.
fn find_scratch_reg<E>(
    machine: &Machine,
    region_allocation: &RegionAllocation<E>,
    range: Range<LivePoint<E>>,
    bank: RegBank,
    is_used: impl Fn(Reg<E>) -> bool,
) -> Option<Reg<E>>
where
    E: EntityRepr,
{
    bank.stack_to_stack_move_regs(machine)
        .iter()
        .filter_map(|reg| reg.with_repr::<E>())
        .find(|&reg| region_allocation.is_reg_free(machine, reg, range.clone()) && !is_used(reg))
}

/// Expand a batch move, and its stack and register groups, into a set of scalar
/// moves (which is what the parallel-move solver actually understands).
fn expand_groups<E>(
    machine: &Machine,
    spill_slots: &SpillSlots<E>,
    output: &mut OutputInner<E>,
    batch_move: BatchMove<E>,
    out: &mut Vec<(ParallelMove<E>, Val<E>)>,
) -> IResult<()>
where
    E: EntityRepr,
{
    let BatchMove { src, dst, val } = batch_move;

    let len = src.len_scalars(machine, spill_slots);
    debug_assert_eq!(len, dst.len_scalars(machine, spill_slots));

    for i in 0..len {
        out.push((
            ParallelMove {
                src: src.nth_scalar(machine, spill_slots, output, i)?,
                dst: dst.nth_scalar(machine, spill_slots, output, i)?,
            },
            val,
        ));
    }

    Ok(())
}

fn into_move<E>(mv: ParallelMove<E>) -> Move<E>
where
    E: EntityRepr,
{
    match (mv.src, mv.dst) {
        (ScalarAllocation::Reg(from), ScalarAllocation::Reg(to)) => Move::RegReg { from, to },
        (ScalarAllocation::Reg(from), ScalarAllocation::Stack(to)) => Move::Spill { from, to },
        (ScalarAllocation::Stack(from), ScalarAllocation::Reg(to)) => Move::Reload { from, to },
        (ScalarAllocation::Stack(_), ScalarAllocation::Stack(_)) => {
            unreachable!("should have already resolved stack-to-stack moves: {mv:?}")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(feature = "visualizer")]
    use crate::events::Event as LoggedEvent;
    use crate::{
        Inst, RegClass,
        context::Context,
        error::{Error, InternalError},
        input::OperandConstraint,
        machine::RegClassMembers,
        output::StackAllocation,
        test::{TestFunction, TestInput, TestMachine},
    };
    use core::sync::atomic::{AtomicUsize, Ordering};
    use mutatis::{
        check::{Check, CheckResult},
        mutators as m,
    };
    #[cfg(feature = "visualizer")]
    use std::collections::{BTreeMap, BTreeSet};
    use std::{format, string::String, vec::Vec};

    /// Run every phase up through move generation, or `None` when allocation
    /// itself gave up, e.g. for want of registers, leaving nothing to check.
    fn generate(test_input: &TestInput) -> Result<Option<Context>, String> {
        let mut context = Context::new();
        assert!(context.is_reset());

        let result = test_input.with_input(|input| -> IResult<()> {
            let ctx = &mut context.context32;
            {
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
                } = &mut *ctx;
                let func = input.func;
                rpo.construct(func, dfs, output)?;
                region_tree.construct(func, counts, dfs, output)?;
                liveness.construct(func, counts, rpo, output)?;
                live_ranges.construct(input, counts, events, liveness, output)?;
            }
            crate::coalescing::coalesce(ctx, input)?;
            crate::region_allocation::region_allocate(ctx, input)?;
            crate::spill_slot_allocation::allocate_spill_slots(ctx, input)?;
            crate::spill_placement::place_spills(ctx, input)?;
            generate_moves(ctx, input)
        });

        if result.is_err() {
            return match context.context32.output.take_error() {
                // Not every function fits on every machine.
                InternalError::Error(Error::TooManyLiveRegs) => Ok(None),
                error => Err(format!("allocation failed: {error:?}")),
            };
        }

        Ok(Some(context))
    }

    /// One register's worth of a value: the `index`th register of a value in a
    /// register group, and the whole of any other value.
    ///
    /// Moves are what this pass emits and a move carries one register, so this
    /// is the granularity everything here works at: a member that is dropped,
    /// or crossed with another member, is a different `Part` arriving.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct Part {
        val: Val<u32>,
        index: usize,
    }

    /// As much machine state as the checks need: what each location holds.
    ///
    /// A location is always a single register or a single slot, never a group:
    /// the parts are what is tracked.
    #[derive(Default)]
    struct State {
        locs: Vec<(ScalarAllocation<u32>, Part)>,
    }

    impl State {
        /// The part in `alloc`, if the simulation knows what is there.
        fn read(&self, alloc: ScalarAllocation<u32>) -> Option<Part> {
            self.locs
                .iter()
                .find(|&&(a, _)| a == alloc)
                .map(|&(_, part)| part)
        }

        /// Put `part` in `alloc`, forgetting the contents of everything
        /// `alloc` overlaps.
        fn write(&mut self, machine: &Machine, alloc: ScalarAllocation<u32>, part: Option<Part>) {
            self.locs
                .retain(|&(a, _)| !Interfere::interfere(machine, a, alloc));
            if let Some(part) = part {
                self.locs.push((alloc, part));
            }
        }
    }

    /// How much of each kind of edit a run saw, for non-vacuity checking.
    #[derive(Default)]
    struct Seen {
        reg_regs: usize,
        spills: usize,
        reloads: usize,
        remats: usize,
        critical_edge_moves: usize,
        param_edges: usize,

        /// Parameters whose slot an edge has to fill from the argument's,
        /// which spill placement cannot do: it only ever stores a value into
        /// its own home.
        stack_params: usize,

        /// Edits atop the entry block, which is where the fills that spread a
        /// function parameter from its arrival to its other pieces go, and
        /// where nothing else can: an edge into the entry block has to put its
        /// moves elsewhere, since the function's own arrival shares the spot.
        entry_param_fills: usize,

        /// Spills and reloads of one member of a value that lives in a
        /// register group, which are the moves that group support adds.
        group_spills: usize,
        group_reloads: usize,
    }

    /// Run `edits` against `state`, in the order they were emitted.
    fn apply(
        state: &mut State,
        input: &Input<'_, TestFunction>,
        edits: &[Edit<u32>],
        seen: &mut Seen,
    ) {
        let machine = input.machine;

        for &edit in edits {
            let edit = match edit {
                Edit::Move(move_) => EdgeEdit::Move(move_),
                Edit::Remat(remat) => EdgeEdit::Remat(remat),
                Edit::CriticalEdge(CriticalEdgeEdit { edit, .. }) => {
                    seen.critical_edge_moves += 1;
                    edit
                }
            };

            let move_ = match edit {
                EdgeEdit::Move(move_) => move_,
                EdgeEdit::Remat(Remat { val, dest, .. }) => {
                    seen.remats += 1;
                    // Only a value that fits in one register is ever
                    // rematerialized, so the whole of it lands in `dest`.
                    state.write(
                        machine,
                        ScalarAllocation::Reg(dest),
                        Some(Part { val, index: 0 }),
                    );
                    continue;
                }
            };

            let (src, dst) = match move_ {
                Move::RegReg { from, to } => {
                    seen.reg_regs += 1;
                    (ScalarAllocation::Reg(from), ScalarAllocation::Reg(to))
                }
                Move::Spill { from, to } => {
                    seen.spills += 1;
                    (ScalarAllocation::Reg(from), ScalarAllocation::Stack(to))
                }
                Move::Reload { from, to } => {
                    seen.reloads += 1;
                    (ScalarAllocation::Stack(from), ScalarAllocation::Reg(to))
                }
            };

            let part = state.read(src);

            // A spill or reload of a value that occupies more than one
            // register moves a single member, which is what this pass had to
            // learn to do.
            if let Some(part) = part {
                if part.val.num_regs(input) > 1 {
                    match move_ {
                        Move::Spill { .. } => seen.group_spills += 1,
                        Move::Reload { .. } => seen.group_reloads += 1,
                        Move::RegReg { .. } => {}
                    }
                }
            }

            state.write(machine, dst, part);
        }
    }

    /// Check that the moves get every value where the allocation says it
    /// belongs.
    ///
    /// The check is compositional rather than a simulation. Every batch sits in
    /// a gap between two instructions, and the spans say what holds what on
    /// either side of it, so each gap can be checked on its own: start from the
    /// state going in, apply the batch, and see that the state coming out
    /// holds. Chaining those gives the property we want, with no fixpoint over
    /// the CFG.
    ///
    /// The gap at the top of a block and the gap before a terminator do need
    /// the control flow, and are checked once per edge, so that an edge needing
    /// a move and a sibling that does not are told apart.
    fn check_moves(test_input: &TestInput) -> Result<Seen, String> {
        let Some(context) = generate(test_input)? else {
            return Ok(Seen::default());
        };

        test_input.with_input(|input| -> Result<Seen, String> {
            let mut seen = Seen::default();

            let ctx = &context.context32;
            let func = input.func;
            let machine = input.machine;
            let liveness = &ctx.liveness;
            let live_ranges = &ctx.live_ranges;
            let spill_slots = &ctx.spill_slots;
            let edits = ctx.move_generation.edits();

            // A value's allocation, split into the locations that hold it,
            // one per register it occupies: a group into its members, and the
            // stack home of a value in a group into that value's slots.
            let parts_of = |val: Val<u32>,
                            alloc: Allocation<u32>|
             -> Vec<(ScalarAllocation<u32>, Part)> {
                match alloc {
                    Allocation::Reg(RegAllocation::Reg(reg)) => {
                        Vec::from([(ScalarAllocation::Reg(reg), Part { val, index: 0 })])
                    }
                    Allocation::Reg(RegAllocation::RegGroup(group)) => group
                        .members(machine)
                        .iter()
                        .enumerate()
                        .map(|(index, &reg)| (ScalarAllocation::Reg(reg), Part { val, index }))
                        .collect(),
                    Allocation::Stack(home) => home
                        .slots(spill_slots)
                        .enumerate()
                        .map(|(index, slot)| (ScalarAllocation::Stack(slot), Part { val, index }))
                        .collect(),
                }
            };

            // Every span that holds its value somewhere, with the allocation
            // the allocator gave it. One holding it nowhere neither puts
            // anything in place nor requires anything to be.
            let spans = live_ranges
                .spans()
                .filter_map(|span| {
                    Some((
                        span.val(live_ranges),
                        span.start(live_ranges),
                        span.end(live_ranges),
                        span.allocation(live_ranges, spill_slots)?,
                        span.block(func, live_ranges),
                    ))
                })
                .collect::<Vec<_>>();

            // Where each of spill placement's stores lands, worked out from
            // the shape of the CFG the way `emit_spills` does. Checking the
            // slots against these is what keeps the seeding below from simply
            // assuming that every store did its job.
            let mut stores = Vec::new();
            for site in ctx.spill_placement.spills() {
                let val = site.val(live_ranges);
                let block = site.span().block(func, live_ranges);
                if site.point() != block.end_point(input) {
                    stores.push((PackedMovePosition::point(site.point()), val));
                    continue;
                }
                let input_block = func.block(block);
                for (index, succ) in input_block.successors().enumerate() {
                    if !succ.is_live_in(liveness, val) {
                        continue;
                    }
                    let pos = edge_position(
                        input,
                        EdgeData {
                            succ,
                            pred: block,
                            index: u16::try_from(index).unwrap(),
                        },
                    )
                    .expect("the edge indices already fit, or generation would have failed");
                    stores.push((pos, val));
                }
            }

            // The values whose store lands in one of the batches at `at`.
            let filling = |at: &[PackedMovePosition<u32>]| {
                stores
                    .iter()
                    .filter(|&&(p, _)| at.contains(&p))
                    .map(|&(_, val)| val)
                    .collect::<Vec<_>>()
            };

            // Which value each slot holds at `point`: the one whose stack span
            // covers it, a slot being shared by values whose ranges do not
            // overlap. A span that *begins* here counts, unlike the registers
            // below, because spill placement hoists a store up the dominator
            // tree, so the store may be blocks away. That a reload is dominated
            // by its store is spill placement's property, tested there.
            //
            // Except for the values in `filling`, whose stores are in the very
            // batch about to be checked: seeding those would be assuming the
            // answer, and is exactly what let a store of the wrong value go
            // unnoticed. They have to be written by the batch instead.
            let slots_at = |point: LivePoint<u32>, filling: &[Val<u32>]| {
                let mut state = State::default();
                for &(val, start, end, alloc, _) in &spans {
                    if matches!(alloc, Allocation::Stack(_))
                        && start <= point
                        && point < end
                        && !filling.contains(&val)
                    {
                        for (alloc, part) in parts_of(val, alloc) {
                            state.write(machine, alloc, Some(part));
                        }
                    }
                }
                state
            };

            // What the stores at `pos` must have left in their slots. `rename`
            // says which value a slot's contents go by here, since on an edge a
            // parameter's slot holds the argument the predecessor passed.
            let stored_at = |pos: PackedMovePosition<u32>,
                             rename: &dyn Fn(Val<u32>) -> Val<u32>|
             -> Vec<(ScalarAllocation<u32>, Part)> {
                stores
                    .iter()
                    .filter(|&&(p, _)| p == pos)
                    .flat_map(|&(_, val)| {
                        let home = val
                            .stack_home(spill_slots)
                            .expect("a value being spilled has a stack home to spill it into");
                        let named = rename(val);
                        parts_of(val, Allocation::Stack(home))
                            .into_iter()
                            .map(move |(alloc, part)| (alloc, Part { val: named, ..part }))
                    })
                    .collect()
            };

            // The state going into the gap before `inst`: every span reaching
            // it, in the allocation it names. A span ending exactly here counts,
            // as it still holds the value going in.
            let state_in_gap = |inst: Inst, filling: &[Val<u32>]| {
                let point = LivePoint::new(inst, Position::Early);
                let mut state = slots_at(point, filling);
                for &(val, start, end, alloc, _) in &spans {
                    if start < point && point <= end {
                        for (alloc, part) in parts_of(val, alloc) {
                            state.write(machine, alloc, Some(part));
                        }
                    }
                }
                state
            };

            // What must be in place by the end of the gap before `inst`: every
            // span covering it, minus what `inst` defines and so does not exist.
            let needed_at = |inst: Inst| {
                let point = LivePoint::new(inst, Position::Early);
                let input_inst = func.inst(inst);
                let defines = |val| {
                    input_inst
                        .operands()
                        .any(|op| op.kind() == DefUse::Def && op.val() == Some(val))
                };
                spans
                    .iter()
                    .filter(|&&(val, start, end, ..)| {
                        start <= point && point < end && !defines(val)
                    })
                    .flat_map(|&(val, _, _, alloc, _)| parts_of(val, alloc))
                    .collect::<Vec<_>>()
            };

            // What `inst` reads, which the gap's moves must leave alone.
            let read_by = |inst: Inst| {
                let input_inst = func.inst(inst);
                let uses = |val| {
                    input_inst
                        .operands()
                        .any(|op| op.kind() == DefUse::Use && op.val() == Some(val))
                };
                needed_at(inst)
                    .into_iter()
                    .filter(|&(_, part)| uses(part.val))
                    .collect::<Vec<_>>()
            };

            let check = |state: &State,
                         needed: &[(ScalarAllocation<u32>, Part)],
                         what: &dyn core::fmt::Debug|
             -> Result<(), String> {
                for &(alloc, part) in needed {
                    if state.read(alloc) != Some(part) {
                        return Err(format!(
                            "{what:?}: {alloc:?} should hold {part:?} here, but it holds {:?}",
                            state.read(alloc),
                        ));
                    }
                }
                Ok(())
            };

            let batch = |pos: PackedMovePosition<u32>| {
                edits
                    .iter()
                    .filter(|&&(p, _)| p == pos)
                    .map(|&(_, edit)| edit)
                    .collect::<Vec<_>>()
            };

            // The gaps inside a block, both ends of which its spans describe.
            for (block, input_block) in func.blocks() {
                let insts = input_block
                    .insts()
                    .map(|(inst, _)| inst)
                    .collect::<Vec<_>>();
                let last = *insts
                    .last()
                    .expect("validation checked that a block has at least a terminator");
                let has_successors = input_block.len_successors() > 0;

                for (i, &inst) in insts.iter().enumerate() {
                    // The top of a block belongs to its incoming edges, and is
                    // checked per edge below.
                    if i == 0 {
                        continue;
                    }

                    let early = PackedMovePosition::point(LivePoint::new(inst, Position::Early));
                    let mut state = state_in_gap(inst, &filling(&[early]));
                    apply(&mut state, input, &batch(early), &mut seen);

                    // Spill placement's stores land here, in the gap before the
                    // instruction they were placed at. The ones it put at a
                    // block's exit go on the outgoing edges instead, and are
                    // checked per edge below.
                    check(&state, &stored_at(early, &|val| val), &(block, inst))?;

                    // Everything the instruction reads must be in place by
                    // now. Nothing runs between here and the instruction: a
                    // point edit is only ever at an early point, since
                    // `LivePoint::inst_boundary_after` always lands on one and
                    // `emit_half_moves` asserts it.
                    check(&state, &needed_at(inst), &(block, inst))?;

                    // The gap before a terminator ends with the moves for the
                    // outgoing edges, checked per edge below; everything else
                    // had to be in place before them, since they read it.
                    if inst == last && has_successors {
                        apply(
                            &mut state,
                            input,
                            &batch(PackedMovePosition::departure(LivePoint::new(
                                inst,
                                Position::Early,
                            ))),
                            &mut seen,
                        );
                        // An edge's moves must not clobber what the terminator
                        // still reads.
                        check(&state, &read_by(inst), &(block, inst))?;
                    }
                }
            }

            // The gap atop the entry block, which no edge covers: the loop
            // below walks real predecessor edges, and an edge into the entry
            // block never places its moves here anyway, since the function's
            // own arrival shares the position. So this is the only check the
            // entry parameters' fills ever face.
            {
                let entry = func.entry_block();
                let entry_start = entry.start_point(input);
                let pos = PackedMovePosition::point(entry_start);
                let params = func.block(entry).params().collect::<Vec<_>>();

                // The furthest-reaching piece of a parameter starting here is
                // where the caller left it, the rule `emit_entry_param_fills`
                // and `Output::block_param_allocs` both follow.
                let arrival = |param: Val<u32>| {
                    live_ranges
                        .spans()
                        .filter(|span| {
                            span.val(live_ranges) == param && span.start(live_ranges) == entry_start
                        })
                        .max_by_key(|span| (span.end(live_ranges), *span))
                        .and_then(|span| span.allocation(live_ranges, spill_slots))
                };

                // The parameters are left out of the slot seeding, not just
                // the values `filling` names: a parameter's stack piece is
                // written by the very batch under test, so seeding it would
                // be assuming what the fills are supposed to do.
                let mut unseeded = filling(&[pos]);
                unseeded.extend(params.iter().copied());
                let mut state = slots_at(entry_start, &unseeded);
                for &param in &params {
                    if let Some(alloc) = arrival(param) {
                        for (alloc, part) in parts_of(param, alloc) {
                            state.write(machine, alloc, Some(part));
                        }
                    }
                }

                let fills = batch(pos);
                seen.entry_param_fills += fills.len();
                apply(&mut state, input, &fills, &mut seen);

                // One piece held the parameter going in; all of them must hold
                // it coming out. That is what makes this no tautology: the
                // arrival is one span, the requirement is every span.
                let mut needed = Vec::new();
                for &(val, span_start, _, alloc, block) in &spans {
                    if block != entry || span_start != entry_start || !params.contains(&val) {
                        continue;
                    }
                    needed.extend(parts_of(val, alloc));
                }
                check(&state, &needed, &(entry, "arrival"))?;
                check(&state, &stored_at(pos, &|val| val), &(entry, "arrival"))?;
            }

            // Every edge on its own: both a parameter's value and the moves a
            // value needs can differ between edges into one block.
            for (pred, input_pred) in func.blocks() {
                let last = block_last_inst(&input_pred);
                let params_are_dead = |block: Block<u32>| {
                    func.block(block)
                        .params()
                        .all(|param| !block.is_live_in(liveness, param))
                };

                for (index, succ) in input_pred.successors().enumerate() {
                    let input_succ = func.block(succ);
                    let entry = succ.start_point(input);

                    // The three places this edge's moves can go.
                    let before_pos =
                        PackedMovePosition::departure(LivePoint::new(last, Position::Early));
                    let edge_pos =
                        PackedMovePosition::critical_edge(pred, u16::try_from(index).unwrap());
                    let arrival_pos = PackedMovePosition::point(entry);

                    // A move on the edge itself is legal only when the edge
                    // really is critical: neither block will take the move.
                    // The successor will not when another edge reaches it, and
                    // the entry block never will, since the function's own
                    // entry reaches it too.
                    let on_edge = batch(edge_pos);
                    if !on_edge.is_empty() {
                        let succ_takes_it =
                            input_succ.len_predecessors() == 1 && succ != func.entry_block();
                        let critical = !succ_takes_it
                            && (input_pred.len_successors() > 1
                                || func.inst(last).operands_len() > 0);
                        if !critical {
                            return Err(format!(
                                "the edge {pred:?} -[{index}]-> {succ:?} is not critical, so its \
                                 moves belong in a block rather than on the edge: {on_edge:?}",
                            ));
                        }
                        for edit in &on_edge {
                            let named = match edit {
                                Edit::CriticalEdge(on_edge) => {
                                    on_edge.target == succ && on_edge.succ == index
                                }
                                _ => false,
                            };
                            if !named {
                                return Err(format!(
                                    "{edit:?} is at the position of the edge {pred:?} \
                                     -[{index}]-> {succ:?} but does not name that edge",
                                ));
                            }
                        }
                    }

                    // The predecessor's live-out values, as its spans name them.
                    let mut state = slots_at(entry, &filling(&[before_pos, edge_pos, arrival_pos]));
                    for &(val, _, end, alloc, block) in &spans {
                        if block == pred && end == pred.end_point(input) {
                            for (alloc, part) in parts_of(val, alloc) {
                                state.write(machine, alloc, Some(part));
                            }
                        }
                    }

                    // Everything between the two blocks, in order: the end of
                    // the gap before the terminator, the edge itself, then the
                    // top of the successor.
                    let before = batch(before_pos);
                    let arrival = batch(arrival_pos);
                    let moved = !before.is_empty() || !on_edge.is_empty() || !arrival.is_empty();
                    apply(&mut state, input, &before, &mut seen);
                    apply(&mut state, input, &on_edge, &mut seen);
                    apply(&mut state, input, &arrival, &mut seen);

                    // A parameter is defined on this edge by the argument the
                    // predecessor passes, so that is what must arrive.
                    let params = input_succ.params().collect::<Vec<_>>();
                    let args = input_pred.successor_block_args(index).collect::<Vec<_>>();
                    assert_eq!(
                        params.len(),
                        args.len(),
                        "validation checked that an edge passes one argument per parameter",
                    );

                    let mut needed = Vec::new();
                    for &(val, start, end, alloc, block) in &spans {
                        if block != succ || start > entry || entry >= end {
                            continue;
                        }
                        if !succ.is_live_in(liveness, val) {
                            continue;
                        }
                        // A parameter's locations must hold the argument's
                        // parts, member for member.
                        let arg = match params.iter().position(|&param| param == val) {
                            Some(i) => args[i],
                            None => val,
                        };
                        if arg != val && matches!(alloc, Allocation::Stack(_)) {
                            seen.stack_params += 1;
                        }
                        needed.extend(
                            parts_of(val, alloc)
                                .into_iter()
                                .map(|(alloc, part)| (alloc, Part { val: arg, ..part })),
                        );
                    }

                    check(&state, &needed, &(pred, index, succ))?;

                    // And the stores spill placement asked for on this edge,
                    // under the same renaming: a parameter's slot holds the
                    // argument, not the parameter.
                    let rename = |val| match params.iter().position(|&param| param == val) {
                        Some(i) => args[i],
                        None => val,
                    };
                    for pos in [before_pos, edge_pos, arrival_pos] {
                        check(&state, &stored_at(pos, &rename), &(pred, index, succ))?;
                    }

                    if moved && !params.is_empty() && !params_are_dead(succ) {
                        seen.param_edges += 1;
                    }
                }
            }

            Ok(seen)
        })
    }

    /// The pipeline through this pass never panics or trips a debug assertion,
    /// and leaves a context that resets.
    #[test]
    fn the_whole_pipeline_runs() -> CheckResult<TestInput> {
        Check::new()
            .iters(1_000)
            .run(|test_input: &TestInput| -> Result<(), String> {
                if let Some(mut context) = generate(test_input)? {
                    context.reset();
                    assert!(context.is_reset());
                }
                Ok(())
            })
    }

    /// A value that lives in a register group is spilled and reloaded one
    /// member at a time, each member in its own slot.
    ///
    /// The property test covers this too, but only when a random input happens
    /// to spill a group; this pins the shape of the edits down.
    #[test]
    fn every_member_of_a_register_group_is_spilled_and_reloaded() {
        let class = RegClass::try_new(usize::from(TestMachine::GROUP_CLASS)).unwrap();
        let test_input = TestInput::with_group_use_constraints(&[
            OperandConstraint::Stack,
            OperandConstraint::Reg(class),
        ]);
        let context = generate(&test_input).unwrap().unwrap();
        let ctx = &context.context32;

        test_input.with_input(|input| {
            let machine = input.machine;
            let RegClassMembers::Groups(groups) = class.members(machine) else {
                panic!("rc0 is a class of register groups");
            };
            let members = groups[0].members(machine);

            let val = Val::<u32>::try_new(0).unwrap();

            // The value's stack home is a group of slots, one per register
            // group member, and the spills and reloads below name exactly
            // those slots, in member order.
            let home = val.stack_home(&ctx.spill_slots);
            let Some(StackAllocation::SpillSlotGroup(group)) = home else {
                panic!("a value in a class of register groups has a group of slots, got {home:?}");
            };
            let slots = group.members(&ctx.spill_slots).to_vec();
            assert_eq!(slots.len(), members.len(), "one slot per member");
            assert_ne!(slots[0], slots[1], "the members do not share a slot");
            assert!(
                val.spill_slots(&ctx.spill_slots).eq(slots.iter().copied()),
                "the value's slots are the group's slots",
            );

            let mut spills = Vec::new();
            let mut reloads = Vec::new();
            for &(_, edit) in ctx.move_generation.edits() {
                match edit {
                    Edit::Move(Move::Spill { from, to }) => spills.push((from, to)),
                    Edit::Move(Move::Reload { from, to }) => reloads.push((from, to)),
                    _ => {}
                }
            }

            let expected_spills = members
                .iter()
                .zip(&slots)
                .map(|(&reg, &slot)| (reg, slot))
                .collect::<Vec<_>>();
            let expected_reloads = expected_spills
                .iter()
                .map(|&(reg, slot)| (slot, reg))
                .collect::<Vec<_>>();
            spills.sort_unstable();
            reloads.sort_unstable();
            assert_eq!(spills, expected_spills);
            assert_eq!(reloads, expected_reloads);
        });
    }

    /// A block parameter that lives in a spill slot is filled from the slot
    /// its argument lives in, a move that only the edge can make: spill
    /// placement stores a value into its own home and never into another
    /// value's.
    ///
    /// The property test covers this too, but only when a random input happens
    /// to leave a parameter on the stack; this pins the shape of the edits
    /// down.
    #[test]
    fn a_parameter_on_the_stack_is_filled_from_its_argument() {
        let test_input = TestInput::with_stack_param_and_arg();
        let context = generate(&test_input).unwrap().unwrap();
        let ctx = &context.context32;

        // The moves put every value where the allocation says it belongs; the
        // rest of this says which moves those are.
        check_moves(&test_input).unwrap();

        test_input.with_input(|input| {
            let home = |val: Val<u32>| match val.stack_home(&ctx.spill_slots) {
                Some(StackAllocation::SpillSlot(slot)) => slot,
                home => panic!("{val:?} lives in a single slot, got {home:?}"),
            };
            let arg = home(Val::try_new(0).unwrap());
            let param = home(Val::try_new(1).unwrap());
            assert_ne!(
                arg, param,
                "the argument is live past the edge, so it cannot share the parameter's slot",
            );

            // The block has one predecessor, so the edge's moves go atop it.
            let block = Block::<u32>::try_new(1).unwrap();
            let pos = PackedMovePosition::point(block.start_point(input));
            let edits = ctx
                .move_generation
                .edits()
                .iter()
                .filter(|&&(p, _)| p == pos)
                .map(|&(_, edit)| edit)
                .collect::<Vec<_>>();

            // One slot-to-slot move, which the solver routes through a
            // scratch register.
            let [
                Edit::Move(Move::Reload { from, to: via }),
                Edit::Move(Move::Spill { from: back, to }),
            ] = edits[..]
            else {
                panic!("expected the argument's slot reloaded and stored into the parameter's atop {block:?}, got {edits:?}");
            };
            assert_eq!(from, arg);
            assert_eq!(back, via, "the store writes back what the reload read");
            assert_eq!(to, param);
        });
    }

    /// The inputs the property check starts its random walk from.
    fn seeds() -> Vec<TestInput> {
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();
        let group_class = RegClass::try_new(usize::from(TestMachine::GROUP_CLASS)).unwrap();
        std::vec![
            TestInput::default(),
            TestInput::with_spilled_merge_param(),
            TestInput::with_stack_param_and_arg(),
            TestInput::with_use_constraints(&[OperandConstraint::Reg(class)]),
            TestInput::with_use_constraints(&[
                OperandConstraint::Stack,
                OperandConstraint::Reg(class),
            ]),
            // A value in a register group that has to be on the stack for one
            // use and in its group for another: the spills and reloads of a
            // single group member that this pass had to learn to do.
            TestInput::with_group_use_constraints(&[
                OperandConstraint::Stack,
                OperandConstraint::Reg(group_class),
            ]),
            TestInput::with_group_use_constraints(&[
                OperandConstraint::Reg(group_class),
                OperandConstraint::Stack,
                OperandConstraint::Reg(group_class),
            ]),
            TestInput::with_reuse_def(OperandConstraint::Any),
            TestInput::with_block_arg_constraints(OperandConstraint::Any, OperandConstraint::Stack),
            // Parameters of the *entry* block, the only ones no edge fills.
            TestInput::with_two_entry_params(),
            TestInput::with_an_entry_param_read_two_ways(),
            TestInput::with_entry_params_in_two_banks(),
            TestInput::with_a_self_looping_entry_block(),
            TestInput::with_a_spilled_self_looping_entry_param(),
            TestInput::with_a_recomputed_read_before_a_spill_and_a_reload(),
            // A value carried past a block that wants every register, cheap
            // enough to recompute that the crossing piece holds it nowhere and
            // the moves at the far end have no source. Not `AlwaysRemat`, so
            // the other costs' path is reached too.
            {
                let mut test_input = TestInput::with_a_value_carried_past_a_crowded_block(false);
                test_input.set_remat_costs(Some(RematCost::CheaperThanReload));
                test_input
            },
        ]
    }

    /// The moves put every value where the allocation says it belongs, at
    /// every boundary and along every edge. The counters make sure the inputs
    /// really reach every kind of move.
    #[test]
    fn move_generation_properties() -> CheckResult<TestInput> {
        static REG_REGS: AtomicUsize = AtomicUsize::new(0);
        static SPILLS: AtomicUsize = AtomicUsize::new(0);
        static RELOADS: AtomicUsize = AtomicUsize::new(0);
        static REMATS: AtomicUsize = AtomicUsize::new(0);
        static CRITICAL_EDGE_MOVES: AtomicUsize = AtomicUsize::new(0);
        static PARAM_EDGES: AtomicUsize = AtomicUsize::new(0);
        static STACK_PARAMS: AtomicUsize = AtomicUsize::new(0);
        static ENTRY_PARAM_FILLS: AtomicUsize = AtomicUsize::new(0);
        static GROUP_SPILLS: AtomicUsize = AtomicUsize::new(0);
        static GROUP_RELOADS: AtomicUsize = AtomicUsize::new(0);

        let result = Check::new().iters(10_000).run_with(
            m::default::<TestInput>(),
            seeds(),
            |test_input: &TestInput| -> Result<(), String> {
                let seen = check_moves(test_input)?;
                REG_REGS.fetch_add(seen.reg_regs, Ordering::Relaxed);
                SPILLS.fetch_add(seen.spills, Ordering::Relaxed);
                RELOADS.fetch_add(seen.reloads, Ordering::Relaxed);
                REMATS.fetch_add(seen.remats, Ordering::Relaxed);
                CRITICAL_EDGE_MOVES.fetch_add(seen.critical_edge_moves, Ordering::Relaxed);
                PARAM_EDGES.fetch_add(seen.param_edges, Ordering::Relaxed);
                STACK_PARAMS.fetch_add(seen.stack_params, Ordering::Relaxed);
                ENTRY_PARAM_FILLS.fetch_add(seen.entry_param_fills, Ordering::Relaxed);
                GROUP_SPILLS.fetch_add(seen.group_spills, Ordering::Relaxed);
                GROUP_RELOADS.fetch_add(seen.group_reloads, Ordering::Relaxed);
                Ok(())
            },
        );

        if result.is_ok() {
            for (what, counter) in [
                ("register-to-register move", &REG_REGS),
                ("spill", &SPILLS),
                ("reload", &RELOADS),
                ("rematerialization", &REMATS),
                ("move on a critical edge", &CRITICAL_EDGE_MOVES),
                ("edge into a block with parameters", &PARAM_EDGES),
                (
                    "parameter filled in its slot from an argument",
                    &STACK_PARAMS,
                ),
                ("fill atop the entry block", &ENTRY_PARAM_FILLS),
                ("spill of a register group's member", &GROUP_SPILLS),
                ("reload of a register group's member", &GROUP_RELOADS),
            ] {
                assert!(
                    counter.load(Ordering::Relaxed) > 0,
                    "no random input produced a {what}, so the properties are vacuous",
                );
            }
        }

        result
    }
    /// Every `MoveEmitted` event's index addresses the edit its move became.
    #[cfg(feature = "visualizer")]
    #[test]
    fn every_move_emitted_addresses_its_edit() -> CheckResult<TestInput> {
        // How many runs had a move edit after a rematerialization, which is
        // exactly the case where the index a move was emitted with is not the
        // index it ends up at.
        static SHIFTED: AtomicUsize = AtomicUsize::new(0);

        let result = Check::new().iters(10_000).run_with(
            m::default::<TestInput>(),
            seeds(),
            |test_input: &TestInput| -> Result<(), String> {
                let Some(context) = generate(test_input)? else {
                    return Ok(());
                };
                let ctx = &context.context32;
                let edits = ctx.move_generation.edits();

                let is_move = |edit: &Edit<u32>| {
                    matches!(
                        edit,
                        Edit::Move(_)
                            | Edit::CriticalEdge(CriticalEdgeEdit {
                                edit: EdgeEdit::Move(_),
                                ..
                            })
                    )
                };

                let mut num_emitted = 0;
                for (_, event) in ctx.events.iter() {
                    let LoggedEvent::MoveEmitted { pos, move_, index } = *event else {
                        continue;
                    };
                    num_emitted += 1;

                    let (edit_pos, edit) = *edits.get(index).ok_or_else(|| {
                        format!("{move_:?} claims edit {index}, past the end of the edit list")
                    })?;
                    if edit_pos != pos {
                        return Err(format!(
                            "{move_:?} claims edit {index}, which is at {edit_pos:?}, not {pos:?}",
                        ));
                    }
                    let emitted = match edit {
                        Edit::Move(mv) => mv,
                        Edit::CriticalEdge(CriticalEdgeEdit {
                            edit: EdgeEdit::Move(mv),
                            ..
                        }) => mv,
                        _ => return Err(format!("edit {index} is {edit:?}, not a move")),
                    };
                    if emitted != move_ {
                        return Err(format!("edit {index} is {emitted:?}, not {move_:?}"));
                    }
                }

                // And no move edit went unannounced.
                let num_move_edits = edits.iter().filter(|(_, edit)| is_move(edit)).count();
                if num_emitted != num_move_edits {
                    return Err(format!(
                        "{num_emitted} `MoveEmitted` events for {num_move_edits} move edits",
                    ));
                }

                let first_remat = edits.iter().position(|(_, edit)| !is_move(edit));
                let last_move = edits.iter().rposition(|(_, edit)| is_move(edit));
                if let (Some(first_remat), Some(last_move)) = (first_remat, last_move)
                    && first_remat < last_move
                {
                    SHIFTED.fetch_add(1, Ordering::Relaxed);
                }

                Ok(())
            },
        );

        if result.is_ok() {
            assert!(
                SHIFTED.load(Ordering::Relaxed) > 0,
                "no random input put a move edit after a rematerialization, so the property \
                 never sees an index that moved",
            );
        }

        result
    }

    /// Every resolved move has the two halves it was joined from.
    #[cfg(feature = "visualizer")]
    #[test]
    fn every_resolved_move_has_both_halves() -> CheckResult<TestInput> {
        Check::new().iters(10_000).run_with(
            m::default::<TestInput>(),
            seeds(),
            |test_input: &TestInput| -> Result<(), String> {
                let Some(context) = generate(test_input)? else {
                    return Ok(());
                };
                let ctx = &context.context32;

                let mut sources = BTreeMap::new();
                let mut dests = BTreeMap::new();
                let mut resolved = Vec::new();
                for (_, event) in ctx.events.iter() {
                    match *event {
                        LoggedEvent::HalfMoveSource {
                            pos, val, alloc, ..
                        } => {
                            // A later source displaces an earlier one, and the
                            // last one is the one `resolve` reads.
                            sources.insert((pos, val), alloc);
                        }
                        LoggedEvent::HalfMoveDest { pos, val, alloc } => {
                            dests.entry((pos, val)).or_insert_with(Vec::new).push(alloc);
                        }
                        LoggedEvent::MoveResolved { pos, val, src, dst } => {
                            resolved.push((pos, val, src, dst));
                        }
                        _ => continue,
                    }
                }

                for (pos, val, src, dst) in resolved {
                    match sources.get(&(pos, val)) {
                        Some(&alloc) if alloc == src => {}
                        Some(&alloc) => {
                            return Err(format!(
                                "the move of {val:?} at {pos:?} reads {src:?}, but the last \
                                 source there was {alloc:?}",
                            ));
                        }
                        None => {
                            return Err(format!(
                                "the move of {val:?} at {pos:?} reads {src:?}, which was never \
                                 logged as a source",
                            ));
                        }
                    }
                    if !dests.get(&(pos, val)).is_some_and(|ds| ds.contains(&dst)) {
                        return Err(format!(
                            "the move of {val:?} at {pos:?} writes {dst:?}, which was never \
                             logged as a destination",
                        ));
                    }
                }

                Ok(())
            },
        )
    }

    /// Every rematerialization fills a destination that was asked for, in a
    /// register, with a value that can be rematerialized.
    #[cfg(feature = "visualizer")]
    #[test]
    fn every_remat_fills_a_logged_dest() -> CheckResult<TestInput> {
        Check::new().iters(10_000).run_with(
            m::default::<TestInput>(),
            seeds(),
            |test_input: &TestInput| -> Result<(), String> {
                let Some(context) = generate(test_input)? else {
                    return Ok(());
                };
                let ctx = &context.context32;

                let mut dests = BTreeSet::new();
                let mut remats = Vec::new();
                for (_, event) in ctx.events.iter() {
                    match *event {
                        LoggedEvent::HalfMoveDest { pos, val, alloc } => {
                            dests.insert((pos, val, alloc));
                        }
                        LoggedEvent::RematEmitted { pos, val, dest } => {
                            remats.push((pos, val, dest));
                        }
                        _ => continue,
                    }
                }

                for (pos, val, dest) in remats {
                    let dst = Allocation::Reg(RegAllocation::Reg(dest));
                    if !dests.contains(&(pos, val, dst)) {
                        return Err(format!(
                            "{val:?} is rematerialized into {dest:?} at {pos:?}, which was never \
                             logged as a destination",
                        ));
                    }
                    if test_input
                        .func
                        .value(val.with_repr32())
                        .remat_cost()
                        .is_none()
                    {
                        return Err(format!(
                            "{val:?} is rematerialized but not rematerializable"
                        ));
                    }
                }

                Ok(())
            },
        )
    }

    /// A whole run's event log is valid JSON, whatever it holds.
    #[cfg(feature = "visualizer")]
    #[test]
    fn the_event_log_serializes() {
        let mut kinds = BTreeSet::new();

        // The seeds, plus a critical edge, plus the seeds again with every
        // value rematerializable: between them they reach every corner of move
        // generation.
        let mut inputs = seeds();
        inputs.push(TestInput::with_a_critical_edge());
        inputs.extend(seeds().into_iter().map(|mut test_input| {
            test_input.set_remat_costs(Some(RematCost::AlwaysRemat));
            test_input
        }));

        for test_input in inputs {
            let Some(context) = generate(&test_input).unwrap() else {
                continue;
            };
            let events = Vec::from_iter(context.context32.events.iter().map(|(_, event)| event));
            assert!(!events.is_empty());

            let json = serde_json::to_string(&events).unwrap();
            let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
            let parsed = parsed.as_array().unwrap();
            assert_eq!(parsed.len(), events.len());

            for event in parsed {
                kinds.insert(String::from(event["kind"].as_str().unwrap()));
            }
        }

        // Each of move generation's events should have appeared somewhere
        // above.
        for kind in [
            "HalfMoveSource",
            "HalfMoveDest",
            "MoveResolved",
            "RematEmitted",
            "ScratchRegChosen",
            "ParallelMoveBatchSolved",
            "MoveEmitted",
            "CriticalEdgeEdit",
        ] {
            assert!(kinds.contains(kind), "no seed input logged a {kind} event");
        }
    }
}
