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
    error::{IResult, InternalError},
    events::EventsLog,
    hash_map::{Entry, FxHashMap},
    input::{
        DefUse, Input, InputBlock, InputFunction, InputInst as _, InputValue as _, Position,
        RematCost,
    },
    live_ranges::{LivePoint, LiveRanges, LiveSpan, Reservation, sort_spans},
    liveness::{Liveness, block_first_inst, block_last_inst},
    machine::{Interfere, Machine, Reg, RegBank},
    output::{
        Allocation, CriticalEdgeEdit, EdgeEdit, Edit, Move, OutputInner, RegAllocation, Remat,
        ScalarAllocation, StackAllocation,
    },
    parallel_moves::{ParallelMove, ParallelMoveSolver, ScratchReason, ScratchSource, SolveError},
    region_allocation::RegionAllocation,
    rpo::Rpo,
    spill_placement::SpillPlacement,
    spill_slot_allocation::{SpillSlot, SpillSlotSize, SpillSlots},
    spilled_live_ranges::SpilledLiveRanges,
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

    context.move_generation.generate(
        input,
        &mut context.counts,
        &mut context.events,
        &context.rpo,
        &context.liveness,
        &context.live_ranges,
        &context.region_allocation,
        &mut context.spill_slots,
        &context.spill_placement,
        &context.spilled_live_ranges,
        &mut context.output,
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

    fn borrow_range(self, input: &Input<'_, impl InputFunction>) -> Range<LivePoint<E>> {
        self.unpack().borrow_range(input)
    }

    fn occupancy_range(self, input: &Input<'_, impl InputFunction>) -> Range<LivePoint<E>> {
        self.unpack().occupancy_range(input)
    }
}

impl<E> MovePosition<E>
where
    E: EntityRepr,
{
    /// The live range a scratch register borrowed at this position must be
    /// free over.
    pub(crate) fn borrow_range(self, input: &Input<'_, impl InputFunction>) -> Range<LivePoint<E>> {
        let point = match self {
            MovePosition::Point(point) | MovePosition::Departure(point) => point,
            MovePosition::CriticalEdge { pred, .. } => pred.end_point(input).prev_point(),
        };
        point..point.next_point()
    }

    /// The live range a value must cover to still be in its register while
    /// the moves at this position run.
    pub(crate) fn occupancy_range(
        self,
        input: &Input<'_, impl InputFunction>,
    ) -> Range<LivePoint<E>> {
        let point = match self {
            MovePosition::Point(point) | MovePosition::Departure(point) => point,
            MovePosition::CriticalEdge { .. } => return self.borrow_range(input),
        };

        let is_first_inst_in_block = || {
            let block = input.func.inst(point.inst().with_repr32()).block();
            block_first_inst(&input.func.block(block)) == point.inst().with_repr32()
        };

        match point.pos() {
            // Moving before the first instruction of the block.
            //
            // No shift, unlike moves before other instructions in this block,
            // since a value live into the block starts its span right here.
            // This also covers an early def here, which is conservative and
            // costs us only a scratch candidate.
            Position::Early if is_first_inst_in_block() => point..point.next_point(),

            // Moving before a non-first instruction.
            //
            // A span starting here does not have its value in its register
            // until the moves complete, so shift the range back.
            Position::Early => point.prev_point()..point,

            // Moving after an instruction.
            //
            // These run after the late half and before the next point begins,
            // so what is in the register is what covers the point, and the
            // range needs no shift.
            Position::Late => point..point.next_point(),
        }
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

/// One of `generate`'s passes, in the order they must run.
///
/// The passes consume and mutate state produced by each other and rely on
/// invariants created by each other that are easy to accidentally overlook. We
/// use this for debug asserts; see `enter_pass`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MovePass {
    /// No pass has run yet.
    Start,
    IndexFunction,
    EmitHalfMoves,
    EmitSpills,
    EmitReservationHalfMoves,
    Resolve,
    Sequentialize,
}

impl MovePass {
    /// The pass that must run after this one, if any.
    fn next(self) -> Option<Self> {
        match self {
            MovePass::Start => Some(MovePass::IndexFunction),
            MovePass::IndexFunction => Some(MovePass::EmitHalfMoves),
            MovePass::EmitHalfMoves => Some(MovePass::EmitSpills),
            MovePass::EmitSpills => Some(MovePass::EmitReservationHalfMoves),
            MovePass::EmitReservationHalfMoves => Some(MovePass::Resolve),
            MovePass::Resolve => Some(MovePass::Sequentialize),
            MovePass::Sequentialize => None,
        }
    }
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

    /// The edges that enter each block.
    incoming_edges: SecondaryMap<Block<E>, EntityRange<Edge<E>>>,

    /// Where each edge's moves go, in the same order as `edges`.
    ///
    /// A pure function of the edge, asked for once per span crossing it.
    edge_positions: Vec<PackedMovePosition<E>>,

    /// Where each block's outgoing edges' moves go, in the order the block
    /// lists its successors, with `outgoing_edges` giving each block's run.
    ///
    /// `edge_positions` answers the same question, but `edges` is sorted by
    /// successor, so reaching an entry of it from a `(pred, index)` pair would
    /// need a search. The live-out half of `emit_value_half_moves` walks a
    /// block's successors once per live-out span, which is many times per
    /// block.
    outgoing_positions: Vec<PackedMovePosition<E>>,

    /// Each block's run of `outgoing_positions`.
    outgoing_edges: SecondaryMap<Block<E>, EntityRange<Edge<E>>>,

    /// For a block parameter, the block it belongs to and its index in that
    /// block's parameter list.
    param_of: SecondaryMap<Val<E>, Option<(Block<E>, usize)>>,

    /// Each block's first and last live points.
    ///
    /// `Block::start_point` and `end_point` each look the block up in the
    /// function and convert an instruction index, and `emit_half_moves` asks
    /// for both once per span -- many times per block, and from a loop over
    /// values rather than over blocks, so no cursor helps.
    block_points: SecondaryMap<Block<E>, Option<(LivePoint<E>, LivePoint<E>)>>,

    /// Scratch for the pass's walk over every value's spans.
    spans: Vec<LiveSpan<E>>,

    /// Scratch for `sort_spans`.
    keyed_spans: Vec<(u128, LiveSpan<E>)>,

    /// Scratch, live only while visiting one block, sorted by the instruction
    /// and value each entry answers for.
    reservation_in_outs: Vec<ReservationInOut<E>>,

    /// Every move to make, sorted by position.
    batch_moves: Vec<(PackedMovePosition<E>, BatchMove<E>)>,

    /// One position's worth of `batch`, with groups expanded into scalar
    /// locations.
    expanded: Vec<ParallelMove<E>>,

    /// Every rematerialization to perform, sorted by position.
    remats: Vec<(PackedMovePosition<E>, Remat<E>)>,

    /// One position's worth of sequentialized parallel moves.
    solved: Vec<ParallelMove<E>>,

    /// The registers that writing one candidate scratch would evict, while we
    /// are working out whether it is a candidate we can use.
    ///
    /// Each carries the bracket it would get, and whether something is still
    /// living in it when the batch ends, which together say whether another
    /// register's reload may land on top of it.
    scratch_eviction_regs: Occupants<E>,

    /// Scratch space for `BatchScratch::choose`: what the best candidate so
    /// far would evict, held aside while later candidates overwrite
    /// `scratch_eviction_regs`.
    scratch_settled_regs: Occupants<E>,

    /// The registers we had to evict while solving one position's batch, so
    /// that a second scratch does not land on one of them.
    ///
    /// Only the evictions under a wide bracket, since the solver hands the
    /// tight ones back the moment it is done with them.
    wide_evicted_regs: Vec<Reg<E>>,

    /// The slots those evicted registers' contents went to, so that a second
    /// scratch does not land on one of those either.
    ///
    /// Also any slot a cycle parked in: the solver is done with one of those
    /// once the park move is out, but a wide save sits above the whole batch,
    /// where it would write over the parked value.
    wide_evicted_slots: Vec<SpillSlot<E>>,

    /// The slots used by tight evictions, so that a wide one does not land on
    /// one of them.
    ///
    /// Kept apart from `wide_evicted_slots` because two tight stays can share
    /// a slot and a wide one can share with nobody: tight brackets never
    /// overlap one another, while a wide one encloses every tight stay, so a
    /// save landing inside it writes over what it is holding.
    tight_evicted_slots: Vec<SpillSlot<E>>,

    /// The parallel-move solver.
    solver: ParallelMoveSolver<E>,

    /// The result of this pass: every edit, sorted by position.
    edits: Vec<(PackedMovePosition<E>, Edit<E>)>,

    /// The current sub-pass within move generation.
    pass: MovePass,
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
            incoming_edges: SecondaryMap::new(EntityRange::empty()),
            edge_positions: Vec::new(),
            outgoing_positions: Vec::new(),
            outgoing_edges: SecondaryMap::new(EntityRange::empty()),
            param_of: SecondaryMap::new(None),
            block_points: SecondaryMap::new(None),
            spans: Vec::new(),
            keyed_spans: Vec::new(),
            reservation_in_outs: Vec::new(),
            batch_moves: Vec::new(),
            expanded: Vec::new(),
            remats: Vec::new(),
            solved: Vec::new(),
            scratch_eviction_regs: Occupants::new(),
            scratch_settled_regs: Occupants::new(),
            wide_evicted_regs: Vec::new(),
            wide_evicted_slots: Vec::new(),
            tight_evicted_slots: Vec::new(),
            solver: ParallelMoveSolver::new(),
            edits: Vec::new(),
            pass: MovePass::Start,
        }
    }

    pub fn reset(&mut self) {
        let Self {
            sources,
            dests,
            edges,
            incoming_edges,
            edge_positions,
            outgoing_positions,
            outgoing_edges,
            param_of,
            block_points,
            spans,
            keyed_spans,
            reservation_in_outs,
            batch_moves,
            expanded,
            remats,
            solved,
            scratch_eviction_regs: eviction_regs,
            scratch_settled_regs: settled_regs,
            wide_evicted_regs,
            wide_evicted_slots,
            tight_evicted_slots,
            solver,
            edits,
            pass,
        } = self;
        sources.clear();
        dests.clear();
        edges.reset();
        incoming_edges.reset();
        edge_positions.clear();
        outgoing_positions.clear();
        outgoing_edges.reset();
        param_of.reset();
        block_points.reset();
        spans.clear();
        keyed_spans.clear();
        reservation_in_outs.clear();
        batch_moves.clear();
        expanded.clear();
        remats.clear();
        solved.clear();
        eviction_regs.clear();
        settled_regs.clear();
        wide_evicted_regs.clear();
        wide_evicted_slots.clear();
        tight_evicted_slots.clear();
        solver.reset();
        edits.clear();
        *pass = MovePass::Start;
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            sources,
            dests,
            edges,
            incoming_edges,
            edge_positions,
            outgoing_positions,
            outgoing_edges,
            param_of,
            block_points,
            spans,
            keyed_spans,
            reservation_in_outs,
            batch_moves,
            expanded,
            remats,
            solved,
            scratch_eviction_regs: eviction_regs,
            scratch_settled_regs: settled_regs,
            wide_evicted_regs,
            wide_evicted_slots,
            tight_evicted_slots,
            solver,
            edits,
            pass,
        } = self;
        sources.is_empty()
            && dests.is_empty()
            && edges.is_reset()
            && incoming_edges.is_reset()
            && edge_positions.is_empty()
            && outgoing_positions.is_empty()
            && outgoing_edges.is_reset()
            && param_of.is_reset()
            && block_points.is_reset()
            && spans.is_empty()
            && keyed_spans.is_empty()
            && reservation_in_outs.is_empty()
            && batch_moves.is_empty()
            && expanded.is_empty()
            && remats.is_empty()
            && solved.is_empty()
            && eviction_regs.is_empty()
            && settled_regs.is_empty()
            && wide_evicted_regs.is_empty()
            && wide_evicted_slots.is_empty()
            && tight_evicted_slots.is_empty()
            && solver.is_reset()
            && edits.is_empty()
            && *pass == MovePass::Start
    }

    /// Record that `pass` is starting, and check the passes run in order.
    fn enter_pass(&mut self, pass: MovePass) {
        debug_assert_eq!(
            Some(pass),
            self.pass.next(),
            "move generation's passes must run in order, and each exactly once",
        );
        self.pass = pass;
    }

    /// Get the edits this pass generated, sorted by position and then moves
    /// before rematerializations.
    pub(crate) fn edits(&self) -> &[(PackedMovePosition<E>, Edit<E>)] {
        &self.edits
    }

    /// Those edits, mutably, so that a test can break a correct allocation and
    /// watch the checker notice.
    #[cfg(test)]
    pub(crate) fn edits_mut(&mut self) -> &mut Vec<(PackedMovePosition<E>, Edit<E>)> {
        &mut self.edits
    }

    /// Where in the whole edit list the edits at program points inside the
    /// block whose instructions run from `first` to `last` sit.
    pub(crate) fn block_point_edit_range(&self, first: Inst<E>, last: Inst<E>) -> Range<usize> {
        let start = PackedMovePosition::point(LivePoint::new(first, Position::Early));
        let end = PackedMovePosition::point(LivePoint::new(last, Position::Late).next_point());
        let lo = self.edits.partition_point(|&(pos, _)| pos < start);
        let hi = self.edits.partition_point(|&(pos, _)| pos < end);
        lo..hi
    }

    /// Where in the whole edit list `pred`'s outgoing critical-edge edits sit.
    pub(crate) fn block_edge_edit_range(&self, pred: Block<E>) -> Range<usize> {
        let start = PackedMovePosition::<E>::pack(1, pred.index(), 0);
        let end = PackedMovePosition::<E>::pack(1, pred.index() + 1, 0);
        let lo = self.edits.partition_point(|&(pos, _)| pos < start);
        let hi = self.edits.partition_point(|&(pos, _)| pos < end);
        lo..hi
    }

    /// The edits at program points inside the block whose instructions run from
    /// `first` to `last`, in program order.
    #[cfg(feature = "visualizer")]
    pub(crate) fn block_point_edits(
        &self,
        first: Inst<E>,
        last: Inst<E>,
    ) -> &[(PackedMovePosition<E>, Edit<E>)] {
        &self.edits[self.block_point_edit_range(first, last)]
    }

    /// The edits on critical edges leaving `pred`, in outgoing-edge order.
    #[cfg(feature = "visualizer")]
    pub(crate) fn block_edge_edits(&self, pred: Block<E>) -> &[(PackedMovePosition<E>, Edit<E>)] {
        &self.edits[self.block_edge_edit_range(pred)]
    }

    /// Drop the edits at `indices`, which must be strictly increasing and in
    /// bounds.
    pub(crate) fn remove_edits(&mut self, indices: &[usize]) {
        debug_assert!(
            indices.windows(2).all(|w| w[0] < w[1]),
            "the indices to remove must be strictly increasing and free of duplicates",
        );
        debug_assert!(
            indices.last().is_none_or(|&last| last < self.edits.len()),
            "every index to remove must address an edit",
        );

        // Use `retain`, rather than e.g. `swap_remove`, to keep the edits
        // sorted.
        let mut remove_indices = indices.iter().copied().peekable();
        let mut edit_index = 0;
        self.edits.retain(|_| {
            let remove_edit = remove_indices.peek() == Some(&edit_index);
            if remove_edit {
                let _ = remove_indices.next();
            }
            edit_index += 1;
            !remove_edit
        });
    }

    /// Drop the edits at `remove`, as `remove_edits` does, and merge in the
    /// edits in `insert`, which must be sorted by position.
    ///
    /// An inserted edit goes after every existing edit at its position.
    pub(crate) fn remove_and_insert_edits(
        &mut self,
        remove: &[usize],
        insert: &[(PackedMovePosition<E>, Edit<E>)],
    ) {
        if insert.is_empty() {
            self.remove_edits(remove);
            return;
        }
        debug_assert!(
            insert.windows(2).all(|w| w[0].0 <= w[1].0),
            "the edits to insert must be sorted by position",
        );
        debug_assert!(
            remove.windows(2).all(|w| w[0] < w[1]),
            "the indices to remove must be strictly increasing and free of duplicates",
        );

        let old = core::mem::take(&mut self.edits);
        let mut edits = Vec::with_capacity(old.len() - remove.len() + insert.len());
        let mut remove = remove.iter().copied().peekable();
        let mut insert = insert.iter().copied().peekable();
        for (i, (pos, edit)) in old.into_iter().enumerate() {
            while let Some(&(new_pos, new_edit)) = insert.peek() {
                if new_pos >= pos {
                    break;
                }
                edits.push((new_pos, new_edit));
                insert.next();
            }
            if remove.peek() == Some(&i) {
                remove.next();
                continue;
            }
            edits.push((pos, edit));
        }
        debug_assert!(
            remove.peek().is_none(),
            "every index to remove must address an edit"
        );
        edits.extend(insert);
        self.edits = edits;
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
        spilled_live_ranges: &SpilledLiveRanges<E>,
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
        self.emit_reservation_half_moves(
            input,
            counts,
            events,
            rpo,
            liveness,
            live_ranges,
            spill_slots,
            output,
        )?;
        self.resolve(input, counts, events);
        self.sequentialize(
            input,
            counts,
            events,
            live_ranges,
            region_allocation,
            spill_slots,
            spilled_live_ranges,
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
        self.enter_pass(MovePass::IndexFunction);
        let func = input.func;

        self.block_points.reserve(func.len_blocks());
        for block in rpo.iter() {
            let input_block = func.block(block.with_repr32());

            self.block_points[block] = Some((block.start_point(input), block.end_point(input)));

            for (index, param) in input_block.params().enumerate() {
                let param = output.with_repr::<E, _>(param)?;
                self.param_of[param] = Some((block, index));
            }

            // Only reachable predecessors matter: an unreachable block has no
            // live ranges, and so nothing to move along its edges.
            let outgoing_start = self.outgoing_positions.len();
            for (index, succ) in input_block.successors().enumerate() {
                let index = u16::try_from(index).unwrap();
                let succ = output.with_repr::<E, _>(succ)?;
                let edge = EdgeData {
                    succ,
                    pred: block,
                    index,
                };
                self.edges.push(output, edge)?;
                self.outgoing_positions.push(edge_position(input, edge)?);
            }
            self.outgoing_edges[block] = EntityRange {
                start: output.entity::<Edge<E>>(outgoing_start)?,
                end: output.entity::<Edge<E>>(self.outgoing_positions.len())?,
            };
        }

        self.edges.as_mut_slice().sort_unstable();
        debug_assert!(
            self.edges
                .as_slice()
                .windows(2)
                .all(|w| w[0].succ <= w[1].succ),
            "the fill below walks one run per block, so edges must be grouped \
             by successor",
        );

        let edges = self.edges.as_slice();

        // One pass over the sorted edges records each block's run, so that
        // reading a block's edges need not search for it: it is asked once per
        // live-in span, which is many times per block.
        self.incoming_edges.reserve(func.len_blocks());
        let mut e = 0;
        while e < edges.len() {
            let succ = edges[e].succ;
            let start = e;
            while e < edges.len() && edges[e].succ == succ {
                e += 1;
            }
            self.incoming_edges[succ] = EntityRange {
                start: output.entity::<Edge<E>>(start)?,
                end: output.entity::<Edge<E>>(e)?,
            };
        }

        self.edge_positions.reserve(edges.len());
        for &edge in edges {
            self.edge_positions.push(edge_position(input, edge)?);
        }

        Ok(())
    }

    /// Where `edge`'s moves go, from the table `index_function` filled.
    fn edge_position_of(&self, edge: Edge<E>) -> PackedMovePosition<E> {
        self.edge_positions[edge.index()]
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
        self.enter_pass(MovePass::EmitHalfMoves);
        let mut spans = core::mem::take(&mut self.spans);
        debug_assert!(spans.is_empty());

        spans.extend(live_ranges.spans());
        sort_spans(live_ranges, &mut spans, &mut self.keyed_spans);

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

        // `self.spans` is left populated and sorted for the reservation pass.
        self.spans = spans;

        result
    }

    /// The spans of `val`, in program order.
    ///
    /// Only valid while `self.spans` holds the sorted list `emit_half_moves`
    /// and `emit_reservation_half_moves` share.
    fn spans_of(&self, live_ranges: &LiveRanges<E>, val: Val<E>) -> &[LiveSpan<E>] {
        let range = self.spans_range(live_ranges, val);
        &self.spans[range]
    }

    /// The indices where the spans of `val` sit in `self.spans`.
    fn spans_range(&self, live_ranges: &LiveRanges<E>, val: Val<E>) -> Range<usize> {
        let spans = self.spans.as_slice();
        let start = spans.partition_point(|s| s.val(live_ranges) < val);
        let end = spans.partition_point(|s| s.val(live_ranges) <= val);
        start..end
    }

    /// Does `span` only get its value in the gap where it begins, so that
    /// reading out of it there would read it before it is filled?
    fn arrives_in_the_gap(
        &self,
        input: &Input<'_, impl InputFunction>,
        live_ranges: &LiveRanges<E>,
        spill_slots: &SpillSlots<E>,
        span: LiveSpan<E>,
        pos: PackedMovePosition<E>,
        key_val: Val<E>,
        held: Allocation<E>,
    ) -> bool {
        let func = input.func;
        let val = span.val(live_ranges);
        let start = span.start(live_ranges);
        let block = span.block(func, live_ranges);

        // At the top of a block the value arrives along the edges, either
        // before this gap or as a source a predecessor records in it. What is
        // left is a span no predecessor delivers to, as an `AlwaysRemat`
        // value's is in a block that never mentions it: only `resolve`'s
        // recomputation fills it, after this position's moves.
        if start == block.start_point(input) {
            return !self.sources.contains_key(&HalfMoveKey::new(pos, key_val))
                && Self::should_remat(input, held, None, key_val);
        }

        // The instruction itself puts it in place.
        if defines_val_at(func, val, start) {
            return false;
        }

        // Otherwise a previous span of this block hands over to this one, and
        // only a previous span that holds the value somewhere can.
        incoming_allocation(
            input,
            live_ranges,
            spill_slots,
            self.spans_of(live_ranges, val),
            block,
            start,
        )
        .is_none()
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
            let (block_start, block_end) = self.block_points[block]
                .expect("`index_function` records every reachable block's points");
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
            // This span is live-in to its block: it begins at the block's
            // start point and its value is live there.
            if start == block_start && block.is_live_in(liveness, val) {
                // Check whether the value is a parameter of this block.
                let param = self.param_of[val].filter(|&(b, _)| b == block);

                for e in self.incoming_edges[block] {
                    let edge = self.edges[e];
                    let pos = self.edge_position_of(e);

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
            if start != block_start {
                let incoming = incoming_allocation(
                    input,
                    live_ranges,
                    spill_slots,
                    &value_spans[..i],
                    block,
                    start,
                );
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
            // And live-out: it reaches the block's end point and its value
            // is live past it. `span_is_live_out_of_block` asks the same
            // question where the block's points are not already to hand.
            if end == block_end && block.is_live_out(liveness, val) {
                // `index_function` worked these out once per edge; this loop
                // runs once per live-out span, which is many times per block.
                let outgoing = self.outgoing_edges[block];
                for i in outgoing.start.index()..outgoing.end.index() {
                    let pos = self.outgoing_positions[i];
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
        self.enter_pass(MovePass::EmitSpills);
        let func = input.func;

        for spill_site in spill_placement.spills().iter().copied() {
            let span = spill_site.span();
            let val = span.val(live_ranges);
            let block = spill_site.block();
            let home = val.stack_home(spill_slots).unwrap();
            let dst = Allocation::Stack(home);
            let arrives_in = span
                .allocation(live_ranges, spill_slots)
                .expect("a span we spill from holds its value in a register");

            if spill_site.point() != block.end_point(input) {
                let pos = PackedMovePosition::point(spill_site.point());
                let key_val = self.val_for_spill_key(input, output, block, val, pos)?;

                debug_assert!(
                    !(spill_site.point() == block.start_point(input)
                        && block.is_live_in(liveness, val)
                        && block.with_repr32() != func.entry_block()
                        && func.block(block.with_repr32()).len_predecessors() == 1)
                        || self.sources.contains_key(&HalfMoveKey::new(pos, key_val)),
                    "{val:?} arrives in {block:?} from nowhere, so the spill \
                     placed at its start has no source to read from",
                );

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
}

/// Where one reservation's value is on either side of its instruction.
#[derive(Clone, Copy)]
struct ReservationInOut<E>
where
    E: EntityRepr,
{
    /// The instruction whose reservations this answers for.
    inst: Inst<E>,

    /// The value they hold a register for.
    val: Val<E>,

    /// The span the value is read out of, to be delivered into the register
    /// before the instruction reads it.
    read_from: Option<LiveSpan<E>>,

    /// The span the value is written into, carrying it back out of the register
    /// after the instruction writes it.
    written_into: Option<LiveSpan<E>>,
}

/// Find the spans the value is in on either side of each reservation's
/// instruction.
fn find_reservation_in_outs<E>(
    func: &impl InputFunction,
    live_ranges: &LiveRanges<E>,
    in_outs: &mut Vec<ReservationInOut<E>>,
    block: Block<E>,
    reservations: EntityRange<Reservation<E>>,
) where
    E: EntityRepr,
{
    debug_assert!(in_outs.is_empty());

    // A clobber has no value to deliver or carry out, so it needs no entry.
    in_outs.extend(reservations.into_iter().filter_map(|r| {
        Some(ReservationInOut {
            inst: r.start(live_ranges).inst(),
            val: r.val(live_ranges)?,
            read_from: None,
            written_into: None,
        })
    }));
    in_outs.sort_unstable_by_key(|p| (p.inst, p.val));
    in_outs.dedup_by_key(|p| (p.inst, p.val));

    for u in block.uses(live_ranges) {
        let point = u.point(live_ranges);
        let span = u.span(live_ranges);
        let key = (point.inst(), span.val(live_ranges));
        let Ok(entry) = in_outs.binary_search_by_key(&key, |p| (p.inst, p.val)) else {
            continue;
        };

        let operand = func
            .inst(point.inst().with_repr32())
            .operand(u.operand(live_ranges));
        match operand.kind() {
            // The first one in this order.
            DefUse::Use => _ = in_outs[entry].read_from.get_or_insert(span),
            // A value is defined once, so there is only ever the one of these.
            DefUse::Def => {
                debug_assert!(in_outs[entry].written_into.is_none());
                in_outs[entry].written_into = Some(span);
            }
        }
    }
}

/// Where the value of the span starting at `start` in `block` comes from, when
/// a previous span of the same value in the same block hands it over.
///
/// `val_spans` is a window of one value's spans in program order, as
/// `MoveGeneration::pieces_of` hands it out. Spans at or after `start`, and
/// spans belonging to other blocks, are not candidates.
fn incoming_allocation<E>(
    input: &Input<'_, impl InputFunction>,
    live_ranges: &LiveRanges<E>,
    spill_slots: &SpillSlots<E>,
    val_spans: &[LiveSpan<E>],
    block: Block<E>,
    start: LivePoint<E>,
) -> Option<Allocation<E>>
where
    E: EntityRepr,
{
    let func = input.func;
    val_spans
        .iter()
        .rev()
        .skip_while(|prev| prev.start(live_ranges) >= start)
        .take_while(|prev| prev.block(func, live_ranges) == block)
        // A value's spans within a block abut or overlap, so at most one of
        // them reaches `start` and the first one found is the only one.
        .find(|prev| {
            let val = prev.val(live_ranges);
            let reaches = start <= prev.end(live_ranges);
            debug_assert!(
                reaches
                    || func.value(val.with_repr32()).remat_cost() == Some(RematCost::AlwaysRemat),
                "{val:?}'s spans must overlap or abut, but {prev:?} ends at {:?}, before \
                 {start:?}",
                prev.end(live_ranges),
            );
            reaches
        })
        // A span holding its value nowhere does not flow into this one;
        // `resolve` fills the source-less destination by recomputing.
        .and_then(|prev| prev.allocation(live_ranges, spill_slots))
}

impl<E> MoveGeneration<E>
where
    E: EntityRepr,
{
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

        for e in self.incoming_edges[block] {
            let edge = self.edges[e];
            if self.edge_position_of(e) == pos {
                return self.block_call_arg(input, output, edge, k);
            }
        }

        Ok(val)
    }

    /// Connect each register reserved for a fixed operand to wherever the
    /// value's own span needs it.
    ///
    /// A fixed operand leaves its value's bundle unconstrained (see
    /// `live_ranges::ReservationData`), so these moves make good on the
    /// bundle's allocation.
    fn emit_reservation_half_moves(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        rpo: &Rpo<E>,
        liveness: &Liveness<E>,
        live_ranges: &LiveRanges<E>,
        spill_slots: &SpillSlots<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        self.enter_pass(MovePass::EmitReservationHalfMoves);

        debug_assert_eq!(self.spans.len(), live_ranges.spans().len());
        debug_assert!(self.spans.is_sorted_by_key(|&span| (
            span.val(live_ranges),
            span.start(live_ranges),
            span.end(live_ranges),
        )));

        for block in rpo.iter() {
            let reservations = block.reservations(live_ranges);
            if reservations.is_empty() {
                continue;
            }

            find_reservation_in_outs(
                input.func,
                live_ranges,
                &mut self.reservation_in_outs,
                block,
                reservations,
            );

            for reservation in reservations {
                // A clobber has no half-moves to emit, and so no
                // `reservation_in_outs` entry to look up.
                let Some(val) = reservation.val(live_ranges) else {
                    debug_assert!(
                        !reservation.uses(live_ranges) && !reservation.defs(live_ranges),
                        "a reservation with no value has no operand to move for",
                    );
                    continue;
                };
                let held = Allocation::Reg(reservation.reg(live_ranges));

                let key = (reservation.start(live_ranges).inst(), val);
                let entry = self
                    .reservation_in_outs
                    .binary_search_by_key(&key, |p| (p.inst, p.val))
                    .expect("`reservation_in_outs` has an entry for every reservation");

                if reservation.uses(live_ranges) {
                    // At the top of a block the move sits on the incoming
                    // edge, where a parameter goes by its predecessor's
                    // argument.
                    let pos = PackedMovePosition::point(reservation.start(live_ranges));
                    let key_val = self.val_for_spill_key(input, output, block, val, pos)?;

                    // A span filled in this very gap cannot be read out of
                    // here.
                    let arrives_here =
                        self.reservation_in_outs[entry]
                            .read_from
                            .is_some_and(|span| {
                                span.start(live_ranges) >= reservation.start(live_ranges)
                                    && self.arrives_in_the_gap(
                                        input,
                                        live_ranges,
                                        spill_slots,
                                        span,
                                        pos,
                                        key_val,
                                        held,
                                    )
                            });

                    self.emit_reservation_arrival(
                        counts,
                        events,
                        live_ranges,
                        spill_slots,
                        pos,
                        key_val,
                        held,
                        self.reservation_in_outs[entry].read_from,
                        arrives_here,
                    );
                }

                if reservation.defs(live_ranges) {
                    self.emit_reservation_departure(
                        input,
                        counts,
                        events,
                        liveness,
                        live_ranges,
                        spill_slots,
                        output,
                        block,
                        reservation,
                        val,
                        held,
                        self.reservation_in_outs[entry].written_into,
                    )?;
                }
            }

            self.reservation_in_outs.clear();
        }

        self.spans.clear();
        Ok(())
    }

    /// Move `val` into the register reserved for the operands that read it
    /// there.
    fn emit_reservation_arrival(
        &mut self,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        live_ranges: &LiveRanges<E>,
        spill_slots: &SpillSlots<E>,
        pos: PackedMovePosition<E>,
        key_val: Val<E>,
        held: Allocation<E>,
        read_from: Option<LiveSpan<E>>,
        arrives_here: bool,
    ) {
        match read_from.and_then(|span| span.allocation(live_ranges, spill_slots)) {
            // Already where it needs to be.
            Some(alloc) if alloc == held => {}

            // Where the value is over this gap, which loses to a span boundary
            // here: that one knows where it *arrives*.
            Some(alloc) if !arrives_here => {
                self.emit_spill(counts, events, pos, key_val, alloc, held)
            }

            // A value held nowhere, or held only once this gap has filled it,
            // is left to `resolve` to recompute.
            _ => self.emit_dest(counts, events, pos, key_val, held),
        }
    }

    /// Move `val` out of the register the instruction defining it wrote it to.
    ///
    /// The move goes in the gap after the instruction, or, on a terminator,
    /// along the outgoing edges.
    fn emit_reservation_departure(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        liveness: &Liveness<E>,
        live_ranges: &LiveRanges<E>,
        spill_slots: &SpillSlots<E>,
        output: &mut OutputInner<E>,
        block: Block<E>,
        reservation: Reservation<E>,
        val: Val<E>,
        held: Allocation<E>,
        written_into: Option<LiveSpan<E>>,
    ) -> IResult<()> {
        let Some(span) = written_into else {
            // Nothing reads the value, so there is nowhere to put it.
            return Ok(());
        };

        let end = reservation.end(live_ranges);

        if end != block.end_point(input) {
            // The value is in the register and nowhere else over this gap.
            self.overwrite_source(counts, events, PackedMovePosition::point(end), val, held);

            // And every place the value still has to be in, past this gap, is
            // filled out of that register here, since the register is the only
            // place it is.
            let pos = PackedMovePosition::point(end);
            for i in self.spans_range(live_ranges, val) {
                let span = self.spans[i];
                if span.start(live_ranges) > end || span.end(live_ranges) <= end {
                    continue;
                }
                let Some(alloc) = span.allocation(live_ranges, spill_slots) else {
                    continue;
                };
                if alloc != held {
                    self.emit_dest(counts, events, pos, val, alloc);
                }
            }

            // A span on the stack is wanted here even when it stops at this
            // gap: spill placement declines its store, having no site where the
            // value sits in a register of its own, so this definition owns it.
            if let Some(alloc @ Allocation::Stack(_)) = span.allocation(live_ranges, spill_slots)
                && alloc != held
            {
                self.emit_dest(counts, events, pos, val, alloc);
            }
        } else {
            // The instruction terminates the block, so the gap after it is the
            // outgoing edges.
            if !span_is_live_out_of_block(input, liveness, val, block, span.end(live_ranges)) {
                return Ok(());
            }
            let stack_home = match span.allocation(live_ranges, spill_slots) {
                Some(alloc @ Allocation::Stack(_)) => Some(alloc),
                _ => None,
            };
            let input_block = input.func.block(block.with_repr32());
            for (index, succ) in input_block.successors().enumerate() {
                let succ = output.with_repr::<E, _>(succ)?;
                let pos = edge_position(
                    input,
                    EdgeData {
                        succ,
                        pred: block,
                        index: u16::try_from(index).unwrap(),
                    },
                )?;
                self.overwrite_source(counts, events, pos, val, held);

                if let Some(alloc) = stack_home
                    && succ.is_live_in(liveness, val)
                {
                    self.emit_dest(counts, events, pos, val, alloc);
                }
            }
        }

        Ok(())
    }

    /// Record that `val` is in `alloc` at `pos`, unless something better
    /// informed already said where it is.
    fn emit_source_if_unknown(
        &mut self,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        pos: PackedMovePosition<E>,
        val: Val<E>,
        alloc: Allocation<E>,
    ) {
        if let Entry::Vacant(entry) = self.sources.entry(HalfMoveKey::new(pos, val)) {
            trace!("move generation: emit source {val:?} at {pos:?} is {alloc:?}");
            counts.half_move_sources.inc();
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

    /// Record that `val` is in `alloc` at `pos`, regardless whatever else was
    /// recorded there.
    ///
    /// `emit_source` keeps the better of two answers because a value can be in
    /// several places at once (e.g. in a register and on the stack). A fixed
    /// definition's register, however, is not one answer among several: the
    /// instruction put the value there and nowhere else, so every other answer
    /// at that point is stale.
    fn overwrite_source(
        &mut self,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        pos: PackedMovePosition<E>,
        val: Val<E>,
        alloc: Allocation<E>,
    ) {
        debug_assert_eq!(self.pass, MovePass::EmitReservationHalfMoves);
        trace!("move generation: overwrite source {val:?} at {pos:?} is {alloc:?}");
        counts.half_move_sources.inc();
        let replaced = self.sources.insert(HalfMoveKey::new(pos, val), alloc);
        event!(
            events,
            HalfMoveSource {
                pos,
                val,
                alloc,
                replaced
            }
        );
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
        self.emit_source_if_unknown(counts, events, pos, val, arrives_in);
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
        self.enter_pass(MovePass::Resolve);
        let mut dests = core::mem::take(&mut self.dests);

        // One destination can be asked for multiple times: two spans beginning
        // at one point can share an allocation, and a value can be both live
        // across an edge and passed as an argument on it. In either case, we
        // only need to put a value into a destination once.
        //
        // That used to be a sort and a `dedup` here, over every destination.
        // It need not be, because both paths out of the loop below already
        // collapse a repeat:
        //
        // * a move goes to `batch_moves`, which `sequentialize_batch` sorts
        //   and dedups by `(src, dst)` once the groups are expanded -- and a
        //   repeated destination resolves to the same source, since the
        //   source is a function of the key, so it expands identically;
        // * a rematerialization goes to `remats`, which `sequentialize`
        //   dedups.
        //
        // Both lists are far shorter than this one: 1,252 remats and one
        // position's worth of moves at a time, against 158,615 destinations
        // on a sample.

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

            // The solver drops a move whose source and destination overlap, and
            // group expansion pairs the two sides index-wise, so an equal pair
            // expands to equal scalar pairs and every one of them is discarded.
            // Most of this loop's moves are such a pair.
            if src == dst {
                continue;
            }

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
        live_ranges: &LiveRanges<E>,
        region_allocation: &RegionAllocation<E>,
        spill_slots: &mut SpillSlots<E>,
        spilled_live_ranges: &SpilledLiveRanges<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        self.enter_pass(MovePass::Sequentialize);

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
                    live_ranges,
                    region_allocation,
                    spill_slots,
                    spilled_live_ranges,
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
        remats.sort_unstable();
        // Two destinations asking for one value in one register at one point
        // want a single recomputation, not two. `resolve` no longer dedups
        // its destinations, so this is where such a repeat is collapsed.
        //
        // It removes nothing on the corpus -- 0 of 70,999 remats over 13,925
        // inputs -- because the 61 duplicated destinations there all take the
        // move path. Kept anyway, and not asserted away: nothing rules out a
        // duplicated destination for a rematerializable value, and this list
        // is 1,252 entries against the 158,615 `resolve` used to sort.
        remats.dedup();
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
    fn sequentialize_batch<F>(
        &mut self,
        input: &Input<'_, F>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        live_ranges: &LiveRanges<E>,
        region_allocation: &RegionAllocation<E>,
        spill_slots: &mut SpillSlots<E>,
        spilled_live_ranges: &SpilledLiveRanges<E>,
        output: &mut OutputInner<E>,
        chunk: &[(PackedMovePosition<E>, BatchMove<E>)],
    ) -> IResult<()>
    where
        F: InputFunction,
    {
        let machine = input.machine;
        let pos = chunk[0].0;
        let borrowed_range = pos.borrow_range(input);

        // What a register actually holds while these moves run, which is not
        // the same question as what a scratch register has to be free over.
        let occupied_range = pos.occupancy_range(input);

        let mut expanded = core::mem::take(&mut self.expanded);
        let mut solved = core::mem::take(&mut self.solved);
        let mut eviction_regs =
            core::mem::replace(&mut self.scratch_eviction_regs, Occupants::new());
        let mut settled_regs = core::mem::replace(&mut self.scratch_settled_regs, Occupants::new());
        let mut wide_evicted_regs = core::mem::take(&mut self.wide_evicted_regs);
        let mut wide_evicted_slots = core::mem::take(&mut self.wide_evicted_slots);
        let mut tight_evicted_slots = core::mem::take(&mut self.tight_evicted_slots);
        let mut solver = core::mem::replace(&mut self.solver, ParallelMoveSolver::new());
        debug_assert!(expanded.is_empty() && solved.is_empty());
        debug_assert!(
            wide_evicted_regs.is_empty()
                && wide_evicted_slots.is_empty()
                && tight_evicted_slots.is_empty()
        );
        eviction_regs.clear();
        settled_regs.clear();

        let result = (|| -> IResult<()> {
            for &(_, batch_move) in chunk {
                expand_groups(machine, spill_slots, output, batch_move, &mut expanded)?;
            }

            // Expanding batch moves into scalar moves can result in duplicates.
            expanded.sort_unstable();
            expanded.dedup_by_key(|m| (m.src(), m.dst()));

            let result = {
                let mut source = BatchScratch {
                    input,
                    machine,
                    region_allocation,
                    live_ranges,
                    spill_slots,
                    spilled_live_ranges,
                    output,
                    counts,
                    events,
                    pos,
                    borrowed_range: borrowed_range.clone(),
                    occupied_range: occupied_range.clone(),
                    expanded: &expanded,
                    wide_evicted_regs: &mut wide_evicted_regs,
                    wide_evicted_slots: &mut wide_evicted_slots,
                    tight_evicted_slots: &mut tight_evicted_slots,
                    eviction_regs: &mut eviction_regs,
                    settled_regs: &mut settled_regs,
                };
                solver.solve(expanded.iter().copied(), &mut source, &mut solved)
            };
            match result {
                Ok(()) => {}
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

            for &mv in &solved {
                self.emit_move(input, counts, events, output, pos, into_move(mv))?;
            }

            Ok(())
        })();

        expanded.clear();
        self.expanded = expanded;

        solved.clear();
        self.solved = solved;

        eviction_regs.clear();
        self.scratch_eviction_regs = eviction_regs;

        settled_regs.clear();
        self.scratch_settled_regs = settled_regs;

        wide_evicted_regs.clear();
        self.wide_evicted_regs = wide_evicted_regs;

        wide_evicted_slots.clear();
        self.wide_evicted_slots = wide_evicted_slots;

        tight_evicted_slots.clear();
        self.tight_evicted_slots = tight_evicted_slots;

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

/// Everything the parallel-move solver needs to know about the machine while
/// it sequentializes one position's batch.
struct BatchScratch<'a, 'i, E, F>
where
    E: EntityRepr,
    F: InputFunction,
{
    input: &'a Input<'i, F>,
    machine: &'a Machine,
    region_allocation: &'a RegionAllocation<E>,
    live_ranges: &'a LiveRanges<E>,
    spill_slots: &'a mut SpillSlots<E>,
    spilled_live_ranges: &'a SpilledLiveRanges<E>,
    output: &'a mut OutputInner<E>,
    counts: &'a mut Counts,
    events: &'a mut EventsLog<E>,

    /// Where the batch sits, and the two ranges its questions are asked over.
    pos: PackedMovePosition<E>,

    /// What is wanted from a register at or after the point these moves feed.
    borrowed_range: Range<LivePoint<E>>,

    /// What a register actually holds while these moves run, which is not the
    /// same question.
    occupied_range: Range<LivePoint<E>>,

    /// The batch itself, groups already expanded into scalar moves.
    expanded: &'a [ParallelMove<E>],

    /// The registers we have evicted for the whole length of the batch, so that
    /// a second scratch does not land on one of them.
    wide_evicted_regs: &'a mut Vec<Reg<E>>,

    /// The slots those evictions are sitting in, likewise.
    wide_evicted_slots: &'a mut Vec<SpillSlot<E>>,

    /// The slots the tight evictions have used, likewise.
    tight_evicted_slots: &'a mut Vec<SpillSlot<E>>,

    /// Scratch space for `occupants`: the registers that writing one candidate
    /// would evict, while we work out whether it is one we can use.
    eviction_regs: &'a mut Occupants<E>,

    /// Scratch space for `choose`: what the best candidate so far would
    /// evict.
    settled_regs: &'a mut Occupants<E>,
}

/// How long an evicted register stays saved.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Bracket {
    /// Saved and reloaded around just the two moves being staged, because the
    /// batch wants those units back before it is over.
    Tight,

    /// Saved ahead of the whole batch and put back after it, because putting
    /// it back writes over the register we took.
    Wide,
}

const PARK_BRACKET: Bracket = Bracket::Wide;

/// One register that writing a candidate scratch would clobber.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Occupant<E>
where
    E: EntityRepr,
{
    /// The register holding the value.
    reg: Reg<E>,

    /// How long it would have to stay saved.
    bracket: Bracket,

    /// Whether something is still living in it when the batch ends, which is
    /// what decides whether another register's reload may land on top of it.
    outlives: bool,
}

/// What evicting one candidate scratch register would put out, while we work
/// out whether it is a candidate we can use.
///
/// At most one entry per register: a register named twice keeps the stronger
/// `outlives` claim rather than appearing twice with different ones.
struct Occupants<E>
where
    E: EntityRepr,
{
    occupants: Vec<Occupant<E>>,
}

impl<E> Occupants<E>
where
    E: EntityRepr,
{
    const fn new() -> Self {
        Occupants {
            occupants: Vec::new(),
        }
    }

    fn clear(&mut self) {
        self.occupants.clear();
    }

    fn is_empty(&self) -> bool {
        self.occupants.is_empty()
    }

    fn iter(&self) -> impl Iterator<Item = Occupant<E>> {
        self.occupants.iter().copied()
    }

    /// Claim `reg`, keeping the stronger `outlives` claim when something
    /// already claimed it.
    ///
    /// `bracket` is only consulted for a register nobody has claimed yet,
    /// since working one out means scanning the batch.
    fn note(&mut self, reg: Reg<E>, outlives: bool, bracket: impl FnOnce() -> Bracket) {
        match self.occupants.iter_mut().find(|o| o.reg == reg) {
            Some(seen) => seen.outlives |= outlives,
            None => self.occupants.push(Occupant {
                reg,
                bracket: bracket(),
                outlives,
            }),
        }
    }

    /// Drop everything nobody is going to read.
    ///
    /// Bracketing a dead value costs something real: two registers sharing a
    /// unit cannot both be restored, so a dead one crowding out a live one
    /// makes the register unusable for no gain.
    fn drop_dead(&mut self) {
        self.occupants
            .retain(|o| o.outlives || o.bracket == Bracket::Tight);
    }

    /// Whether anything here needs a tight bracket.
    fn any_tight(&self) -> bool {
        self.iter().any(|o| o.bracket == Bracket::Tight)
    }

    /// Whether every pair sharing a unit is a pair `may_share` allows.
    fn pairs_may_share(&self, overlap: &dyn Fn(Reg<E>, Reg<E>) -> bool) -> bool {
        self.occupants.iter().enumerate().all(|(i, a)| {
            self.occupants[i + 1..].iter().all(|b| {
                !overlap(a.reg, b.reg) || may_share(a.bracket, b.bracket, a.outlives, b.outlives)
            })
        })
    }
}

/// May two evicted registers that share a unit both be put back?
///
/// Only if their reloads sit at different depths: the wide one lands on top of
/// the tight one, so whatever the tight one holds has to be finished with by
/// then, which is what `outlives` says it is not.
fn may_share(a: Bracket, b: Bracket, a_outlives: bool, b_outlives: bool) -> bool {
    match (a, b) {
        (Bracket::Tight, Bracket::Wide) => !a_outlives,
        (Bracket::Wide, Bracket::Tight) => !b_outlives,
        (Bracket::Tight, Bracket::Tight) | (Bracket::Wide, Bracket::Wide) => false,
    }
}

/// Is `slot` one that nothing may sit in for the length of an eviction?
///
/// The slot has to last as long as the eviction, so it cannot be one the batch
/// is already reading or writing, nor one another eviction has taken.
///
/// A wide bracket is the only one that clashes with a tight one, since every
/// tight stay runs inside it. Two tight stays never overlap and may share.
///
/// `taken` is the eviction being arranged, whose earlier entries have slots
/// but are recorded nowhere else yet.
fn slot_is_taken<E>(
    expanded: &[ParallelMove<E>],
    wide_evicted_slots: &[SpillSlot<E>],
    tight_evicted_slots: &[SpillSlot<E>],
    bracket: Bracket,
    unavailable: &[ScalarAllocation<E>],
    slot: SpillSlot<E>,
    taken: &[(Reg<E>, SpillSlot<E>)],
) -> bool
where
    E: EntityRepr,
{
    if wide_evicted_slots.contains(&slot) || taken.iter().any(|&(_, s)| s == slot) {
        return true;
    }
    if bracket == Bracket::Wide && tight_evicted_slots.contains(&slot) {
        return true;
    }
    let slot = ScalarAllocation::Stack(slot);
    unavailable.contains(&slot) || expanded.iter().any(|&m| m.src() == slot || m.dst() == slot)
}

/// Whether `BatchScratch::choose` may hold out for a candidate whose evicted
/// values can all be saved into the stack homes they already have.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HomePreference {
    /// Prefer such a candidate, settling for any eligible one when none turns
    /// up.
    PreferHomes,

    /// Take the first eligible candidate.
    IgnoreHomes,
}

impl<E, F> BatchScratch<'_, '_, E, F>
where
    E: EntityRepr,
    F: InputFunction,
{
    /// The bank of the value `mv` moves.
    fn bank(&self, mv: ParallelMove<E>) -> RegBank {
        let bank = move_bank(self.input, mv);
        debug_assert!(
            match (mv.src(), mv.dst()) {
                (ScalarAllocation::Reg(reg), _) | (_, ScalarAllocation::Reg(reg)) =>
                    reg.with_repr32().bank(self.machine) == bank,
                _ => true,
            },
            "{mv:?} names a register from a different bank than the value it moves",
        );
        bank
    }

    fn inc_count(&mut self, reason: ScratchReason) {
        match reason {
            ScratchReason::StackToStack => self.counts.stack_to_stack_moves.inc(),
            ScratchReason::CycleBreak => self.counts.move_cycles_broken.inc(),
        }
    }

    /// Record that `scratch` is what `mv` gets.
    fn chosen(&mut self, mv: ParallelMove<E>, reason: ScratchReason, scratch: ScalarAllocation<E>) {
        self.inc_count(reason);
        let pos = self.pos;
        event!(
            self.events,
            ScratchRegChosen {
                pos,
                mv,
                scratch,
                reason
            }
        );
    }

    /// Is this a move where the source and destination do not overlap?
    fn is_not_self_move(&self, m: ParallelMove<E>) -> bool {
        !Interfere::interfere(self.machine, m.src(), m.dst())
    }

    /// Whether `reg` is off limits because this batch or an outstanding
    /// scratch is already using it.
    fn is_used(&self, reg: Reg<E>, unavailable: &[ScalarAllocation<E>]) -> bool {
        unavailable
            .iter()
            .any(|&a| ScalarAllocation::interfere(self.machine, reg.into(), a))
            // TODO: investigate whether lazily caching a `RegSet` of all the
            // registers used in this batch improves perf.
            || batch_uses_reg(self.machine, self.expanded, reg)
    }

    /// Whether nothing here is using `reg`, so we may evict whatever is in it
    /// for the duration of the batch.
    fn is_idle(&self, reg: Reg<E>, unavailable: &[ScalarAllocation<E>]) -> bool {
        // `reg` must not interfere with any of the `unavailable` locations.
        !unavailable
            .iter()
            .any(|&a| ScalarAllocation::interfere(self.machine, reg.into(), a))
            // And the batch must not move through `reg`.
            && !batch_moves_through_reg(self.machine, self.expanded, reg)
            // And we must not have already evicted `reg` for the duration of
            // this batch.
            && !self.wide_evicted_regs.iter().any(|&other: &Reg<E>| {
                Interfere::interfere(
                    self.machine,
                    ScalarAllocation::Reg(reg),
                    ScalarAllocation::Reg(other),
                )
            })
    }

    fn slot_is_taken(
        &self,
        bracket: Bracket,
        unavailable: &[ScalarAllocation<E>],
        slot: SpillSlot<E>,
        taken: &[(Reg<E>, SpillSlot<E>)],
    ) -> bool {
        slot_is_taken(
            self.expanded,
            self.wide_evicted_slots,
            self.tight_evicted_slots,
            bracket,
            unavailable,
            slot,
            taken,
        )
    }

    /// Get or create a slot nothing else is looking at, big enough for `size`.
    fn emergency_slot(
        &mut self,
        size: SpillSlotSize,
        bracket: Bracket,
        unavailable: &[ScalarAllocation<E>],
        taken: &[(Reg<E>, SpillSlot<E>)],
    ) -> Result<SpillSlot<E>, SolveError> {
        self.spill_slots
            .emergency_slot(self.counts, self.events, self.output, size, |slot| {
                slot_is_taken(
                    self.expanded,
                    self.wide_evicted_slots,
                    self.tight_evicted_slots,
                    bracket,
                    unavailable,
                    slot,
                    taken,
                )
            })
            .map_err(|()| SolveError::EntityReprTooSmall)
    }

    /// Get the stack-home for the sole occupant of `reg` across this batch, if
    /// any.
    fn stack_home(
        &self,
        reg: Reg<E>,
        unavailable: &[ScalarAllocation<E>],
        taken: &[(Reg<E>, SpillSlot<E>)],
    ) -> Option<SpillSlot<E>> {
        if !reg.stands_alone(self.machine) || !self.is_idle(reg, unavailable) {
            return None;
        }

        let val = self.region_allocation.sole_reg_occupant(
            self.machine,
            self.live_ranges,
            reg,
            self.borrowed_range.clone(),
        )?;

        let Some(StackAllocation::SpillSlot(slot)) = val.stack_home(self.spill_slots) else {
            return None;
        };

        // Borrowing is only safe while the slot still belongs to `val`. Over
        // whole live ranges it always does. Narrowed, the reservation may have
        // ended above here and the slot gone to someone else.
        if self.input.options.narrow_spill_slot_live_ranges
            && !self.spilled_live_ranges.reserved_across(
                self.borrow_block(),
                val,
                self.borrowed_range.clone(),
            )
        {
            return None;
        }

        let size = reg.with_repr32().bank(self.machine).size(self.machine);
        let bracket = self.bracket(reg, unavailable);
        (slot.size(self.spill_slots) == size
            && !self.slot_is_taken(bracket, unavailable, slot, taken))
        .then_some(slot)
    }

    /// The block the borrow sits in.
    fn borrow_block(&self) -> Block<E> {
        match self.pos.unpack() {
            MovePosition::Point(point) | MovePosition::Departure(point) => self
                .input
                .func
                .inst(point.inst().with_repr32())
                .block()
                .with_repr::<E>()
                .expect("every block index already fit in `E` in the earlier passes"),
            // Charged to the block it leaves, whose exit `borrow_range` names.
            MovePosition::CriticalEdge { pred, .. } => pred,
        }
    }

    /// How wide a bracket the solver puts around `reg` when we evict it.
    fn bracket(&self, reg: Reg<E>, unavailable: &[ScalarAllocation<E>]) -> Bracket {
        if self.is_named_in_batch(reg, unavailable) {
            Bracket::Tight
        } else {
            Bracket::Wide
        }
    }

    /// Whether this batch names `reg`.
    fn is_named_in_batch(&self, reg: Reg<E>, unavailable: &[ScalarAllocation<E>]) -> bool {
        let loc = ScalarAllocation::Reg(reg);

        // Is it named in the batch of parallel-moves itself?
        if self.expanded.iter().any(|&m| {
            self.is_not_self_move(m)
                && (m.src() == loc
                    || m.dst() == loc
                    || Interfere::interfere(self.machine, loc, m.dst()))
        }) {
            return true;
        }

        // Or else, is it otherwise unavailable?
        unavailable.contains(&loc)
    }

    /// Gather everything that would be clobbered by writing to `reg`, including
    /// anything live in another register that shares units with it.
    ///
    /// The resulting set is written into `out`.
    ///
    /// Answers `Err(())` when we cannot name everything that would be
    /// clobbered, e.g. due to fixed-register constraints' reservations, or
    /// when what we did name cannot all be put back afterwards. Either way
    /// `reg` is no use to us and `out` is left empty.
    fn collect_occupants(
        &self,
        reg: Reg<E>,
        unavailable: &[ScalarAllocation<E>],
        spent: &[Reg<E>],
        out: &mut Occupants<E>,
    ) -> Result<(), ()> {
        out.clear();

        let result = (|| {
            self.note_named_occupants(reg, unavailable, spent, out);
            self.note_parked_occupants(reg, unavailable, out);
            self.note_allocated_occupants(reg, unavailable, out)?;
            out.drop_dead();
            self.occupants_are_restorable(out)
        })();

        if result.is_err() {
            out.clear();
        }

        result
    }

    /// Add `other` to `out` as a holder of units `reg` covers, if it overlaps
    /// `reg`.
    ///
    /// `outlives` says something is still living in it when the batch ends. A
    /// register only the batch names is empty by then, having been read and
    /// its result put elsewhere, and an empty register is one another reload
    /// may write over.
    fn note_occupant(
        &self,
        reg: Reg<E>,
        other: Reg<E>,
        outlives: bool,
        unavailable: &[ScalarAllocation<E>],
        out: &mut Occupants<E>,
    ) {
        let reg_loc = ScalarAllocation::Reg(reg);
        let other_loc = ScalarAllocation::Reg(other);
        if !Interfere::interfere(self.machine, reg_loc, other_loc) {
            return;
        }
        out.note(other, outlives, || self.bracket(other, unavailable));
    }

    /// Add what the batch itself is holding in units `reg` covers, minus what
    /// it has already finished with.
    fn note_named_occupants(
        &self,
        reg: Reg<E>,
        unavailable: &[ScalarAllocation<E>],
        spent: &[Reg<E>],
        out: &mut Occupants<E>,
    ) {
        for &m in self.expanded.iter() {
            let is_self_move = !self.is_not_self_move(m);
            for (loc, written) in [(m.src(), false), (m.dst(), true)] {
                if let ScalarAllocation::Reg(other) = loc {
                    if self.wide_evicted_regs.contains(&other) || spent.contains(&other) {
                        continue;
                    }
                    self.note_occupant(reg, other, written || is_self_move, unavailable, out);
                }
            }
        }
    }

    /// Add what the solver has parked in units `reg` covers.
    fn note_parked_occupants(
        &self,
        reg: Reg<E>,
        unavailable: &[ScalarAllocation<E>],
        out: &mut Occupants<E>,
    ) {
        for &loc in unavailable {
            if let ScalarAllocation::Reg(other) = loc {
                self.note_occupant(reg, other, false, unavailable, out);
            }
        }
    }

    /// Add what region allocation has in units `reg` covers, minus whatever
    /// the batch is going to write over anyway.
    ///
    /// Answers `Err(())` if the allocator named a holder we cannot, which
    /// makes the whole set untrustworthy.
    fn note_allocated_occupants(
        &self,
        reg: Reg<E>,
        unavailable: &[ScalarAllocation<E>],
        out: &mut Occupants<E>,
    ) -> Result<(), ()> {
        let mut result = Ok(());

        // Two ranges, two different questions. `occupied` is what is
        // physically in the register while the moves run, so it decides
        // whether writing over it loses anything. `span` is what is wanted at
        // or after the point they feed, so it decides whether it has to
        // survive them. A dead def answers only the first; a span cut at a
        // block edge answers only the second.
        for (range, outlives) in [
            (self.occupied_range.clone(), false),
            (self.borrowed_range.clone(), true),
        ] {
            self.region_allocation.for_each_reg_occupant(
                self.machine,
                self.live_ranges,
                reg,
                range,
                |alloc| {
                    for other in self.holders_of(alloc, &mut result) {
                        self.note_allocated_occupant(reg, other, outlives, unavailable, out);
                    }
                },
            );
        }

        result
    }

    /// The registers an allocation puts a value in, failing `complete` if it
    /// names one we cannot.
    fn holders_of(
        &self,
        alloc: RegAllocation<E>,
        result: &mut Result<(), ()>,
    ) -> impl Iterator<Item = Reg<E>> {
        let (one, group) = match alloc {
            RegAllocation::Reg(other) => (Some(other), &[][..]),
            RegAllocation::RegGroup(group) => (None, group.members(self.machine)),
        };
        one.into_iter().chain(group.iter().filter_map(|other| {
            // A group's members are in the machine's own numbering, so one that
            // does not fit ours is a holder we cannot name, and a set missing a
            // holder is not one we can act on.
            let other = other.with_repr::<E>();
            if other.is_none() {
                *result = Err(());
            }
            other
        }))
    }

    /// Add one register region allocation reports, unless the batch is about
    /// to write over it or we have already lent it out.
    fn note_allocated_occupant(
        &self,
        reg: Reg<E>,
        other: Reg<E>,
        outlives: bool,
        unavailable: &[ScalarAllocation<E>],
        out: &mut Occupants<E>,
    ) {
        if self.wide_evicted_regs.contains(&other) {
            return;
        }

        let other_loc = ScalarAllocation::Reg(other);
        let is_overwritten = self.expanded.iter().any(|&mv| {
            self.is_not_self_move(mv) && Interfere::interfere(self.machine, mv.dst(), other_loc)
        });
        if !is_overwritten {
            self.note_occupant(reg, other, outlives, unavailable, out);
        }
    }

    /// Whether every holder in `out` can be put back afterwards.
    fn occupants_are_restorable(&self, out: &Occupants<E>) -> Result<(), ()> {
        let overlap = |a: Reg<E>, b: Reg<E>| Interfere::interfere(self.machine, a, b);

        // A register evicted earlier has a reload waiting at the end, which
        // writes over everything sharing a unit with it. Only a tight bracket
        // fits under that, since it is empty once it closes.
        let clear_of_evicted = out.iter().all(|o| {
            self.wide_evicted_regs.iter().all(|&other| {
                !overlap(o.reg, other)
                    || (o.bracket == Bracket::Tight && (other == o.reg || !o.outlives))
            })
        });

        if clear_of_evicted && out.pairs_may_share(&overlap) {
            Ok(())
        } else {
            Err(())
        }
    }

    /// Choose an eligible scratch register.
    ///
    /// Whatever we had to evict, if anything, is pushed to `out`.
    fn choose(
        &self,
        bank: RegBank,
        reason: ScratchReason,
        eligible: &dyn Fn(Reg<E>) -> bool,
        homes: HomePreference,
        unavailable: &[ScalarAllocation<E>],
        spent: &[Reg<E>],
        out: &mut Occupants<E>,
        settled: &mut Occupants<E>,
    ) -> Option<Reg<E>> {
        let allocatable = bank.stack_to_stack_move_regs(self.machine);
        let candidates = || allocatable.iter().filter_map(|reg| reg.with_repr::<E>());

        let mut settle_for = None;
        for reg in candidates() {
            if !eligible(reg)
                || self
                    .collect_occupants(reg, unavailable, spent, out)
                    .is_err()
            {
                continue;
            }

            // A cycle break holds its scratch from here until the parked move
            // fills it back in, with the cycle's other moves in between, so it
            // must be wide bracketed. If anything this register evicts wants
            // a tight bracket instead, the pair cannot be arranged and the
            // register is no use for this.
            if reason == ScratchReason::CycleBreak && out.any_tight() {
                continue;
            }

            match homes {
                HomePreference::PreferHomes => {
                    if out
                        .iter()
                        .all(|o| self.stack_home(o.reg, unavailable, &[]).is_some())
                    {
                        return Some(reg);
                    }

                    if settle_for.is_none() {
                        settle_for = Some(reg);
                        core::mem::swap(out, settled);
                    }
                }
                HomePreference::IgnoreHomes => {
                    return Some(reg);
                }
            }
        }

        // `out` holds the last candidate we looked at, which is not the one we
        // settled on; that one was put aside when we settled on it.
        let reg = settle_for?;
        core::mem::swap(out, settled);
        Some(reg)
    }

    /// Find each evicted value somewhere to sit, and remember wide-brackted
    /// ones that last the whole batch.
    fn finish_eviction(
        &mut self,
        mv: ParallelMove<E>,
        reason: ScratchReason,
        unavailable: &[ScalarAllocation<E>],
        victim: Option<Reg<E>>,
        eviction_regs: &Occupants<E>,
        evicting: &mut Vec<(Reg<E>, SpillSlot<E>)>,
    ) -> Result<Option<Reg<E>>, SolveError> {
        let Some(reg) = victim else {
            return Ok(None);
        };

        // Find each evicted value somewhere to sit. The slot has to fit that
        // register, which need not be one of the move's own bank: the
        // neighbours we put out can belong to any bank sharing units with it.
        for occupant in eviction_regs.iter() {
            let other = occupant.reg;
            let slot = match self.stack_home(other, unavailable, evicting) {
                Some(slot) => {
                    self.counts.scratch_reg_homes_reused.inc();
                    slot
                }
                None => {
                    let size = other.bank(self.machine).size(self.machine);
                    self.emergency_slot(size, occupant.bracket, unavailable, evicting)?
                }
            };
            self.counts.borrowed_scratch_regs.inc();
            let pos = self.pos;
            event!(
                self.events,
                ScratchRegBorrowed {
                    pos,
                    reg: other,
                    slot
                }
            );
            trace!("move generation: evicting {other:?} into {slot:?}");
            evicting.push((other, slot));
        }

        // A tight bracket is over as soon as the two moves it wraps are, so
        // the register is nobody's after that and there is nothing to
        // remember about it. Its slot is another matter: it holds something
        // for a stretch of the batch, which is a stretch of every wide
        // bracket, so no wide bracket may be given it. A wide one is
        // outstanding until the batch ends, and nothing else may land on
        // either the register or the slot while it is.
        //
        // Which of the two a register gets is the solver's decision, and
        // `bracket` is that same decision made here.
        for &(other, slot) in evicting.iter() {
            if self.bracket(other, unavailable) == Bracket::Tight {
                self.tight_evicted_slots.push(slot);
            } else {
                self.wide_evicted_regs.push(other);
                self.wide_evicted_slots.push(slot);
            }
        }
        trace!("move generation: borrowing {reg:?} as a scratch");
        self.chosen(mv, reason, reg.into());

        Ok(Some(reg))
    }
}

impl<E, F> ScratchSource<E> for BatchScratch<'_, '_, E, F>
where
    E: EntityRepr,
    F: InputFunction,
{
    fn overlaps(&self, a: ScalarAllocation<E>, b: ScalarAllocation<E>) -> bool {
        Interfere::interfere(self.machine, a, b)
    }

    fn is_suitable(&mut self, mv: ParallelMove<E>, reason: ScratchReason, reg: Reg<E>) -> bool {
        let bank = move_bank(self.input, mv);

        let reg32 = reg.with_repr32();
        if reg32.bank(self.machine) != bank || reg32.is_non_allocatable(self.machine) {
            return false;
        }

        self.chosen(mv, reason, reg.into());
        true
    }

    #[cfg(debug_assertions)]
    fn predicted_tight(&self, reg: Reg<E>, unavailable: &[ScalarAllocation<E>]) -> Option<bool> {
        Some(self.bracket(reg, unavailable) == Bracket::Tight)
    }

    fn find_free(
        &mut self,
        mv: ParallelMove<E>,
        reason: ScratchReason,
        unavailable: &[ScalarAllocation<E>],
    ) -> Option<Reg<E>> {
        let bank = self.bank(mv);
        let reg = find_scratch_reg(
            self.machine,
            self.region_allocation,
            self.borrowed_range.clone(),
            bank,
            |reg| self.is_used(reg, unavailable),
        )?;
        self.chosen(mv, reason, reg.into());
        Some(reg)
    }

    fn evict(
        &mut self,
        mv: ParallelMove<E>,
        reason: ScratchReason,
        unavailable: &[ScalarAllocation<E>],
        spent: &[Reg<E>],
        evicting: &mut Vec<(Reg<E>, SpillSlot<E>)>,
    ) -> Result<Option<Reg<E>>, SolveError> {
        let bank = self.bank(mv);

        let mut out = core::mem::replace(self.eviction_regs, Occupants::new());
        let mut settled = core::mem::replace(self.settled_regs, Occupants::new());

        let victim = self
            .choose(
                bank,
                reason,
                &|reg| self.is_idle(reg, unavailable),
                HomePreference::PreferHomes,
                unavailable,
                spent,
                &mut out,
                &mut settled,
            )
            .or_else(|| {
                if reason != ScratchReason::StackToStack {
                    return None;
                }
                self.choose(
                    bank,
                    reason,
                    &|reg| !self.is_idle(reg, unavailable),
                    HomePreference::IgnoreHomes,
                    unavailable,
                    spent,
                    &mut out,
                    &mut settled,
                )
            });

        let result = self.finish_eviction(mv, reason, unavailable, victim, &out, evicting);

        out.clear();
        *self.eviction_regs = out;

        settled.clear();
        *self.settled_regs = settled;

        result
    }

    fn emergency_slot(
        &mut self,
        mv: ParallelMove<E>,
        reason: ScratchReason,
        unavailable: &[ScalarAllocation<E>],
    ) -> Result<SpillSlot<E>, SolveError> {
        let size = self.bank(mv).size(self.machine);

        // A park holds its value until the move that reads it back, so every
        // tight stay in the batch runs inside it. Asking wide keeps it off any
        // slot a tight bracket has touched, which a later tight save would
        // otherwise write over.
        let slot = self.emergency_slot(size, PARK_BRACKET, unavailable, &[])?;

        self.wide_evicted_slots.push(slot);
        self.counts.cycles_parked_on_the_stack.inc();
        trace!("move generation: breaking a move-cycle with {slot:?}");
        self.chosen(mv, reason, ScalarAllocation::Stack(slot));
        Ok(slot)
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
    // edges' values) and its terminator must leave the gap alone.
    let pred_block = input.func.block(edge.pred.with_repr32());
    if pred_block.len_successors() == 1 {
        let last = block_last_inst(&pred_block);
        let last_inst = input.func.inst(last);
        if crate::liveness::terminator_leaves_the_gap_free(&last_inst) {
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

/// The register bank of the value `mv` moves.
fn move_bank<E>(input: &Input<'_, impl InputFunction>, mv: ParallelMove<E>) -> RegBank
where
    E: EntityRepr,
{
    mv.val()
        .expect("a scratch is only ever wanted for one of the batch's own moves")
        .reg_bank(input)
}

/// Does anything in `moves` read or write `reg`, including indirectly?
fn batch_uses_reg<E>(machine: &Machine, moves: &[ParallelMove<E>], reg: Reg<E>) -> bool
where
    E: EntityRepr,
{
    let reg = ScalarAllocation::Reg(reg);
    moves.iter().any(|m| {
        Interfere::interfere(machine, m.src(), reg) || Interfere::interfere(machine, m.dst(), reg)
    })
}

/// Like `batch_uses_reg`, but not counting a move from a location to itself.
///
/// The solver throws self-moves away, so they are not moves it has to make.
/// What they do say is that the register comes out of the batch holding what
/// it went in holding, which evicting it and putting it back afterwards
/// delivers. So a register only a self-move names is one we can borrow, even
/// though it is not one we can simply take.
fn batch_moves_through_reg<E>(machine: &Machine, moves: &[ParallelMove<E>], reg: Reg<E>) -> bool
where
    E: EntityRepr,
{
    let reg = ScalarAllocation::Reg(reg);
    moves.iter().any(|m| {
        !Interfere::interfere(machine, m.src(), m.dst())
            && (Interfere::interfere(machine, m.src(), reg)
                || Interfere::interfere(machine, m.dst(), reg))
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
    out: &mut Vec<ParallelMove<E>>,
) -> IResult<()>
where
    E: EntityRepr,
{
    let BatchMove { src, dst, val } = batch_move;

    let len = src.len_scalars(machine, spill_slots);
    debug_assert_eq!(len, dst.len_scalars(machine, spill_slots));

    for i in 0..len {
        out.push(ParallelMove::new(
            val,
            src.nth_scalar(machine, spill_slots, output, i)?,
            dst.nth_scalar(machine, spill_slots, output, i)?,
        ));
    }

    Ok(())
}

fn into_move<E>(mv: ParallelMove<E>) -> Move<E>
where
    E: EntityRepr,
{
    match (mv.src(), mv.dst()) {
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
            let func = input.func;
            ctx.rpo.construct(func, &mut ctx.dfs, &mut ctx.output)?;
            ctx.region_tree
                .construct(func, &mut ctx.counts, &mut ctx.dfs, &mut ctx.output)?;
            ctx.liveness
                .construct(func, &mut ctx.counts, &ctx.rpo, &mut ctx.output)?;
            ctx.live_ranges.construct(
                input,
                &mut ctx.counts,
                &mut ctx.events,
                &mut ctx.liveness,
                &mut ctx.output,
            )?;
            crate::coalescing::coalesce(ctx, input)?;
            crate::region_allocation::region_allocate(ctx, input)?;
            crate::spill_placement::place_spills(ctx, input)?;
            crate::spill_slot_allocation::allocate_spill_slots(ctx, input)?;
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

            // The registers held for fixed operands, which no span covers and
            // which nothing else describes. A val-less one holds no value to
            // track through the gaps.
            let reservations = func
                .blocks()
                .flat_map(|(block, _)| {
                    block
                        .reservations(live_ranges)
                        .into_iter()
                        .filter_map(move |r| {
                            Some((
                                r.val(live_ranges)?,
                                r.start(live_ranges),
                                r.end(live_ranges),
                                Allocation::Reg(r.reg(live_ranges)),
                                r.uses(live_ranges),
                                block,
                            ))
                        })
                })
                .collect::<Vec<_>>();

            // Where each of spill placement's stores lands, worked out from
            // the shape of the CFG the way `emit_spills` does. Checking the
            // slots against these is what keeps the seeding below from simply
            // assuming that every store did its job.
            let mut stores = Vec::new();
            for site in ctx.spill_placement.spills() {
                let val = site.val(live_ranges);
                let block = site.block();
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

                // And the reserved registers, last: a reservation is what the
                // instruction itself did with the register, and no span can
                // say otherwise.
                for &(val, start, end, alloc, _, _) in &reservations {
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
                    // Plus every register held for a read. `defines` does not
                    // apply: an instruction that both reads a register and
                    // defines the same value into it still needs the read.
                    .chain(
                        reservations
                            .iter()
                            .filter(|&&(_, start, end, _, reads, _)| {
                                reads && start <= point && point < end
                            })
                            .flat_map(|&(val, _, _, alloc, ..)| parts_of(val, alloc)),
                    )
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

                // A fixed read of the entry block's first instruction is
                // delivered here: that gap is the top of the block.
                for &(val, start, end, alloc, reads, block) in &reservations {
                    if block == entry && reads && start <= entry_start && entry_start < end {
                        needed.extend(parts_of(val, alloc));
                    }
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
                    // entry reaches it too. The predecessor will not when it
                    // has another successor or a gap-free terminator.
                    let on_edge = batch(edge_pos);
                    if !on_edge.is_empty() {
                        let succ_takes_it =
                            input_succ.len_predecessors() == 1 && succ != func.entry_block();
                        let terminator = func.inst(last);
                        let critical = !succ_takes_it
                            && (input_pred.len_successors() > 1
                                || !crate::liveness::terminator_leaves_the_gap_free(&terminator));
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

                    // A fixed operand of the terminator holds its register
                    // right up to the edge, whatever the spans say.
                    for &(val, _, end, alloc, _, block) in &reservations {
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

                    // And the registers held for the fixed reads of the
                    // successor's first instruction, delivered on this edge.
                    for &(val, start, end, alloc, reads, block) in &reservations {
                        if block != succ || !reads || start > entry || entry >= end {
                            continue;
                        }
                        let arg = match params.iter().position(|&param| param == val) {
                            Some(i) => args[i],
                            None => val,
                        };
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

    /// A cycle of moves from one spill slot to another when the machine has
    /// no free register to break it with: the allocator takes the one
    /// register off whatever is holding it, parks the cycle in it, and gives
    /// it back afterwards.
    ///
    /// The register serves twice over: once to hold the parked value for the
    /// length of the cycle, and once to stage the slot-to-slot move that frees
    /// it. So the second borrow sits inside the first and brackets only its
    /// own two moves.
    ///
    /// Run by hand rather than through `crate::test::check_allocation`, for
    /// the same reason as the test below: that helper answers `Ok(())` to
    /// `Error::TooManyLiveRegs`, and giving up is exactly the bug.
    #[test]
    fn a_cycle_of_stack_moves_evicts_a_register_when_none_is_free() {
        let test_input = TestInput::with_a_cycle_of_stack_moves_and_no_free_register();

        let mut context = Context::new();
        test_input.with_input(|input| {
            let output = crate::run(&mut context, input)
                .expect("the cycle can be broken, by evicting the one register");
            crate::checker::check(input, &output).expect("and the result is a correct allocation");
        });

        // The moves put every value where the allocation says it belongs.
        check_moves(&test_input).unwrap();

        // And these are the moves, on the first of the two edges that need
        // them: the register's own value out of the way, the cycle rotated
        // through the register, and the value back where it was.
        let context = generate(&test_input)
            .unwrap()
            .expect("allocation succeeded");
        let ctx = &context.context32;
        let edits = ctx.move_generation.edits();
        let pos = edits.first().expect("the edges need moves").0;
        let edits = edits
            .iter()
            .filter(|&&(p, _)| p == pos)
            .map(|&(_, edit)| match edit {
                Edit::CriticalEdge(CriticalEdgeEdit {
                    edit: EdgeEdit::Move(mv),
                    ..
                }) => mv,
                edit => panic!("the moves go on the edge, got {edit:?}"),
            })
            .collect::<Vec<_>>();
        let [
            Move::Spill {
                from: lent,
                to: saved,
            },
            Move::Reload {
                from: first,
                to: via,
            },
            Move::Spill {
                from: staging,
                to: parked,
            },
            Move::Reload {
                from: second,
                to: staged,
            },
            Move::Spill {
                from: stored,
                to: fills_first,
            },
            Move::Reload {
                from: unparked,
                to: restaged,
            },
            Move::Spill {
                from: written,
                to: fills_second,
            },
            Move::Reload {
                from: unsaved,
                to: returned,
            },
        ] = edits[..]
        else {
            panic!("expected a cycle rotated through one borrowed register, got {edits:?}");
        };

        // Every one of the eight moves goes through the same register.
        for reg in [lent, staging, staged, stored, restaged, written, returned] {
            assert_eq!(reg, via, "the machine has only the one register to use");
        }

        // The outer borrow spans the batch; the inner one only the two moves
        // that stage the second slot-to-slot move, and needs a slot of its
        // own so as not to tread on the parked value.
        assert_eq!(unsaved, saved, "the register's own value comes back");
        assert_eq!(unparked, parked, "and so does the parked one");
        assert_ne!(saved, parked, "from somewhere else entirely");

        // The cycle: each slot is read before the other is written over it.
        assert_eq!(
            fills_first, first,
            "the second value lands in the first slot"
        );
        assert_eq!(
            fills_second, second,
            "and the first value in the second slot",
        );
        assert_ne!(first, second, "which is what made it a cycle");
        for slot in [saved, parked] {
            assert_ne!(slot, first);
            assert_ne!(slot, second, "the borrows do not touch the cycle's slots");
        }
    }

    /// A move from one spill slot to another when the machine has no free
    /// register to stage it through: the allocator takes one off whatever is
    /// holding it, and that value goes to a slot and comes back around the
    /// move.
    ///
    /// Run by hand rather than through `crate::test::check_allocation`, which
    /// answers `Ok(())` to `Error::TooManyLiveRegs` on the grounds that not
    /// every function fits on every machine. Behind that helper this fixture
    /// would pass whether the move was made or given up on, and giving up is
    /// exactly the bug.
    #[test]
    fn a_stack_to_stack_move_evicts_a_register_when_none_is_free() {
        let test_input = TestInput::with_a_stack_to_stack_move_and_no_free_register();

        let mut context = Context::new();
        test_input.with_input(|input| {
            let output = crate::run(&mut context, input)
                .expect("the move can be made, by evicting the one register");
            crate::checker::check(input, &output).expect("and the result is a correct allocation");
        });

        // The moves put every value where the allocation says it belongs.
        check_moves(&test_input).unwrap();

        // And these are the moves: the register's own value parked in a slot,
        // the slot-to-slot move staged through it, and the value put back.
        let context = generate(&test_input)
            .unwrap()
            .expect("allocation succeeded");
        let ctx = &context.context32;
        let home = |i| match Val::<u32>::try_new(i).unwrap().stack_home(&ctx.spill_slots) {
            Some(StackAllocation::SpillSlot(slot)) => slot,
            home => panic!("v{i} lives in a single slot, got {home:?}"),
        };
        let arg = home(0);
        let param = home(2);

        let edits = ctx.move_generation.edits();
        let pos = edits.first().expect("the edge needs moves").0;
        assert!(
            edits.iter().all(|&(p, _)| p == pos),
            "the whole borrow happens in the one gap, got {edits:?}",
        );
        let edits = edits.iter().map(|&(_, edit)| edit).collect::<Vec<_>>();
        let [
            Edit::Move(Move::Spill {
                from: lent,
                to: parked,
            }),
            Edit::Move(Move::Reload {
                from: read,
                to: via,
            }),
            Edit::Move(Move::Spill {
                from: wrote,
                to: filled,
            }),
            Edit::Move(Move::Reload {
                from: restored,
                to: back,
            }),
        ] = edits[..]
        else {
            panic!("expected one staged move bracketed by a borrow, got {edits:?}");
        };
        assert_eq!(lent, via, "the register saved is the one lent out");
        assert_eq!(via, wrote, "which the move is staged through");
        assert_eq!(via, back, "and which its own value comes back to");
        assert_eq!(parked, restored, "from where it was parked");
        assert_ne!(parked, arg);
        assert_ne!(parked, param, "somewhere the move itself does not touch");
        assert_eq!(read, arg, "the argument's slot is read");
        assert_eq!(filled, param, "and the parameter's slot is filled");
    }

    /// A cycle of register-to-register moves running through every register
    /// the bank has. There is nothing free to break it with, and nothing
    /// worth evicting either: a save would have to go above the very move
    /// that fills the victim, which is in the cycle too. The broken cycle
    /// waits on the stack instead.
    ///
    /// Run by hand rather than through `crate::test::check_allocation`, for
    /// the same reason as the tests above: that helper answers `Ok(())` to
    /// `Error::TooManyLiveRegs`, and giving up is exactly the bug.
    #[test]
    fn a_cycle_through_every_register_parks_on_the_stack() {
        let test_input = TestInput::with_a_cycle_through_every_register();

        let mut context = Context::new();
        test_input.with_input(|input| {
            let output = crate::run(&mut context, input)
                .expect("the cycle can be broken, by parking it on the stack");
            crate::checker::check(input, &output).expect("and the result is a correct allocation");
        });

        // The moves put every value where the allocation says it belongs.
        check_moves(&test_input).unwrap();

        // And these are the moves: one end of the cycle parked in a slot, the
        // other rotated into the register it leaves, and the parked value read
        // back into the register that freed up behind it.
        let context = generate(&test_input)
            .unwrap()
            .expect("allocation succeeded");
        let ctx = &context.context32;

        let edits = ctx.move_generation.edits();
        let pos = edits.first().expect("the edge needs moves").0;
        assert!(
            edits.iter().all(|&(p, _)| p == pos),
            "the whole swap happens in the one gap, got {edits:?}",
        );
        let edits = edits.iter().map(|&(_, edit)| edit).collect::<Vec<_>>();
        let [
            Edit::Move(Move::Spill {
                from: parked,
                to: slot,
            }),
            Edit::Move(Move::RegReg {
                from: rotated,
                to: vacated,
            }),
            Edit::Move(Move::Reload {
                from: read,
                to: filled,
            }),
        ] = edits[..]
        else {
            panic!("expected a swap staged through a slot, got {edits:?}");
        };
        assert_eq!(slot, read, "the value comes back out of where it parked");
        assert_eq!(
            parked, vacated,
            "and into the register the rotation wrote over",
        );
        assert_eq!(
            rotated, filled,
            "while the other register takes the parked value's place",
        );
        assert_ne!(parked, rotated, "the two ends of a swap are distinct");
    }

    /// How long an evicted value sits in its slot, which is what decides who
    /// else may have that slot.
    ///
    /// Two evicted registers sharing a unit can both be put back only when
    /// one bracket nests inside the other and the inner register is empty by
    /// the time the outer reload lands on it.
    #[test]
    fn only_a_spent_tight_bracket_may_nest_inside_a_wide_one() {
        use Bracket::{Tight, Wide};

        for outlives in [false, true] {
            assert!(
                !may_share(Tight, Tight, outlives, outlives),
                "two tight brackets sit at the same depth, so the second save \
                 writes over the first (outlives: {outlives})",
            );
            assert!(
                !may_share(Wide, Wide, outlives, outlives),
                "so do two wide ones (outlives: {outlives})",
            );
        }

        for (a, b) in [(Tight, Wide), (Wide, Tight)] {
            let tight_first = a == Tight;
            assert!(
                may_share(a, b, false, false),
                "a tight bracket nests inside a wide one, and an empty \
                 register takes the wide reload harmlessly (tight first: \
                 {tight_first})",
            );
            assert!(
                !may_share(a, b, tight_first, !tight_first),
                "unless the tight bracket's register is still holding \
                 something the wide reload would destroy (tight first: \
                 {tight_first})",
            );
            assert!(
                may_share(a, b, !tight_first, tight_first),
                "the wide bracket's own register outliving the batch is \
                 expected and decides nothing (tight first: {tight_first})",
            );
        }
    }

    /// Tight and wide brackets are not symmetric, and the asymmetry is the
    /// whole rule: the wide one opens before the batch's first move and closes
    /// after its last, so every tight bracket runs inside it and a save of
    /// theirs lands on top of what it is holding. Tight brackets never overlap
    /// one another, since `push_move` pushes each tight save straight after the
    /// two halves its reload opened with nothing in between, so they are free
    /// to share.
    ///
    /// Getting this backwards is a silent miscompile, not a panic: the wide
    /// reload simply puts back whatever the tight save left there. So it is
    /// pinned here on the plain slices `slot_is_taken` takes, where the rule is
    /// visible without a machine to arrange around it.
    #[test]
    fn a_wide_eviction_may_not_share_a_slot_with_a_tight_one() {
        let slot = |i| SpillSlot::<u32>::try_new(i).unwrap();

        // A slot some tight bracket has already used, and a batch that names
        // nothing at all, so `slot_is_taken` answers out of the tight/wide
        // rule alone.
        let used = slot(0);
        let tight_evicted_slots = &[used][..];

        assert!(
            !slot_is_taken::<u32>(
                &[],
                &[],
                tight_evicted_slots,
                Bracket::Tight,
                &[],
                used,
                &[]
            ),
            "two tight brackets never run at once, so the second is free to reuse \
             what the first has finished with",
        );
        assert!(
            slot_is_taken::<u32>(&[], &[], tight_evicted_slots, Bracket::Wide, &[], used, &[]),
            "but a wide one is open across every tight bracket, so a tight save \
             would write over what it is holding",
        );

        // A slot nobody has touched is nobody's, whichever kind of stay is
        // asking: the rule above is about the slots in `tight_evicted_slots`, not
        // about wide brackets being fussy in general.
        let fresh = slot(1);
        for bracket in [Bracket::Tight, Bracket::Wide] {
            assert!(
                !slot_is_taken::<u32>(&[], &[], tight_evicted_slots, bracket, &[], fresh, &[]),
                "a slot no bracket has used is free ({bracket:?})",
            );
        }

        // A wide bracket's slot, by contrast, is off limits to everything:
        // it is still holding its value when any later stay would run.
        let wide_evicted_slots = &[used][..];
        for bracket in [Bracket::Tight, Bracket::Wide] {
            assert!(
                slot_is_taken::<u32>(&[], wide_evicted_slots, &[], bracket, &[], used, &[]),
                "a slot evicted for the whole batch is nobody else's ({bracket:?})",
            );
        }
    }

    /// A slot a broken cycle is parked in is off limits to an eviction of
    /// either width.
    ///
    /// The park holds its value from before the bracket opens until after it
    /// closes, so however short the stay, it is a stay inside the park's.
    /// This one the solver also asserts, in
    /// `debug_assert_tight_eviction_is_sound`; here is the caller's side of
    /// it, which is what keeps the assertion from ever firing.
    #[test]
    fn an_eviction_may_not_land_on_a_parked_cycle() {
        let slot = |i| SpillSlot::<u32>::try_new(i).unwrap();

        let parked = slot(0);
        let unavailable = &[ScalarAllocation::Stack(parked)][..];

        for bracket in [Bracket::Tight, Bracket::Wide] {
            assert!(
                slot_is_taken::<u32>(&[], &[], &[], bracket, unavailable, parked, &[]),
                "a parked cycle's slot is nobody else's ({bracket:?})",
            );
            assert!(
                !slot_is_taken::<u32>(&[], &[], &[], bracket, unavailable, slot(1), &[]),
                "but only that slot ({bracket:?})",
            );
        }
    }

    /// A park does not take a slot a tight bracket has already used, even
    /// though that bracket is finished with it.
    #[test]
    fn a_park_may_not_share_a_slot_with_a_tight_bracket() {
        let slot = |i| SpillSlot::<u32>::try_new(i).unwrap();

        let used = slot(0);
        let tight_evicted_slots = &[used][..];

        assert!(
            slot_is_taken::<u32>(&[], &[], tight_evicted_slots, PARK_BRACKET, &[], used, &[]),
            "a park outlives every tight stay in the batch, so a slot one of \
             them has used is not free for it to take",
        );
        assert!(
            !slot_is_taken::<u32>(
                &[],
                &[],
                tight_evicted_slots,
                Bracket::Tight,
                &[],
                used,
                &[]
            ),
            "which is exactly what a tight request would allow, so the park \
             must not be making one",
        );

        // The rule is about used slots, not about parks finding nowhere.
        assert!(
            !slot_is_taken::<u32>(
                &[],
                &[],
                tight_evicted_slots,
                PARK_BRACKET,
                &[],
                slot(1),
                &[]
            ),
            "a slot no bracket has used is free for a park like anything else",
        );
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

        let result = Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run_with(
                m::default::<TestInput>(),
                crate::test::corpus(),
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

        let result = Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run_with(
                m::default::<TestInput>(),
                crate::test::corpus(),
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
        Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run_with(
                m::default::<TestInput>(),
                crate::test::corpus(),
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

    /// One value is never recomputed into one register twice at one point.
    ///
    /// `resolve` does not deduplicate its destinations -- two spans can ask
    /// for the same value in the same place -- so `sequentialize` dedups the
    /// rematerializations instead.
    ///
    /// **This test cannot fail today**, and is honest about that: no input
    /// in the corpus or from the generator produces a duplicated destination
    /// that rematerializes (0 of 70,999 remats over 13,925 corpus inputs),
    /// so removing that `dedup` passes the whole suite. It states the
    /// invariant where a future input that does trip it will be caught,
    /// rather than leaving the property unwritten.
    #[cfg(feature = "visualizer")]
    #[test]
    fn a_value_is_rematerialized_once_per_place() -> CheckResult<TestInput> {
        Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run_with(
                m::default::<TestInput>(),
                crate::test::corpus(),
                |test_input: &TestInput| -> Result<(), String> {
                    let Some(context) = generate(test_input)? else {
                        return Ok(());
                    };
                    let ctx = &context.context32;

                    let mut seen = BTreeSet::new();
                    for (pos, remat) in ctx.move_generation.remats.iter().copied() {
                        if !seen.insert((pos, remat.val, remat.dest)) {
                            return Err(format!(
                                "{:?} is rematerialized into {:?} at {pos:?} more than once",
                                remat.val, remat.dest,
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
        Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run_with(
                m::default::<TestInput>(),
                crate::test::corpus(),
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

        // The corpus, plus the corpus again with every value
        // rematerializable: between them they reach every corner of move
        // generation.
        let mut inputs = crate::test::corpus();
        inputs.extend(crate::test::corpus().into_iter().map(|mut test_input| {
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
