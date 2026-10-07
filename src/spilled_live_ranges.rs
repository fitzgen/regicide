//! The range over which each spilled value needs its slot.
//!
//! A slot only has to be reserved where its value is both live *and* spilled.
//! A value that is spilled, reloaded, and then kept in a register does not need
//! its slot across that tail. Narrowing to that range lets more values share a
//! slot, which shrinks the frame.
//!
//! Each value gets one **head**: the nearest common dominator of the points
//! that write it into its slot. Below the head, the slot is reserved wherever a
//! *slot read* is still reachable, which is a backwards dataflow run exactly as
//! liveness is. A slot read is any point a stack-allocated span covers, the
//! entry of a block the value arrives at on the stack, or a stack-constrained
//! operand.
//!
//! # Why one dominating head
//!
//! Spill slot allocation colors these ranges with a greedy one-shot walk in
//! dominance order, which is correct only because a value's definition
//! dominates every point it is live at. Spill placement emits several spills
//! per value, so starting a range at the first spill in reverse post-order
//! would break that and let the walk co-assign two values that really overlap.
//! The nearest common dominator keeps a single start point that dominates the
//! whole range.
//!
//! Cutting the range off above the head is exact, not conservative: every path
//! from above reaches a read only through the head, which rewrites the slot on
//! the way past.
//!
//! # Why reachability, not an interval
//!
//! Only a block's own instructions are contiguous, so "between the head and the
//! last read" does not name a region of the program. Reachability is what that
//! means on a graph, and it is tighter: a value reloaded on one arm of a branch
//! keeps its slot on that arm alone.
//!
//! It also covers the middles a value needs but never reads. `val_home` gives a
//! value one home for the whole function, so a value shaped `stack -> register
//! -> stack` needs the same slot again below; the points in between reach those
//! reads and stay reserved.

use crate::{
    Block, Entity as _, Val,
    btree::{BTreeSet, BTreeSetArena},
    entity::{EntityRepr, EntitySet, SecondaryMap},
    error::IResult,
    input::{DefUse, Input, InputBlock as _, InputFunction, InputInst as _, OperandConstraint},
    live_ranges::{LivePoint, LiveRanges},
    liveness::{Liveness, for_each_operand_rev},
    output::OutputInner,
    region_allocation::RegionAllocation,
    rpo::Rpo,
    spill_placement::SpillPlacement,
    timing::Timing,
};
use alloc::vec::Vec;
use core::ops::Range;

/// What happens to a value's slot reservation at a program point.
///
/// The derived ordering puts `Kill` before `Def` at the same point, so a
/// reservation ending at `p` frees its slot before one beginning at `p` looks
/// for one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum RangeEvent {
    Kill,
    Def,
}

/// Where each spilled value needs its slot.
pub struct SpilledLiveRanges<E>
where
    E: EntityRepr,
{
    arena: BTreeSetArena<E, Val<E>>,

    /// The values whose slot is reserved on entry to each block.
    live_in: SecondaryMap<Block<E>, BTreeSet<E, Val<E>>>,

    /// The values whose slot is reserved at each block's exit: everything
    /// reserved on entry to any successor.
    live_out: SecondaryMap<Block<E>, BTreeSet<E, Val<E>>>,

    /// The point each value's reservation begins at, which dominates every
    /// other point in its range.
    head: SecondaryMap<Val<E>, Option<LivePoint<E>>>,

    /// Parameters of the function, whose slot the caller fills before entry.
    is_function_param: EntitySet<Val<E>>,

    /// The block each value's head lies in.
    ///
    /// Separate from `head` because the nearest-common-dominator walk runs over
    /// blocks, and an edge spill's head names a point its block does not hold.
    head_block: SecondaryMap<Val<E>, Option<Block<E>>>,

    /// Sorted by block, so one block's entries are contiguous.
    heads_in_block: Vec<(Block<E>, Val<E>)>,

    /// Each block's range within `heads_in_block`.
    block_heads: SecondaryMap<Block<E>, (u32, u32)>,

    /// Every slot read, sorted by block and then program order.
    reads: Vec<(Block<E>, LivePoint<E>, Val<E>)>,

    /// Each block's range within `reads`.
    block_reads: SecondaryMap<Block<E>, (u32, u32)>,

    /// Sorted by block and then program order.
    events: Vec<(Block<E>, LivePoint<E>, RangeEvent, Val<E>)>,

    /// Each block's range within `events`.
    block_events: SecondaryMap<Block<E>, (u32, u32)>,

    /// The reservations live at the point being processed.
    live: BTreeSet<E, Val<E>>,

    /// Holds a set's values so a walk can mutate the set it came from.
    scratch: Vec<Val<E>>,

    worklist: Vec<Block<E>>,

    on_worklist: EntitySet<Block<E>>,
}

impl<E> Default for SpilledLiveRanges<E>
where
    E: EntityRepr,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<E> SpilledLiveRanges<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        Self {
            arena: BTreeSetArena::new(),
            live_in: SecondaryMap::new(BTreeSet::new()),
            live_out: SecondaryMap::new(BTreeSet::new()),
            head: SecondaryMap::new(None),
            head_block: SecondaryMap::new(None),
            is_function_param: EntitySet::new(),
            heads_in_block: Vec::new(),
            block_heads: SecondaryMap::new((0, 0)),
            reads: Vec::new(),
            block_reads: SecondaryMap::new((0, 0)),
            events: Vec::new(),
            block_events: SecondaryMap::new((0, 0)),
            live: BTreeSet::new(),
            scratch: Vec::new(),
            worklist: Vec::new(),
            on_worklist: EntitySet::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            arena,
            live_in,
            live_out,
            head,
            head_block,
            is_function_param,
            heads_in_block,
            block_heads,
            reads,
            block_reads,
            events,
            block_events,
            live,
            scratch,
            worklist,
            on_worklist,
        } = self;
        live.clear(arena);
        scratch.clear();
        arena.reset();
        live_in.reset();
        live_out.reset();
        head.reset();
        head_block.reset();
        is_function_param.reset();
        heads_in_block.clear();
        block_heads.reset();
        reads.clear();
        block_reads.reset();
        events.clear();
        block_events.reset();
        worklist.clear();
        on_worklist.reset();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            arena,
            live_in,
            live_out,
            head,
            head_block,
            is_function_param,
            heads_in_block,
            block_heads,
            reads,
            block_reads,
            events,
            block_events,
            live,
            scratch,
            worklist,
            on_worklist,
        } = self;
        arena.is_reset()
            && live_in.is_reset()
            && live_out.is_reset()
            && head.is_reset()
            && head_block.is_reset()
            && is_function_param.is_reset()
            && heads_in_block.is_empty()
            && block_heads.is_reset()
            && reads.is_empty()
            && block_reads.is_reset()
            && events.is_empty()
            && block_events.is_reset()
            && live.is_empty()
            && scratch.is_empty()
            && worklist.is_empty()
            && on_worklist.is_reset()
    }

    /// The values whose slot is reserved on entry to `block`.
    pub(crate) fn live_in(&self, block: Block<E>) -> impl Iterator<Item = Val<E>> + '_ {
        self.live_in[block].iter(&self.arena).copied()
    }

    /// The reservations that begin and end within `block`, in program order.
    pub(crate) fn events(
        &self,
        block: Block<E>,
    ) -> impl Iterator<Item = (LivePoint<E>, RangeEvent, Val<E>)> + '_ {
        let (start, end) = self.block_events[block];
        self.events[start as usize..end as usize]
            .iter()
            .map(|&(_, point, event, val)| (point, event, val))
    }

    /// Is `val`'s slot reserved across all of `range`, which must lie within
    /// `block`?
    ///
    /// Move generation asks before parking an evicted register in a value's
    /// slot: narrowed, the slot may belong to someone else by then.
    pub(crate) fn reserved_across(
        &self,
        block: Block<E>,
        val: Val<E>,
        range: Range<LivePoint<E>>,
    ) -> bool {
        debug_assert!(range.start < range.end);

        let mut reserved = self.live_in[block].contains(&self.arena, &val);
        for (point, event, v) in self.events(block) {
            if v != val {
                continue;
            }
            if point > range.start {
                break;
            }
            reserved = event == RangeEvent::Def;
        }

        if !reserved {
            return false;
        }

        // Held at the start, so it covers the range unless a kill interrupts.
        !self.events(block).any(|(point, event, v)| {
            v == val && event == RangeEvent::Kill && range.start < point && point < range.end
        })
    }

    /// Compute every spilled value's spilled live range.
    pub(crate) fn construct(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        rpo: &Rpo<E>,
        liveness: &Liveness<E>,
        live_ranges: &LiveRanges<E>,
        region_allocation: &RegionAllocation<E>,
        spill_placement: &SpillPlacement<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        let _timing = Timing::new("spilled live ranges");

        debug_assert!(self.is_reset());

        let spilled = region_allocation.spilled();
        if spilled.is_empty() {
            return Ok(());
        }

        self.collect_heads(
            input,
            rpo,
            liveness,
            live_ranges,
            spilled,
            region_allocation,
            spill_placement,
            output,
        )?;
        self.index_heads(spilled);
        self.collect_reads(
            input,
            rpo,
            liveness,
            live_ranges,
            region_allocation,
            spilled,
            spill_placement,
        );
        self.run_to_fixed_point(input, rpo);
        self.collect_events(input, rpo);

        self.check_writes_are_reserved(
            input,
            rpo,
            liveness,
            live_ranges,
            region_allocation,
            spill_placement,
        );
        Ok(())
    }

    /// Find the point each value's reservation begins at: the nearest common
    /// dominator of the points that write it into its slot.
    fn collect_heads(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        rpo: &Rpo<E>,
        liveness: &Liveness<E>,
        live_ranges: &LiveRanges<E>,
        spilled: &EntitySet<Val<E>>,
        region_allocation: &RegionAllocation<E>,
        spill_placement: &SpillPlacement<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        // An entry-block parameter is a parameter of the *function*: the caller
        // fills its slot before entry, so there is no write inside to anchor a
        // head to and it pins to the function's start.
        let entry = output.with_repr(input.func.entry_block())?;
        for param in input.func.block(entry.with_repr32()).params() {
            let val = output.with_repr(param)?;
            if spilled.contains(val) {
                self.head_block[val] = Some(entry);
                self.head[val] = Some(entry.start_point(input));
                self.is_function_param.insert(val);
            }
        }

        // A def straight onto the stack *is* a slot write, so it seeds the
        // dominator like any other site. A def into a register writes no slot,
        // so its head may sit below it; that is where the win comes from.
        self.collect_stack_def_sites(input, live_ranges, region_allocation);

        for site in spill_placement.spills() {
            let val = site.val(live_ranges);
            debug_assert!(spilled.contains(val));

            let block = site.block();
            let point = if site.point() < block.end_point(input) {
                site.point()
            } else {
                // A spill on the block's outgoing edges, which no point within
                // the block names. Every path to a read below runs through the
                // block, so its entry dominates those reads just as the edge
                // does.
                block.start_point(input)
            };
            self.widen_head_to(input, val, block, point);
        }

        // A parameter arriving on the stack is written by the moves on the
        // edges into its block, which run in the predecessors. Its own
        // definition does not dominate those, so widen to cover them.
        for bundle in region_allocation.stack_bundles().iter().copied() {
            for span in bundle.spans(live_ranges) {
                let val = span.val(live_ranges);
                let block = span.block(input.func, live_ranges);
                if span.start(live_ranges) != block.start_point(input)
                    || !block.is_live_in(liveness, val)
                {
                    continue;
                }
                // The arrival is itself a write. Seeding with it keeps the head
                // in the defining block instead of sliding into a predecessor.
                self.widen_head_to(input, val, block, block.start_point(input));
                for pred in reachable_predecessors(input, rpo, block) {
                    self.widen_head_to(input, val, pred, pred.end_point(input).prev_point());
                }
            }
        }

        // Anything still without a head writes its slot nowhere we found, so
        // its definition is the only place its range can begin.
        let mut undefined = false;
        for val in spilled.iter() {
            undefined |= self.head[val].is_none();
        }
        if undefined {
            self.collect_def_sites(input, rpo, spilled, output)?;
        }

        self.check_every_value_has_a_head(input, rpo, spilled);
        Ok(())
    }

    /// Seed the head of every value defined straight into its slot.
    fn collect_stack_def_sites(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        live_ranges: &LiveRanges<E>,
        region_allocation: &RegionAllocation<E>,
    ) {
        for bundle in region_allocation.stack_bundles().iter().copied() {
            for span in bundle.spans(live_ranges) {
                let val = span.val(live_ranges);
                for u in span.uses(live_ranges) {
                    let point = u.point(live_ranges);
                    let input_inst = input.func.inst(point.inst().with_repr32());
                    if input_inst.operand(u.operand(live_ranges)).kind() == DefUse::Def {
                        self.widen_head_to(input, val, span.block(input.func, live_ranges), point);
                    }
                }
            }
        }
    }

    /// Index the heads by block, so neither the dataflow nor the event walk
    /// has to scan every value.
    fn index_heads(&mut self, spilled: &EntitySet<Val<E>>) {
        for val in spilled.iter() {
            let Some(block) = self.head_block[val] else {
                // Unreachable block, so the coloring never asks about it.
                continue;
            };
            self.heads_in_block.push((block, val));
        }
        self.heads_in_block.sort_unstable();
        index_by_block(
            &self.heads_in_block,
            |&(block, _)| block,
            &mut self.block_heads,
        );
    }

    /// Move `val`'s head up until it dominates `point` in `block`, which is
    /// somewhere its slot is written.
    fn widen_head_to(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        val: Val<E>,
        block: Block<E>,
        point: LivePoint<E>,
    ) {
        // A function parameter's slot is filled before entry, so its head
        // stays there.
        if self.is_function_param.contains(val) {
            return;
        }

        let Some(prev) = self.head_block[val] else {
            self.head_block[val] = Some(block);
            self.head[val] = Some(point);
            return;
        };

        let ncd = nearest_common_dominator(input, prev, block);
        self.head_block[val] = Some(ncd);
        self.head[val] = Some(if ncd == prev && ncd == block {
            // Both sites are in this block, so the earlier dominates.
            self.head[val].unwrap().min(point)
        } else if ncd == prev {
            self.head[val].unwrap()
        } else if ncd == block {
            point
        } else {
            // Above both sites, so above every point in either.
            ncd.start_point(input)
        });
    }

    /// Give every value that still has no head one at its definition.
    fn collect_def_sites(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        rpo: &Rpo<E>,
        spilled: &EntitySet<Val<E>>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        for block in rpo.iter() {
            let input_block = input.func.block(block.with_repr32());

            for param in input_block.params() {
                let val = output.with_repr(param)?;
                if spilled.contains(val) && self.head[val].is_none() {
                    self.head_block[val] = Some(block);
                    self.head[val] = Some(block.start_point(input));
                }
            }

            let head = &mut self.head;
            let head_block = &mut self.head_block;
            for_each_operand_rev(&input_block, output, |_output, point, _i, kind, val| {
                if kind == DefUse::Def && spilled.contains(val) && head[val].is_none() {
                    head_block[val] = Some(block);
                    head[val] = Some(point);
                }
                Ok(())
            })?;
        }
        Ok(())
    }

    /// Find every point at which a slot can still be read.
    fn collect_reads(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        rpo: &Rpo<E>,
        liveness: &Liveness<E>,
        live_ranges: &LiveRanges<E>,
        region_allocation: &RegionAllocation<E>,
        spilled: &EntitySet<Val<E>>,
        spill_placement: &SpillPlacement<E>,
    ) {
        // Values handed across outgoing edges on the stack, so each successor's
        // entry can be charged for them too.
        let mut hands_off_on_the_stack: Vec<(Block<E>, Val<E>)> = Vec::new();

        // A spill site is a range member, not just a seed: it *writes* the
        // slot, so the slot must be the value's own there even when no read
        // reaches it.
        for site in spill_placement.spills() {
            let val = site.val(live_ranges);
            let block = site.block();
            let block_end = block.end_point(input);
            if site.point() < block_end {
                self.reads.push((block, site.point(), val));
                continue;
            }

            // An edge spill, which no point in the block names. An edge's moves
            // are solved as one batch with the successor's entry, so charge it
            // to both.
            self.reads.push((block, block_end.prev_point(), val));
            hands_off_on_the_stack.push((block, val));
        }

        // A function parameter holds its slot from the first point: the caller
        // filled it, per `Output::block_param_allocs`, so nothing inside the
        // function writes it and nothing above records it.
        for val in self.is_function_param.iter() {
            let entry = self.head_block[val].expect("a function parameter's head is the entry");
            self.reads.push((entry, entry.start_point(input), val));
        }

        // A stack-allocated span holds its slot across the whole span, through
        // the gap at its end where a reload takes the value back out.
        for bundle in region_allocation.stack_bundles().iter().copied() {
            for span in bundle.spans(live_ranges) {
                let val = span.val(live_ranges);
                debug_assert!(spilled.contains(val));

                let block = span.block(input.func, live_ranges);
                let block_end = block.end_point(input);
                let end = span.end(live_ranges);

                if end < block_end {
                    self.reads.push((block, end, val));
                } else {
                    // The span runs to the block's exit, so the reload is in a
                    // successor or on an edge rather than here.
                    self.reads.push((block, block_end.prev_point(), val));
                    hands_off_on_the_stack.push((block, val));
                }

                // A value arriving on the stack is written by the edge moves,
                // which run at the end of each predecessor.
                if span.start(live_ranges) == block.start_point(input)
                    && block.is_live_in(liveness, val)
                {
                    for pred in reachable_predecessors(input, rpo, block) {
                        self.reads
                            .push((pred, pred.end_point(input).prev_point(), val));
                    }
                }
            }
        }

        // A value arriving on the stack is read at the block's entry, where the
        // reload runs.
        hands_off_on_the_stack.sort_unstable();
        hands_off_on_the_stack.dedup();
        for &(pred, val) in &hands_off_on_the_stack {
            for succ in input.func.block(pred.with_repr32()).successors() {
                let Some(succ) = succ.with_repr::<E>() else {
                    continue;
                };
                if succ.is_live_in(liveness, val) {
                    self.reads.push((succ, succ.start_point(input), val));
                }
            }
        }

        // A stack-constrained operand reads the slot even when the span around
        // it is in a register.
        for span in live_ranges.spans() {
            let val = span.val(live_ranges);
            if !spilled.contains(val) {
                continue;
            }
            for u in span.uses(live_ranges) {
                let point = u.point(live_ranges);
                let input_inst = input.func.inst(point.inst().with_repr32());
                if input_inst.operand(u.operand(live_ranges)).constraint()
                    == OperandConstraint::Stack
                {
                    self.reads
                        .push((span.block(input.func, live_ranges), point, val));
                }
            }
        }

        // Keep only reads the head dominates. One it does not is reached by a
        // path that never ran the head's write, so it reads nothing this value
        // left there.
        self.reads.retain(|&(block, point, val)| {
            let head_block = self.head_block[val].expect("every read is of a value with a head");
            if !dominates(input, head_block, block) {
                return false;
            }
            // In the head's own block, points above the head read whatever was
            // there before.
            block != head_block || self.head[val].unwrap() <= point
        });

        self.reads.sort_unstable();
        self.reads.dedup();
        index_by_block(&self.reads, |&(block, _, _)| block, &mut self.block_reads);
    }

    /// Decide, for each block boundary, whose slots are still reserved there.
    fn run_to_fixed_point(&mut self, input: &Input<'_, impl InputFunction>, rpo: &Rpo<E>) {
        // Pushing in reverse post-order pops in post-order, so a block follows
        // its successors and the loop-free case takes one pass.
        for block in rpo.iter() {
            self.on_worklist.insert(block);
            self.worklist.push(block);
        }

        while let Some(block) = self.worklist.pop() {
            self.on_worklist.remove(block);

            // Through `scratch`, so `live_in` and `live_out` are never borrowed
            // at once.
            self.scratch.clear();
            for succ in input.func.block(block.with_repr32()).successors() {
                let Some(succ) = succ.with_repr::<E>() else {
                    continue;
                };
                self.scratch
                    .extend(self.live_in[succ].iter(&self.arena).copied());
            }
            self.live_out[block].clear(&mut self.arena);
            for val in self.scratch.drain(..) {
                self.live_out[block].insert(&mut self.arena, val);
            }

            self.live.clear(&mut self.arena);
            self.scratch
                .extend(self.live_out[block].iter(&self.arena).copied());
            let (start, end) = self.block_reads[block];
            self.scratch.extend(
                self.reads[start as usize..end as usize]
                    .iter()
                    .map(|&(_, _, val)| val),
            );
            for val in self.scratch.drain(..) {
                self.live.insert(&mut self.arena, val);
            }

            // Nothing is reserved above its head, not even around a back edge:
            // every path to a read rewrites the slot on its way through.
            let (start, end) = self.block_heads[block];
            for &(_, val) in &self.heads_in_block[start as usize..end as usize] {
                self.live.remove(&mut self.arena, &val);
            }

            self.scratch.extend(self.live.iter(&self.arena).copied());
            let mut changed = false;
            for val in self.scratch.drain(..) {
                // Below its head, which is what lets the coloring treat the
                // head as the value's one definition.
                debug_assert!(dominates(input, self.head_block[val].unwrap(), block,));
                changed |= self.live_in[block].insert(&mut self.arena, val);
            }

            if changed {
                for pred in input.func.block(block.with_repr32()).predecessors() {
                    let Some(pred) = pred.with_repr::<E>() else {
                        continue;
                    };
                    if self.on_worklist.insert(pred) {
                        self.worklist.push(pred);
                    }
                }
            }
        }

        self.live.clear(&mut self.arena);
    }

    /// Turn the reservation sets into the events spill slot allocation walks.
    fn collect_events(&mut self, input: &Input<'_, impl InputFunction>, rpo: &Rpo<E>) {
        for block in rpo.iter() {
            let first = self.events.len();

            // Anything reserved at the exit outlives the block, so no kill here.
            self.live.clear(&mut self.arena);
            self.scratch
                .extend(self.live_out[block].iter(&self.arena).copied());
            for val in self.scratch.drain(..) {
                self.live.insert(&mut self.arena, val);
            }

            // Backwards, so the first read we meet for a value is its last.
            let (start, end) = self.block_reads[block];
            let block_end = block.end_point(input);
            for i in (start as usize..end as usize).rev() {
                let (_, point, val) = self.reads[i];
                if self.live.insert(&mut self.arena, val) {
                    // Exclusive, and after the last read, so one value's last
                    // read and another's first write can share a gap without
                    // sharing a slot.
                    let kill = point.next_point().min(block_end);
                    self.events.push((block, kill, RangeEvent::Kill, val));
                }
            }

            // A reservation with no read here still needs its slot for the
            // write itself: an instruction writing its result to the stack has
            // a destination even when nothing reads it. Give it the write's
            // own instruction, as live span construction does for a dead def.
            let (start, end) = self.block_heads[block];
            for &(_, val) in &self.heads_in_block[start as usize..end as usize] {
                let head = self.head[val].unwrap();
                self.events.push((block, head, RangeEvent::Def, val));
                if !self.live.remove(&mut self.arena, &val) {
                    self.events.push((
                        block,
                        head.inst_boundary_after().min(block_end),
                        RangeEvent::Kill,
                        val,
                    ));
                }
            }

            self.events[first..]
                .sort_unstable_by_key(|&(_, point, event, val)| (point, event, val));
            self.block_events[block] = (
                u32::try_from(first).unwrap(),
                u32::try_from(self.events.len()).unwrap(),
            );
        }

        self.live.clear(&mut self.arena);
    }

    /// Every spilled value has a head, unless it is defined in an unreachable
    /// block, which the coloring never asks about.
    fn check_every_value_has_a_head(
        &self,
        input: &Input<'_, impl InputFunction>,
        rpo: &Rpo<E>,
        spilled: &EntitySet<Val<E>>,
    ) {
        if !cfg!(debug_assertions) {
            return;
        }
        for val in spilled.iter() {
            debug_assert!(
                self.head[val].is_some()
                    || !input.func.blocks().any(|(block, input_block)| {
                        rpo.is_reachable(match block.with_repr::<E>() {
                            Some(block) => block,
                            None => return false,
                        }) && input_block
                            .params()
                            .any(|param| param.with_repr::<E>() == Some(val))
                    }),
                "{val:?} needs a stack slot, so it must have somewhere its reservation begins",
            );
        }
    }
}

impl<E> SpilledLiveRanges<E>
where
    E: EntityRepr,
{
    /// Every point that *writes* a value's slot lies within its range.
    ///
    /// The invariant the pass turns on: a write outside the range lands in a
    /// slot that may belong to someone else by then, which is a miscompile
    /// rather than merely a larger frame.
    fn check_writes_are_reserved(
        &self,
        input: &Input<'_, impl InputFunction>,
        rpo: &Rpo<E>,
        liveness: &Liveness<E>,
        live_ranges: &LiveRanges<E>,
        region_allocation: &RegionAllocation<E>,
        spill_placement: &SpillPlacement<E>,
    ) {
        if !cfg!(debug_assertions) {
            return;
        }

        let reserved_at = |block: Block<E>, point: LivePoint<E>, val: Val<E>| {
            self.reserved_across(block, val, point..point.next_point())
        };

        for site in spill_placement.spills() {
            let val = site.val(live_ranges);
            let block = site.block();
            let point = site.point().min(block.end_point(input).prev_point());
            debug_assert!(
                reserved_at(block, point, val),
                "a spill writes {val:?}'s slot at {point:?} in {block:?}, which is outside the \
                 range its slot is reserved over",
            );
        }

        // A value arriving on the stack is written by the edge moves, which run
        // in the predecessors.
        for bundle in region_allocation.stack_bundles().iter().copied() {
            for span in bundle.spans(live_ranges) {
                let val = span.val(live_ranges);
                let block = span.block(input.func, live_ranges);
                if span.start(live_ranges) != block.start_point(input)
                    || !block.is_live_in(liveness, val)
                {
                    continue;
                }
                debug_assert!(
                    reserved_at(block, block.start_point(input), val),
                    "{val:?} arrives on the stack in {block:?}, but its slot is not reserved \
                     there",
                );
                for pred in reachable_predecessors(input, rpo, block) {
                    let exit = pred.end_point(input).prev_point();
                    debug_assert!(
                        reserved_at(pred, exit, val),
                        "{val:?} is written into its slot on the edge from {pred:?} into \
                         {block:?}, but its slot is not reserved at {pred:?}'s exit",
                    );
                }
            }
        }
    }
}

/// The predecessors of `block` that any path from the entry reaches.
fn reachable_predecessors<'a, E>(
    input: &'a Input<'_, impl InputFunction>,
    rpo: &'a Rpo<E>,
    block: Block<E>,
) -> impl Iterator<Item = Block<E>> + 'a
where
    E: EntityRepr,
{
    input
        .func
        .block(block.with_repr32())
        .predecessors()
        .filter_map(|pred| pred.with_repr::<E>())
        .filter(|&pred| rpo.is_reachable(pred))
        .collect::<Vec<_>>()
        .into_iter()
}

/// Record where each block's run of entries lies within `items`, which must
/// already be sorted by block.
fn index_by_block<E, T>(
    items: &[T],
    block_of: impl Fn(&T) -> Block<E>,
    index: &mut SecondaryMap<Block<E>, (u32, u32)>,
) where
    E: EntityRepr,
{
    let mut start = 0;
    while start < items.len() {
        let block = block_of(&items[start]);
        let mut end = start + 1;
        while end < items.len() && block_of(&items[end]) == block {
            end += 1;
        }
        index[block] = (u32::try_from(start).unwrap(), u32::try_from(end).unwrap());
        start = end;
    }
}

/// Does `a` dominate `b`?
fn dominates<E>(input: &Input<'_, impl InputFunction>, a: Block<E>, b: Block<E>) -> bool
where
    E: EntityRepr,
{
    input.func.block(a.with_repr32()).dominates(b.with_repr32())
}

/// The nearest block that dominates both `a` and `b`.
fn nearest_common_dominator<E>(
    input: &Input<'_, impl InputFunction>,
    a: Block<E>,
    b: Block<E>,
) -> Block<E>
where
    E: EntityRepr,
{
    let mut a = a;
    while !dominates(input, a, b) {
        a = input
            .func
            .block(a.with_repr32())
            .immediate_dominator()
            .map(|idom| {
                idom.with_repr::<E>()
                    .expect("every block index already fit in `E` in the earlier passes")
            })
            .expect("the entry block dominates every block, so the walk terminates");
    }
    a
}
