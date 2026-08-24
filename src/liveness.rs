//! Liveness analysis.
//!
//! A value is *live* at a program point when that point can potentially reach a
//! use of that value.
//!
//! This is computed with a backwards analysis, from uses (which mark values
//! live) to defs (which remove values from the live set) and from successor
//! blocks to predecessor blocks.
//!
//! We compute two live sets for each block:
//!
//! 1. The live-in set, which is the set of values that are live when control
//!    enters the block.
//!
//! 2. The live-out set, which is the set of values that are live when control
//!    exits the block.
//!
//! ```text
//! live_out(block) = union(live_in(s) - params(s) for s in successors(block))
//!                 + { the i'th block argument passed to a successor s
//!                     where params(s)[i] is in live_in(s) }
//!
//! live_in(block) = live_out(block) + uses(block) - inst_defs(block)
//! ```
//!
//! We use the classic worklist of blocks approach to implement the
//! analysis. Processing a block entails updating its live-out set based on its
//! successors, then processing each instruction in the block in reverse order,
//! and then updating its live-in set. If the live-in set changed, then we need
//! to re-enqueue the block's predecessors, as their live-out sets might change.
//! The worklist is seeded such that we initially process blocks in post-order,
//! which ensures that, when we have a loop-free control-flow graph, we only
//! process each block once. As we flow backwards, uses mark values live and
//! definitions unmark values live.
//!
//! The analysis flows backwards from block parameters to block arguments; it
//! does not assume that all block parameters are live. A block parameter's
//! definition logically happens *on the control-flow edge*, not at the start of
//! its block, so we unmark successor blocks' parameters when building a block's
//! live-out set, not when we reach the start of a block, which would exclude
//! them from the block's live-in set. Then, values passed as block arguments
//! from this block's terminator to any of its successors are marked live if the
//! the associated block parameter is in the target block's live-in set. Thus,
//! if a block parameter is never used, nor any of its associated block
//! arguments, they are omitted from live range construction. This includes
//! unused block parameters for loops, e.g.:
//!
//! ```text
//! block0(v0):            block1(v1):
//!     --> block1(v0)         --> block0(v1)
//! ```
//!
//! We could, alternatively, compute an overapproximation of liveness in a quick
//! single pass, overapproximating live ranges across loops, however that loss
//! of fidelity results in larger live ranges which leads to more conflicts
//! during the hottest backtracking loop during register allocation, and
//! ultimately results in slower compiles and worse codegen.

use crate::{
    Inst,
    btree::{BTreeSet, BTreeSetArena},
    counts::Counts,
    dfs::{Dfs, DfsEvent},
    entity::{
        Block, Entity as _, EntityRange, EntityRepr, EntitySet, PrimaryMap, SecondaryMap, Val,
    },
    error::IResult,
    input::{DefUse, InputBlock, InputFunction, InputInst as _, Position},
    live_ranges::{LivePoint, SpillWeight, Use, UseData},
    output::OutputInner,
    timing::Timing,
};
use alloc::vec::Vec;

pub struct Liveness<E>
where
    E: EntityRepr,
{
    /// Storage for our live sets.
    arena: BTreeSetArena<E, Val<E>>,

    /// The values live on entry to each block, not counting the block's own
    /// parameters, which are defined at exactly that point.
    live_in: SecondaryMap<Block<E>, BTreeSet<E, Val<E>>>,

    /// The values live at each block's exit: everything live on entry to any
    /// successor, plus the arguments the block passes along its outgoing edges,
    /// which its terminator uses.
    live_out: SecondaryMap<Block<E>, BTreeSet<E, Val<E>>>,

    /// Scratch holding the values live at the point currently being processed.
    live: BTreeSet<E, Val<E>>,

    /// Scratch holding the values that are live across the control-flow edge
    /// currently being processed.
    live_across_edge: BTreeSet<E, Val<E>>,

    /// The worklist of blocks that need to be (re)processed.
    worklist: Vec<Block<E>>,

    /// Whether each block is already on the worklist, so that it is never
    /// enqueued twice.
    on_worklist: EntitySet<Block<E>>,

    /// Whether we've seen a block during our initial traversal that seeds the
    /// worklist.
    seen: EntitySet<Block<E>>,

    /// Scratch for live span construction: where each currently-open span
    /// ends, exclusive.
    ///
    /// An entry is only meaningful while `live` holds its value; stale entries
    /// left behind by an earlier block are never read.
    span_end: SecondaryMap<Val<E>, Option<LivePoint<E>>>,

    /// Scratch for live span construction: the uses of values whose spans are
    /// still open, each chained to the next-later use of the same value.
    ///
    /// The walk runs backwards and pushes at the head, so a chain reads out
    /// head-to-tail in ascending program order for free. That is what lets each
    /// span's uses land contiguously in the shared uses map even though
    /// different values' uses interleave during the walk.
    pending_uses: Vec<(UseData<E>, u32)>,

    /// Scratch for live span construction: the head of each open value's chain
    /// within `pending_uses`, or [`NO_PENDING_USE`].
    ///
    /// Only meaningful while `live` holds the value.
    pending_head: SecondaryMap<Val<E>, u32>,

    /// The spans finished for the block most recently walked, waiting to be
    /// yielded by a [`BlockSpans`].
    finished: Vec<(LivePoint<E>, LivePoint<E>, Val<E>, EntityRange<Use<E>>)>,
}

/// The sentinel that terminates a chain in `Liveness::pending_uses`.
const NO_PENDING_USE: u32 = u32::MAX;

impl<E> Liveness<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        Liveness {
            arena: BTreeSetArena::new(),
            live_in: SecondaryMap::new(BTreeSet::new()),
            live_out: SecondaryMap::new(BTreeSet::new()),
            live: BTreeSet::new(),
            live_across_edge: BTreeSet::new(),
            worklist: Vec::new(),
            seen: EntitySet::new(),
            on_worklist: EntitySet::new(),
            span_end: SecondaryMap::new(None),
            pending_head: SecondaryMap::new(NO_PENDING_USE),
            pending_uses: Vec::new(),
            finished: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            arena,
            live_in,
            live_out,
            live,
            live_across_edge,
            worklist,
            seen,
            on_worklist,
            span_end,
            pending_uses,
            pending_head,
            finished,
        } = self;
        live.clear(arena);
        live_across_edge.clear(arena);
        arena.reset();
        live_in.reset();
        live_out.reset();
        worklist.clear();
        seen.reset();
        on_worklist.reset();
        span_end.reset();
        pending_uses.clear();
        pending_head.reset();
        finished.clear();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            arena,
            live_in,
            live_out,
            live,
            live_across_edge,
            worklist,
            seen,
            on_worklist,
            span_end,
            pending_uses,
            pending_head,
            finished,
        } = self;
        arena.is_reset()
            && live_in.is_reset()
            && live_out.is_reset()
            && live.is_empty()
            && live_across_edge.is_empty()
            && worklist.is_empty()
            && seen.is_reset()
            && on_worklist.is_reset()
            && span_end.is_reset()
            && pending_uses.is_empty()
            && pending_head.is_reset()
            && finished.is_empty()
    }

    /// Get the values that are live on entry to `block`.
    #[allow(dead_code, reason = "will probably need it")]
    pub fn live_in(&self, block: Block<E>) -> impl Iterator<Item = Val<E>> + '_ {
        self.live_in[block].iter(&self.arena).copied()
    }

    /// Get the values that are live at `block`'s exit.
    #[allow(dead_code, reason = "will probably need it")]
    pub fn live_out(&self, block: Block<E>) -> impl Iterator<Item = Val<E>> + '_ {
        self.live_out[block].iter(&self.arena).copied()
    }

    /// Is `val` live on entry to `block`?
    #[allow(dead_code, reason = "will probably need it")]
    pub fn is_live_in(&self, block: Block<E>, val: Val<E>) -> bool {
        self.live_in[block].contains(&self.arena, &val)
    }

    /// Is `val` live at `block`'s exit?
    #[allow(dead_code, reason = "will probably need it")]
    pub fn is_live_out(&self, block: Block<E>, val: Val<E>) -> bool {
        self.live_out[block].contains(&self.arena, &val)
    }

    /// How many values are live on entry to `block`?
    #[allow(dead_code, reason = "will probably need it")]
    pub fn len_live_in(&self, block: Block<E>) -> usize {
        self.live_in[block].len()
    }

    /// How many values are live at `block`'s exit?
    #[allow(dead_code, reason = "will probably need it")]
    pub fn len_live_out(&self, block: Block<E>) -> usize {
        self.live_out[block].len()
    }

    /// Construct this `Liveness` in place for the given function.
    pub fn construct(
        &mut self,
        func: &impl InputFunction,
        counts: &mut Counts,
        dfs: &mut Dfs<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        let _timing = Timing::new("liveness");

        self.live_in.reserve(func.len_blocks());
        self.live_out.reserve(func.len_blocks());
        self.worklist.reserve(func.len_blocks());

        self.seed_worklist(func, dfs, output)?;
        self.run_to_fixed_point(func, counts, output)?;

        if cfg!(debug_assertions) {
            // The only values that may be live on entry to the function are the
            // entry block's parameters, which are the function's parameters.
            // Anything else live here is used before it is defined.
            let entry = output.with_repr(func.entry_block())?;
            for val in self.live_in[entry].iter(&self.arena) {
                debug_assert!(
                    func.block(func.entry_block())
                        .params()
                        .any(|param| output.with_repr(param) == Ok(*val)),
                    "{val:?} is live on entry to the function, but is not one of its \
                     parameters, so it is used before it is defined",
                );
            }
        }

        Ok(())
    }

    /// Initialize the worklist with all of the function's blocks.
    ///
    /// We arrange the worklist so that blocks will be popped in post-order,
    /// which minimizes the number of fixed-point iterations we must do: because
    /// a block is not processed until all of its successors are already
    /// processed, and we are flowing backwards from successors to predecessors,
    /// we only need to process each block once (modulo loops).
    fn seed_worklist(
        &mut self,
        func: &impl InputFunction,
        dfs: &mut Dfs<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        dfs.construct(func, output)?;
        while let Some(event) = dfs.next(func, output, |block| self.seen.contains(block))? {
            match event {
                DfsEvent::Pre(block) => {
                    self.seen.insert(block);
                }
                DfsEvent::Post(block) => {
                    self.on_worklist.insert(block);
                    self.worklist.push(block);
                }
                DfsEvent::AfterEdge(..) => {}
            }
        }
        self.worklist.reverse();
        Ok(())
    }

    /// Process the worklist, running the backwards dataflow to a fixed point.
    fn run_to_fixed_point(
        &mut self,
        func: &impl InputFunction,
        counts: &mut Counts,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        let Self {
            arena,
            live_in,
            live_out,
            live,
            live_across_edge,
            worklist,
            seen,
            on_worklist,
            span_end: _,
            pending_uses: _,
            pending_head: _,
            finished: _,
        } = self;

        while let Some(block) = worklist.pop() {
            on_worklist.remove(block);
            counts.liveness_iterations += 1u64;

            // Recompute this block's live-out set from its successors.
            live_out[block].clear(arena);
            transfer_edges(
                &func.block(block.with_repr32()),
                func,
                arena,
                live_in,
                live_across_edge,
                &mut live_out[block],
                output,
            )?;

            // Walk backwards from the block's exit to its entry.
            live.clear(arena);
            live.union_with(arena, &live_out[block]);
            transfer_insts(&func.block(block.with_repr32()), arena, live, output)?;

            // If the live-out set grew, then we need to re-enqueue our
            // predecessors for processing.
            if live_in[block].union_with(arena, live) {
                for pred in func.block(block.with_repr32()).predecessors() {
                    let pred = output.with_repr(pred)?;
                    if seen.contains(pred) && !on_worklist.contains(pred) {
                        on_worklist.insert(pred);
                        worklist.push(pred);
                    }
                }
            }
        }

        live.clear(arena);
        Ok(())
    }

    /// Build the live spans of every value that is live anywhere within
    /// `block`, walking the block backwards from its exit to its entry.
    ///
    /// Each finished span's uses are appended to `uses` as the walk goes, and
    /// the `EntityRange<Use<E>>` in each yielded span indexes into that map.
    pub fn block_spans<'a>(
        &'a mut self,
        func: &impl InputFunction,
        block: Block<E>,
        uses: &mut PrimaryMap<Use<E>, UseData<E>>,
        output: &mut OutputInner<E>,
    ) -> IResult<BlockSpans<'a, E>> {
        let Self {
            arena,
            live_in: _,
            live_out,
            live,
            live_across_edge: _,
            worklist: _,
            seen: _,
            on_worklist: _,
            span_end,
            pending_uses,
            pending_head,
            finished,
        } = self;

        debug_assert!(live.is_empty());
        debug_assert!(pending_uses.is_empty());
        debug_assert!(finished.is_empty());

        let (first_inst, last_inst) = block_inst_bounds(&func.block(block.with_repr32()));
        let first_inst = output.with_repr(first_inst)?;
        let last_inst = output.with_repr(last_inst)?;

        let block_start = LivePoint::new(first_inst, Position::Early);

        // One past the block's last program point. Validation reserves an
        // instruction index above the largest that any real instruction may
        // take, so this is always representable.
        let block_end = LivePoint::new(last_inst, Position::Late).next_point();

        // Seed the walk with everything live at the block's exit. The
        // arguments this block passes along its outgoing edges are already in
        // here, courtesy of `transfer_edges`, which is why they need no `Use`
        // record of their own: their spans reach the block's end regardless.
        live.union_with(arena, &live_out[block]);
        for val in live.iter(arena) {
            span_end[*val] = Some(block_end);
            pending_head[*val] = NO_PENDING_USE;
        }

        for_each_operand_rev(
            &func.block(block.with_repr32()),
            output,
            |output, point, i, kind, val| {
                let use_data = UseData::new(point, i, SpillWeight::new(0.0));
                match kind {
                    DefUse::Def if live.remove(arena, &val) => {
                        // The value is live after this instruction, so its span
                        // starts here and runs to wherever the backwards walk last
                        // saw it.
                        let end = span_end[val].unwrap();
                        push_pending_use(pending_uses, pending_head, val, use_data);
                        let span_uses =
                            flush_pending_uses(pending_uses, pending_head, val, uses, output)?;
                        finished.push((point, end, val, span_uses));
                    }
                    DefUse::Def => {
                        // A dead def. The instruction may still have side effects,
                        // so it stays in the program, and it generally must write
                        // its result *somewhere* even though nothing reads it.
                        // Giving it a span through the end of its instruction
                        // reserves a register that nothing else may claim there.
                        let end = LivePoint::new(point.inst(), Position::Late).next_point();
                        pending_head[val] = NO_PENDING_USE;
                        push_pending_use(pending_uses, pending_head, val, use_data);
                        let span_uses =
                            flush_pending_uses(pending_uses, pending_head, val, uses, output)?;
                        finished.push((point, end, val, span_uses));
                    }
                    DefUse::Use => {
                        if live.insert(arena, val) {
                            // The first use the backwards walk has seen, so it
                            // is the last one in program order, and the span
                            // ends just after it.
                            span_end[val] = Some(point.next_point());
                            pending_head[val] = NO_PENDING_USE;
                        }
                        push_pending_use(pending_uses, pending_head, val, use_data);
                    }
                }
                Ok(())
            },
        )?;

        // Whatever is still live once the walk reaches the block's entry is
        // live-in, and its span reaches back to the first instruction. This
        // handles a live block parameter with no special case of its own: a
        // parameter is defined on the incoming edge, which is exactly the
        // block's start.
        //
        // A *dead* block parameter, on the other hand, gets no span at all,
        // unlike the dead instruction def above. A parameter is only the
        // destination of a move along an edge, and `transfer_edges` already
        // keeps an argument live only when the parameter it feeds is live-in,
        // so a dead parameter generates no move and needs no register.
        for val in live.iter(arena) {
            let end = span_end[*val].unwrap();
            let span_uses = flush_pending_uses(pending_uses, pending_head, *val, uses, output)?;
            finished.push((block_start, end, *val, span_uses));
        }
        live.clear(arena);
        pending_uses.clear();

        if cfg!(debug_assertions) {
            for (start, end, ..) in finished.iter() {
                debug_assert!(start < end, "every span must cover at least one point");
                debug_assert!(*start >= block_start);
                debug_assert!(*end <= block_end);
            }
        }

        Ok(BlockSpans {
            liveness: self,
            index: 0,
        })
    }
}

/// An iterator over the live spans of a single block, as built by
/// [`Liveness::block_spans`].
pub struct BlockSpans<'a, E>
where
    E: EntityRepr,
{
    liveness: &'a mut Liveness<E>,

    /// How many of `self.liveness.finished`'s spans have been yielded already.
    index: usize,
}

impl<E> Drop for BlockSpans<'_, E>
where
    E: EntityRepr,
{
    fn drop(&mut self) {
        // Leave the scratch empty whether or not this iterator was drained, so
        // that the next block starts clean and `Liveness::is_reset` stays
        // honest.
        self.liveness.finished.clear();
        self.liveness.pending_uses.clear();
    }
}

impl<E> Iterator for BlockSpans<'_, E>
where
    E: EntityRepr,
{
    /// A single live span, its value, and its uses: `(start, end, val, uses)`.
    type Item = (LivePoint<E>, LivePoint<E>, Val<E>, EntityRange<Use<E>>);

    fn next(&mut self) -> Option<Self::Item> {
        let span = *self.liveness.finished.get(self.index)?;
        self.index += 1;
        Some(span)
    }
}

impl<E> ExactSizeIterator for BlockSpans<'_, E>
where
    E: EntityRepr,
{
    fn len(&self) -> usize {
        self.liveness.finished.len() - self.index
    }
}

/// Push `use_data` onto the head of `val`'s chain of pending uses.
fn push_pending_use<E>(
    pending_uses: &mut Vec<(UseData<E>, u32)>,
    pending_head: &mut SecondaryMap<Val<E>, u32>,
    val: Val<E>,
    use_data: UseData<E>,
) where
    E: EntityRepr,
{
    let index = u32::try_from(pending_uses.len()).unwrap();
    debug_assert_ne!(index, NO_PENDING_USE);
    pending_uses.push((use_data, pending_head[val]));
    pending_head[val] = index;
}

/// Move `val`'s chain of pending uses into the shared `uses` map, and return
/// the contiguous range they landed in.
fn flush_pending_uses<E>(
    pending_uses: &[(UseData<E>, u32)],
    pending_head: &mut SecondaryMap<Val<E>, u32>,
    val: Val<E>,
    uses: &mut PrimaryMap<Use<E>, UseData<E>>,
    output: &mut OutputInner<E>,
) -> IResult<EntityRange<Use<E>>>
where
    E: EntityRepr,
{
    let start = uses.next_key(output)?;
    let mut index = core::mem::replace(&mut pending_head[val], NO_PENDING_USE);
    while index != NO_PENDING_USE {
        let (use_data, next) = pending_uses[usize::try_from(index).unwrap()];
        uses.push(output, use_data)?;
        index = next;
    }
    let end = uses.next_key(output)?;

    // The chain was already in ascending program order.
    debug_assert!(
        uses.as_slice()[start.index()..end.index()]
            .is_sorted_by(|a, b| (a.point(), a.operand()) < (b.point(), b.operand())),
    );

    Ok(EntityRange { start, end })
}

/// Compute `live_out` for the block that `input_block` describes, from its
/// successors' live-in sets.
fn transfer_edges<'a, E>(
    input_block: &impl InputBlock<'a>,
    func: &impl InputFunction,
    arena: &mut BTreeSetArena<E, Val<E>>,
    live_in: &SecondaryMap<Block<E>, BTreeSet<E, Val<E>>>,
    live_across_edge: &mut BTreeSet<E, Val<E>>,
    live_out: &mut BTreeSet<E, Val<E>>,
    output: &mut OutputInner<E>,
) -> IResult<()>
where
    E: EntityRepr,
{
    for (i, successor) in input_block.successors().enumerate() {
        debug_assert_eq!(
            input_block.len_successor_block_args(i),
            func.block(successor).len_params()
        );

        let s = output.with_repr(successor)?;
        live_across_edge.clear(arena);

        // Add values that are live-in to the successor.
        live_across_edge.union_with(arena, &live_in[s]);

        // Remove block parameters defined on the edge.
        for param in func.block(successor).params() {
            let param = output.with_repr(param)?;
            live_across_edge.remove(arena, &param);
        }
        live_out.union_with(arena, live_across_edge);

        // Add block arguments that flow into a live block parameter.
        let args = input_block.successor_block_args(i);
        for (arg, param) in args.zip(func.block(successor).params()) {
            let param = output.with_repr(param)?;
            if live_in[s].contains(arena, &param) {
                let arg = output.with_repr(arg)?;
                live_out.insert(arena, arg);
            }
        }
    }

    Ok(())
}

pub(crate) fn block_inst_bounds<'a>(input_block: &impl InputBlock<'a>) -> (Inst, Inst) {
    (block_first_inst(input_block), block_last_inst(input_block))
}

/// Get the first instruction in a block.
pub(crate) fn block_first_inst<'a>(input_block: &impl InputBlock<'a>) -> Inst {
    input_block
        .insts()
        .next()
        .expect("always have at least one instruction in a block: its terminator")
        .0
}

/// Get the last instruction in a block.
pub(crate) fn block_last_inst<'a>(input_block: &impl InputBlock<'a>) -> Inst {
    input_block
        .insts()
        .next_back()
        .expect("always have at least one instruction in a block: its terminator")
        .0
}

/// Visit `input_block`'s operands in reverse program order, walking from the
/// block's exit towards its entry.
///
/// The callback receives each operand's program point, its index within its
/// instruction, its kind, and its value.
///
/// This is the single definition of what a block's instructions do to the live
/// set. Both the dataflow (`transfer_insts`) and live span construction
/// (`Liveness::block_spans`) are written on top of it, so neither can drift
/// from the other.
///
/// Within an instruction, `Late` operands are visited before `Early` ones, so
/// that a value used late and defined early is seen in the order a backwards
/// walk expects. Across instructions, later instructions come first. Operands
/// sharing a slot are visited in descending index order, which is the same
/// reversal applied one level down: the liveness dataflow does not care, but it
/// keeps the uses that live span construction chains up in ascending order.
fn for_each_operand_rev<'a, E, F>(
    input_block: &impl InputBlock<'a>,
    output: &mut OutputInner<E>,
    mut f: F,
) -> IResult<()>
where
    E: EntityRepr,
    F: FnMut(&mut OutputInner<E>, LivePoint<E>, usize, DefUse, Val<E>) -> IResult<()>,
{
    for (inst, input_inst) in input_block.insts().rev() {
        let inst = output.with_repr(inst)?;
        for pos in [Position::Late, Position::Early] {
            let point = LivePoint::new(inst, pos);
            for i in (0..input_inst.operands_len()).rev() {
                let operand = input_inst.operand(i);
                if operand.pos() != pos {
                    continue;
                }
                let val = output.with_repr(operand.val())?;
                f(output, point, i, operand.kind(), val)?;
            }
        }
    }

    Ok(())
}

/// Walk `input_block`'s instructions backwards, removing defs and adding uses.
fn transfer_insts<'a, E>(
    input_block: &impl InputBlock<'a>,
    arena: &mut BTreeSetArena<E, Val<E>>,
    live: &mut BTreeSet<E, Val<E>>,
    output: &mut OutputInner<E>,
) -> IResult<()>
where
    E: EntityRepr,
{
    for_each_operand_rev(input_block, output, |_output, _point, _i, kind, val| {
        // Note that we don't need to worry about the order of adding uses
        // vs. removing defs here because the input is in SSA.
        match kind {
            DefUse::Def => {
                live.remove(arena, &val);
            }
            DefUse::Use => {
                live.insert(arena, val);
            }
        }
        Ok(())
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test::TestFunction;
    use mutatis::check::{Check, CheckResult};
    use std::{
        collections::{BTreeSet as Set, HashMap},
        format,
        string::{String, ToString},
    };

    /// Compute `func`'s liveness.
    fn analyze(func: &TestFunction) -> Result<Liveness<u32>, String> {
        let mut liveness = Liveness::<u32>::new();
        let mut counts = Counts::new();
        let mut dfs = Dfs::<u32>::new();
        let mut output = OutputInner::<u32>::new();

        assert!(liveness.is_reset());

        if liveness
            .construct(func, &mut counts, &mut dfs, &mut output)
            .is_err()
        {
            return Err(format!("`construct` failed: {:?}", output.take_error()));
        }

        // `construct` is done with the `Dfs` when it returns, and drains it.
        if !dfs.is_reset() {
            return Err("`construct` left the `Dfs` un-reset".to_string());
        }
        if liveness.is_reset() {
            return Err("`is_reset` is true after a successful `construct`".to_string());
        }

        Ok(liveness)
    }

    /// Compute each block's predecessors, from the successor edges rather than
    /// from `InputBlock::predecessors`, so that a bug in that method cannot
    /// hide itself here.
    fn predecessors(func: &TestFunction) -> HashMap<Block, Vec<Block>> {
        let mut preds: HashMap<Block, Vec<Block>> =
            func.blocks().map(|(b, _)| (b, Vec::new())).collect();
        for (block, input_block) in func.blocks() {
            for succ in input_block.successors() {
                preds.get_mut(&succ).unwrap().push(block);
            }
        }
        preds
    }

    /// Find where each value is defined.
    fn defs(func: &TestFunction) -> HashMap<Val, Block> {
        let mut defs = HashMap::new();
        for (block, input_block) in func.blocks() {
            for param in input_block.params() {
                defs.insert(param, block);
            }
            for (_inst, input_inst) in input_block.insts() {
                for operand in input_inst.operands() {
                    if operand.kind() == DefUse::Def {
                        defs.insert(operand.val(), block);
                    }
                }
            }
        }
        defs
    }

    /// Find the blocks in which each value is read by an instruction operand.
    fn real_uses(func: &TestFunction) -> HashMap<Val, Set<Block>> {
        let mut uses: HashMap<Val, Set<Block>> = HashMap::new();
        for (block, input_block) in func.blocks() {
            for (_inst, input_inst) in input_block.insts() {
                for operand in input_inst.operands() {
                    if operand.kind() == DefUse::Use {
                        uses.entry(operand.val()).or_default().insert(block);
                    }
                }
            }
        }
        uses
    }

    /// Collect one `(source block, argument, parameter)` triple per position of
    /// per control-flow edge: the argument passed there defines that parameter.
    fn feeds(func: &TestFunction) -> Vec<(Block, Val, Val)> {
        let mut feeds = Vec::new();
        for (block, input_block) in func.blocks() {
            for (i, successor) in input_block.successors().enumerate() {
                let args = input_block.successor_block_args(i);
                for (arg, param) in args.zip(func.block(successor).params()) {
                    feeds.push((block, arg, param));
                }
            }
        }
        feeds
    }

    /// Find the values that anything ever reads.
    ///
    /// An instruction operand reads its value outright. A block argument reads
    /// its value only if the parameter it defines is itself read, so this is the
    /// least set containing every operand's value and closed under feeding.
    ///
    /// No reachability is involved, which is what keeps this independent of the
    /// dataflow that `Liveness` runs: a parameter's definition dominates all of
    /// its uses, so a parameter with any use at all has one reachable from its
    /// own definition, and is therefore live on entry to its own block.
    fn needed(func: &TestFunction, feeds: &[(Block, Val, Val)]) -> Set<Val> {
        let mut needed = Set::new();
        let mut worklist = Vec::new();

        for (_block, input_block) in func.blocks() {
            for (_inst, input_inst) in input_block.insts() {
                for operand in input_inst.operands() {
                    if operand.kind() == DefUse::Use && needed.insert(operand.val()) {
                        worklist.push(operand.val());
                    }
                }
            }
        }

        while let Some(param) = worklist.pop() {
            for &(_src, arg, fed) in feeds {
                if fed == param && needed.insert(arg) {
                    worklist.push(arg);
                }
            }
        }

        needed
    }

    /// Independently compute the sets of values live on entry to and at the exit
    /// of each block, and the set of values that anything reads.
    ///
    /// This works one value at a time and searches backwards from that value's
    /// reads, rather than solving the same block-at-a-time dataflow equations
    /// that `Liveness` does. A value `v` defined in block `d` is live-in to `b`
    /// iff `b` has a path that can reach a block `u` that uses `v` and this
    /// path does not visit `d`.
    fn liveness_oracle(
        func: &TestFunction,
    ) -> (HashMap<Block, Set<Val>>, HashMap<Block, Set<Val>>, Set<Val>) {
        let preds = predecessors(func);
        let defs = defs(func);
        let real_uses = real_uses(func);
        let feeds = feeds(func);
        let needed = needed(func, &feeds);

        let mut live_in: HashMap<Block, Set<Val>> =
            func.blocks().map(|(b, _)| (b, Set::new())).collect();
        let mut live_out: HashMap<Block, Set<Val>> =
            func.blocks().map(|(b, _)| (b, Set::new())).collect();

        // The `(block, value)` pairs where the block passes the value along an
        // edge to a parameter that is read, which is what makes it a read of that
        // value by the block's terminator.
        let read_at_edge: Set<(Block, Val)> = feeds
            .iter()
            .filter(|(_src, _arg, param)| needed.contains(param))
            .map(|&(src, arg, _param)| (src, arg))
            .collect();

        for (val, _) in func.values() {
            let Some(&def_block) = defs.get(&val) else {
                continue;
            };

            // The blocks that read `val`: with an instruction operand, or by
            // passing it along an edge to a parameter that is itself read.
            let mut read_by: Set<Block> = real_uses.get(&val).cloned().unwrap_or_default();
            for &(block, _) in read_at_edge.iter().filter(|&&(_, arg)| arg == val) {
                read_by.insert(block);
            }

            // Everything that reaches a read of `val` without passing through its
            // definition.
            let mut reaches = Set::new();
            let mut worklist: Vec<Block> = read_by
                .iter()
                .copied()
                .filter(|&b| b != def_block)
                .collect();
            for &b in &worklist {
                reaches.insert(b);
            }
            while let Some(block) = worklist.pop() {
                for &pred in &preds[&block] {
                    if pred != def_block && reaches.insert(pred) {
                        worklist.push(pred);
                    }
                }
            }

            let is_param = func.block(def_block).params().any(|param| param == val);

            for (block, input_block) in func.blocks() {
                let live_into_a_successor =
                    input_block.successors().any(|succ| reaches.contains(&succ));

                let live_in_here = if block == def_block {
                    // A parameter is live on entry to its own block when that
                    // block reads it or passes it on. Coming back around to the
                    // block rebinds it, which is why `reaches` excludes the
                    // defining block and this case is separate.
                    is_param && (read_by.contains(&def_block) || live_into_a_successor)
                } else {
                    reaches.contains(&block)
                };
                if live_in_here {
                    live_in.get_mut(&block).unwrap().insert(val);
                }

                // Using `reaches` rather than the live-in sets is what keeps a
                // successor's parameters out of this block's live-out set:
                // `reaches` never holds the block that defines the value.
                if live_into_a_successor || read_at_edge.contains(&(block, val)) {
                    live_out.get_mut(&block).unwrap().insert(val);
                }
            }
        }

        (live_in, live_out, needed)
    }

    #[test]
    fn liveness_properties() -> CheckResult<TestFunction> {
        Check::new()
            .iters(10_000)
            .run(|func: &TestFunction| -> Result<(), String> {
                let entry = func.entry_block();
                let num_values = func.len_values();

                let mut liveness = analyze(func)?;
                let (expected_live_in, expected_live_out, needed) = liveness_oracle(func);

                for (block, input_block) in func.blocks() {
                    let actual_live_in: Vec<Val> = liveness.live_in(block).collect();
                    let actual_live_out: Vec<Val> = liveness.live_out(block).collect();

                    // The sets match the oracle.
                    let expected: Vec<Val> = expected_live_in[&block].iter().copied().collect();
                    if actual_live_in != expected {
                        return Err(format!(
                            "{block:?} has live-in set {actual_live_in:?} but should have \
                             {expected:?}",
                        ));
                    }
                    let expected: Vec<Val> = expected_live_out[&block].iter().copied().collect();
                    if actual_live_out != expected {
                        return Err(format!(
                            "{block:?} has live-out set {actual_live_out:?} but should have \
                             {expected:?}",
                        ));
                    }

                    // The accessors agree with each other, and the iterators
                    // are sorted and duplicate-free.
                    for (what, actual) in
                        [("live-in", &actual_live_in), ("live-out", &actual_live_out)]
                    {
                        if !actual.windows(2).all(|w| w[0] < w[1]) {
                            return Err(format!(
                                "{block:?}'s {what} set {actual:?} is not strictly increasing",
                            ));
                        }
                    }
                    if liveness.len_live_in(block) != actual_live_in.len()
                        || liveness.len_live_out(block) != actual_live_out.len()
                    {
                        return Err(format!(
                            "{block:?} reports {} live-in and {} live-out values, but its \
                             iterators yield {} and {}",
                            liveness.len_live_in(block),
                            liveness.len_live_out(block),
                            actual_live_in.len(),
                            actual_live_out.len(),
                        ));
                    }
                    for val_index in 0..num_values {
                        let val = Val::try_new(val_index).unwrap();
                        if liveness.is_live_in(block, val) != actual_live_in.contains(&val) {
                            return Err(format!(
                                "`is_live_in({block:?}, {val:?})` disagrees with `live_in`",
                            ));
                        }
                        if liveness.is_live_out(block, val) != actual_live_out.contains(&val) {
                            return Err(format!(
                                "`is_live_out({block:?}, {val:?})` disagrees with `live_out`",
                            ));
                        }
                    }

                    // Every live value is one the function defines.
                    for &val in actual_live_in.iter().chain(actual_live_out.iter()) {
                        if val.index() >= num_values {
                            return Err(format!(
                                "{val:?} is live at {block:?}, but the function only defines \
                                 {num_values} values",
                            ));
                        }
                    }

                    // A value live on entry to a block is live at the exit of
                    // every one of its predecessors -- except for the block's
                    // own parameters, which its predecessors define on the
                    // edges rather than carry across them.
                    let params: Vec<Val> = input_block.params().collect();
                    for pred in input_block.predecessors() {
                        for &val in &actual_live_in {
                            if params.contains(&val) {
                                continue;
                            }
                            if !liveness.is_live_out(pred, val) {
                                return Err(format!(
                                    "{val:?} is live-in at {block:?} but not live-out of its \
                                     predecessor {pred:?}",
                                ));
                            }
                        }
                    }

                    // The argument feeding a live parameter is live at the exit
                    // of the block that passes it.
                    for (i, successor) in input_block.successors().enumerate() {
                        let args = input_block.successor_block_args(i);
                        for (arg, param) in args.zip(func.block(successor).params()) {
                            if liveness.is_live_in(successor, param)
                                && !liveness.is_live_out(block, arg)
                            {
                                return Err(format!(
                                    "{block:?} passes {arg:?} to {successor:?}'s parameter \
                                     {param:?}, which is live-in there, but {arg:?} is not \
                                     live-out of {block:?}",
                                ));
                            }
                        }
                    }
                }

                // The only values live on entry to the function are the entry
                // block's own parameters, which are the function's
                // parameters. Anything else would be used before it is defined.
                for val in liveness.live_in(entry) {
                    if !func.block(entry).params().any(|param| param == val) {
                        return Err(format!(
                            "{val:?} is live on entry to the function, but is not one of \
                             {entry:?}'s parameters, so it is used before it is defined",
                        ));
                    }
                }

                // A value live on entry to a block is defined by a block that
                // strictly dominates it.
                let defs = defs(func);
                for (block, input_block) in func.blocks() {
                    for val in liveness.live_in(block) {
                        let def_block = defs[&val];
                        if !func.block(def_block).dominates(block) {
                            return Err(format!(
                                "{val:?} is live-in at {block:?}, but it is defined in \
                                 {def_block:?}, which does not dominate {block:?}",
                            ));
                        }
                        // Dominance may only be non-strict for one of the block's
                        // own parameters: an instruction's result cannot be live on
                        // entry to the block that computes it.
                        if def_block == block && !input_block.params().any(|param| param == val) {
                            return Err(format!(
                                "{val:?} is live-in at {block:?}, which defines it, but it \
                                 is not one of {block:?}'s parameters",
                            ));
                        }
                    }
                }

                // A value that nothing reads is live nowhere.
                for val_index in 0..num_values {
                    let val = Val::try_new(val_index).unwrap();
                    if needed.contains(&val) {
                        continue;
                    }
                    for (block, _) in func.blocks() {
                        if liveness.is_live_in(block, val) || liveness.is_live_out(block, val) {
                            return Err(format!(
                                "nothing reads {val:?}, but it is live at {block:?}",
                            ));
                        }
                    }
                }

                // Constructing twice gives the same answer.
                let again = analyze(func)?;
                for (block, _) in func.blocks() {
                    let first: Vec<Val> = liveness.live_in(block).collect();
                    let second: Vec<Val> = again.live_in(block).collect();
                    if first != second {
                        return Err(format!(
                            "constructing twice gave {block:?} the live-in sets {first:?} \
                             and {second:?}",
                        ));
                    }
                    let first: Vec<Val> = liveness.live_out(block).collect();
                    let second: Vec<Val> = again.live_out(block).collect();
                    if first != second {
                        return Err(format!(
                            "constructing twice gave {block:?} the live-out sets {first:?} \
                             and {second:?}",
                        ));
                    }
                }

                liveness.reset();
                if !liveness.is_reset() {
                    return Err("`is_reset` is false after `reset`".to_string());
                }

                Ok(())
            })
    }
}
