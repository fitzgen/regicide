//! Coalescing live spans into bundles.
//!
//! There are three ways two spans can have *affinity*, meaning that a move
//! between them is implied if they are not allocated to the same location:
//!
//! 1. a value flowing along a control-flow edge,
//! 2. a block argument feeding the parameter it is passed to, and
//! 3. a def that must reuse the register of one of its own operands.
//!
//! When a span in one bundle has affinity with a span in another bundle, we say
//! that the bundles have affinity.
//!
//! Our coalescing is *aggressive*, in the Chaitin sense: two bundles are merged
//! greedily whenever they have affinity and nothing otherwise forbids it, with
//! no lookahead, no undo (until splitting happens in the main allocation loop),
//! and no consideration as to whether the merge increases the bundle's degree
//! in the (logical, never materialized) interference graph.
//!
//! Three things prevent merging:
//!
//! 1. Two spans in different regions may never share a bundle, because a bundle
//!    is allocated within one region.
//! 2. Two spans whose uses want disjoint locations never merge, because a
//!    bundle has one location.
//! 3. And two spans that overlap may not merge, because one location cannot
//!    hold two different values at the same time.
//!
//! Being aggressive makes the result order-dependent (i.e. non-associative):
//! performing one merge can be what makes a later one illegal. For example,
//! bundle `a` can merge into `b`, `b` can merge into `c`, but `a` and `c` have
//! conflicting constraints; therefore, after merging, we end up with either
//! bundles `ab` and `c` or bundles `a` and `bc` depending on our merge
//! order. Therefore, we sort blocks such that hot blocks are visited first, so
//! that when two merges conflict we take the one that will execute most often
//! (placing the conflict's implied move into the block that is colder).
//!
//! Bundles don't cross regions because we want to get the best allocation we
//! can within a region (i.e. within a loop) and we don't want interference from
//! outside the region to pessimize that allocation inside the region. At the
//! same time, if we can avoid moves at region boundaries by allocating a value
//! to the same register inside a loop region and in its parent region outside
//! the loop, that would also be great (so long as we don't pessimize allocation
//! inside the loop region). To address this secondary goal, we propagate
//! register preference hints from child regions *up* to parent regions whenever
//! we would otherwise merge bundles. However, we never propagate hints *down*
//! from parents to children, because it is not worth pessimizing the child
//! region's allocation by bending over backwards to satisfy a hint from its
//! parent, since child regions are, as a general rule, hotter than their
//! parents. Better to accept the cross-region move, and preserve good
//! allocation within the child region, at that point.

use crate::context::ContextInner;
use crate::entity::{Block, Entity, EntityRange, EntityRepr, Region, SecondaryMap, Val};
use crate::error::IResult;
use crate::input::{
    Input, InputBlock, InputFunction, InputInst, InputValue, OperandConstraint, Position,
};
use crate::live_ranges::{LivePoint, LiveRanges, LiveSpan};
use crate::liveness::{block_first_inst, block_last_inst};
use crate::machine::Machine;
use crate::output::OutputInner;
use crate::region_tree::RegionTree;
use crate::timing::Timing;
use crate::union_find::UnionFind;
use alloc::vec::Vec;

/// Scratch state for [`coalesce`].
pub(crate) struct Coalescing<E>
where
    E: EntityRepr,
{
    /// Which spans have been merged together. Each set becomes one bundle, and
    /// the set's representative names it until that bundle exists.
    span_sets: UnionFind<LiveSpan<E>>,

    /// The storage for each set's linked list of spans in ascending program
    /// order.
    ///
    /// This allows us to put every set within this same `SecondaryMap`
    /// allocation, avoiding a per-set `Vec` allocation.
    ///
    /// TODO: Investigate if avoiding allocations with this linked list is
    /// actually faster than allocating a `Vec` (or `SmallVec`) per
    /// bundle. Maybe there is a segment-list-style hybrid solution, where each
    /// node in the linked list is actually an `EntityRange<LiveSpan<E>>`?
    next_span: SecondaryMap<LiveSpan<E>, Option<LiveSpan<E>>>,

    /// A map from the set representative to the first link in the set's linked
    /// list within `self.next_span`.
    set_head: SecondaryMap<LiveSpan<E>, Option<LiveSpan<E>>>,

    /// A map from the set representative to the last link in the set's linked
    /// list within `self.next_span`.
    ///
    /// This allows us to check whether one set's whole range is outside another
    /// set's whole range in constant time in `sets_are_disjoint`.
    set_tail: SecondaryMap<LiveSpan<E>, Option<LiveSpan<E>>>,

    /// A map from the set representative to where that set may be allocated:
    /// the merge of the constraints of every use of every span in the set.
    ///
    /// Always resolved to remove `Reuse` constraints.
    set_constraint: SecondaryMap<LiveSpan<E>, OperandConstraint>,

    /// Scratch space for a stack of regions during a traversal of the region
    /// tree.
    region_stack: Vec<Region<E>>,

    /// Scratch space for a region's blocks, sorted by priority.
    region_blocks: Vec<Block<E>>,

    /// Scratch, live only while visiting one block: the span of each value that
    /// reaches that block's exit.
    val_exit_span: SecondaryMap<Val<E>, Option<LiveSpan<E>>>,

    /// Scratch, live only while visiting one control-flow edge: the span of
    /// each value that is live at the successor block's entry.
    val_entry_span: SecondaryMap<Val<E>, Option<LiveSpan<E>>>,

    /// Affinities whose spans are in different regions.
    ///
    /// We don't merge across regions, so these are set aside and turned into
    /// register hints after every region has been processed.
    cross_region_affinities: Vec<(LiveSpan<E>, LiveSpan<E>)>,
}

impl<E> Coalescing<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        Coalescing {
            span_sets: UnionFind::new(),
            next_span: SecondaryMap::new(None),
            set_head: SecondaryMap::new(None),
            set_tail: SecondaryMap::new(None),
            set_constraint: SecondaryMap::new(OperandConstraint::Any),
            region_stack: Vec::new(),
            region_blocks: Vec::new(),
            val_exit_span: SecondaryMap::new(None),
            val_entry_span: SecondaryMap::new(None),
            cross_region_affinities: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            span_sets,
            next_span,
            set_head,
            set_tail,
            set_constraint,
            region_stack,
            region_blocks,
            val_exit_span,
            val_entry_span,
            cross_region_affinities,
        } = self;
        span_sets.reset();
        next_span.reset();
        set_head.reset();
        set_tail.reset();
        set_constraint.reset();
        val_exit_span.reset();
        val_entry_span.reset();
        debug_assert!(region_stack.is_empty());
        debug_assert!(region_blocks.is_empty());
        debug_assert!(cross_region_affinities.is_empty());
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            span_sets,
            next_span,
            set_head,
            set_tail,
            set_constraint,
            region_stack,
            region_blocks,
            val_exit_span,
            val_entry_span,
            cross_region_affinities,
        } = self;
        span_sets.is_reset()
            && next_span.is_reset()
            && set_head.is_reset()
            && set_tail.is_reset()
            && set_constraint.is_reset()
            && region_stack.is_empty()
            && region_blocks.is_empty()
            && val_exit_span.is_reset()
            && val_entry_span.is_reset()
            && cross_region_affinities.is_empty()
    }

    /// Put `span` in a set of its own.
    fn seed(
        &mut self,
        live_ranges: &LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
        span: LiveSpan<E>,
    ) {
        self.next_span[span] = None;
        self.set_head[span] = Some(span);
        self.set_tail[span] = Some(span);
        self.set_constraint[span] = live_ranges.span_constraint(input, span);
    }

    /// Do the sets represented by `ra` and `rb` hold no two spans that are live
    /// at the same time?
    ///
    /// Read-only, so a `false` answer leaves both sets exactly as they were.
    fn sets_are_disjoint(
        &self,
        live_ranges: &LiveRanges<E>,
        ra: LiveSpan<E>,
        rb: LiveSpan<E>,
    ) -> bool {
        /// Maximum number of spans to test for disjointness, after which we
        /// give up and say the span sets overlap.
        ///
        /// This is a soft limit on the number of spans a bundle can contain,
        /// and not a hard limit, because of the fast path for when the whole
        /// range of one set is fully outside the whole range of the other. This
        /// is fine, because this limit exists to prevent quadratic behavior
        /// where we do a linear check for overlap between two span sets for
        /// every span set; the wholly-non-overlapping fast path is O(1) so it
        /// still avoids the quadratic behavior.
        const MAX_MERGE_SPANS: u32 = 200;

        let (head_a, tail_a) = (self.set_head[ra].unwrap(), self.set_tail[ra].unwrap());
        let (head_b, tail_b) = (self.set_head[rb].unwrap(), self.set_tail[rb].unwrap());

        // Fast path: the whole range of one set lies outside the whole range of
        // the other.
        if !LivePoint::spans_overlap(
            live_ranges.span(head_a).start(),
            live_ranges.span(tail_a).end(),
            live_ranges.span(head_b).start(),
            live_ranges.span(tail_b).end(),
        ) {
            return true;
        }

        // Every span is initially in its own bundle set, so one side being a
        // lone span is the common, rather than corner, case. In this common
        // case, the walk to check disjointness is exactly the same walk that
        // splicing would perform anyway, so there is no quadratic behavior to
        // guard against here, and bounding the walk would cost the occasional
        // legal merge.
        let bounded = head_a != tail_a && head_b != tail_b;

        // Test whether `span_x` and `span_y` overlap, and, if not, advance
        // `next_span_{x,y}` to the next span to test for overlap.
        let check_spans_overlap_then_advance =
            |span_x: LiveSpan<_>,
             next_span_x: &mut Option<LiveSpan<_>>,
             span_y: LiveSpan<_>,
             next_span_y: &mut Option<LiveSpan<_>>| {
                let (dx, dy) = (live_ranges.span(span_x), live_ranges.span(span_y));
                if dx.overlaps(dy) {
                    return true;
                }

                // Disjoint and sorted, so whichever span ends first cannot
                // overlap with any span in the other set either.
                if dx.end() <= dy.start() {
                    *next_span_x = self.next_span[span_x];
                } else {
                    *next_span_y = self.next_span[span_y];
                }
                false
            };

        let (mut x, mut y) = (Some(head_a), Some(head_b));
        if bounded {
            let mut steps = 0;
            while let (Some(sx), Some(sy)) = (x, y) {
                steps += 1;
                if steps > MAX_MERGE_SPANS
                    || check_spans_overlap_then_advance(sx, &mut x, sy, &mut y)
                {
                    return false;
                }
            }
        } else {
            while let (Some(sx), Some(sy)) = (x, y) {
                if check_spans_overlap_then_advance(sx, &mut x, sy, &mut y) {
                    return false;
                }
            }
        }

        true
    }

    /// Try to merge `a` and `b` into the same set.
    ///
    /// Returns `true` if they were merged, `false` if they were not.
    fn try_merge(
        &mut self,
        machine: &Machine,
        live_ranges: &LiveRanges<E>,
        a: LiveSpan<E>,
        b: LiveSpan<E>,
    ) -> bool {
        // NB: this method must not mutate any state until after it is sure that
        // merging will succeed. We cannot leave half-merged state behind after
        // refusing to merge the sets!

        let a = self.span_sets.find(a);
        let b = self.span_sets.find(b);
        if a == b {
            return true;
        }

        let Some(constraint) = self.set_constraint[a].merge(
            &self.set_constraint[b],
            machine,
            |_| unreachable!("already resolved"),
            |_| unreachable!("already resolved"),
        ) else {
            return false;
        };

        if !self.sets_are_disjoint(live_ranges, a, b) {
            return false;
        }

        // Okay, nothing is stopping us from merging these sets. We can now
        // mutate state and splice the sets' lists together (keeping the result
        // sorted).

        // Get a sort comparison key for the given span.
        let compare_key = |span: LiveSpan<E>| {
            let data = live_ranges.span(span);
            (data.start(), data.end(), span)
        };

        // The head and tail of the resulting spliced list.
        let (mut head, mut tail) = (None, None);

        // The next link in `a` and `b`'s lists.
        let (mut next_a, mut next_b) = (self.set_head[a], self.set_head[b]);

        loop {
            let next = match (next_a, next_b) {
                // Done splicing.
                (None, None) => break,

                // Done with `b`, just need to append the tail of `a`.
                (Some(sx), None) => {
                    next_a = self.next_span[sx];
                    sx
                }

                // Done with `a`, just need to append the tail of `b`.
                (None, Some(sy)) => {
                    next_b = self.next_span[sy];
                    sy
                }

                // Still draining both `a` and `b`: take from whichever is less
                // than the other to keep the result sorted.
                (Some(sx), Some(sy)) => {
                    if compare_key(sx) <= compare_key(sy) {
                        next_a = self.next_span[sx];
                        sx
                    } else {
                        next_b = self.next_span[sy];
                        sy
                    }
                }
            };

            // Nothing will ever access `next_span` entries that aren't part of
            // a linked list anymore, so we don't need to actually clear them
            // out here. Leave this here to it is still type checked, just in
            // case we change things in the future in such a way that we need to
            // starting clearing entries. (The `if false` should be boiled away
            // by the compiler's optimizer.)
            if false {
                self.next_span[next] = None;
            }

            // Link `next` into the result list.
            match tail {
                None => head = Some(next),
                Some(t) => self.next_span[t] = Some(next),
            }
            tail = Some(next);
        }

        let root = self.span_sets.union(a, b);
        self.set_head[root] = head;
        self.set_tail[root] = tail;
        self.set_constraint[root] = constraint;
        true
    }
}

/// Run the coalescing pass, grouping spans into bundles.
pub(crate) fn coalesce<E>(
    context: &mut ContextInner<E>,
    input: &Input<'_, impl InputFunction>,
    output: &mut OutputInner<E>,
) -> IResult<()>
where
    E: EntityRepr,
{
    let _timing = Timing::new("coalesce");

    let ContextInner {
        counts,
        region_tree,
        live_ranges,
        coalescing,
        ..
    } = context;

    debug_assert!(coalescing.is_reset());

    // Merge spans into sets within each region.
    coalescing.region_stack.push(region_tree.root());
    while let Some(region) = coalescing.region_stack.pop() {
        coalescing.region_stack.extend(region_tree.children(region));
        coalescing.coalesce_region(region_tree, live_ranges, input, output, region)?;
    }

    // Then build our bundles from the merged span sets.
    build_bundles(coalescing, region_tree, live_ranges, counts, output)?;

    // And finally propagate hints across regions.
    hint_across_regions(coalescing, region_tree, live_ranges, input.machine);

    coalescing.cross_region_affinities.clear();
    coalescing.region_blocks.clear();
    Ok(())
}

impl<E> Coalescing<E>
where
    E: EntityRepr,
{
    /// Merge spans within a region.
    fn coalesce_region(
        &mut self,
        region_tree: &RegionTree<E>,
        live_ranges: &LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
        output: &mut OutputInner<E>,
        region: Region<E>,
    ) -> IResult<()> {
        // Seed each span into its own set.
        for block in region_tree.blocks(region) {
            for span in live_ranges.block_spans(block) {
                self.seed(live_ranges, input, span);
            }
        }

        // Temporarily take `region_blocks` out to avoid borrow issues.
        let mut region_blocks = core::mem::take(&mut self.region_blocks);

        // Coalesce spans starting from each block in the region, hottest first
        // (coalescing is order-dependent; see the module-level doc comments for
        // details).
        region_blocks_by_priority(input, region_tree, region, &mut region_blocks);
        for block in region_blocks.iter() {
            self.coalesce_block(region_tree, live_ranges, input, output, region, *block)?;
        }

        region_blocks.clear();
        debug_assert!(self.region_blocks.is_empty());
        self.region_blocks = region_blocks;

        Ok(())
    }

    /// Merge the sets joined by an affinity that starts in `block`.
    fn coalesce_block(
        &mut self,
        region_tree: &RegionTree<E>,
        live_ranges: &LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
        output: &mut OutputInner<E>,
        region: Region<E>,
        block: Block<E>,
    ) -> IResult<()> {
        let block_end = block_end_point(input, output, block)?;

        self.coalesce_reuse_operands(
            live_ranges,
            input,
            output,
            block,
            &input.func.block(block.with_repr32()),
        )?;

        // Build a map from this block's live-out values to their final spans in
        // this block.
        debug_assert_eq!(self.val_exit_span.len(), 0);
        for span in live_ranges.live_out_spans(block) {
            debug_assert_eq!(live_ranges.span(span).end(), block_end);
            self.val_exit_span[live_ranges.span(span).val()] = Some(span);
        }

        let block_data = input.func.block(block.with_repr32());
        for (i, succ) in block_data.successors().enumerate() {
            let succ_repr = output.with_repr(succ)?;
            let is_same_region = region_tree.block_region(succ_repr) == region;

            // Build a map from the successor's live-in values to their initial
            // spans in the successor.
            debug_assert_eq!(self.val_entry_span.len(), 0);
            let succ_start = block_start_point(input, output, succ_repr)?;
            for span in live_ranges.live_in_spans(succ_repr) {
                debug_assert_eq!(live_ranges.span(span).start(), succ_start);
                let val = live_ranges.span(span).val();
                // We might already have an entry in `val_entry_span` because a
                // value can be associated with multiple spans: for example, when a
                // value is used in multiple operands of the same instruction, but
                // those operands have conflicting constraints, we create a span for
                // each conflicting use, all of which are associated with the same
                // value. In this scenario, which span we put in the map (and
                // therefore attempt to coalesce with) is an arbitrary choice; we
                // take the first span we encounter and ignore others.
                //
                // TODO: investigate taking the least-constrained span, so as to
                // maximize likelihood of successful coalescing?
                if self.val_entry_span[val].is_none() {
                    self.val_entry_span[val] = Some(span);
                }
            }

            // Create affinities between the spans of a value that is both live-in
            // to the successor and live-out of this block.
            for span in live_ranges.live_in_spans(succ_repr) {
                let val = live_ranges.span(span).val();
                if self.val_entry_span[val] != Some(span) {
                    // This span's value is not live-in to the successor; ignore it.
                    continue;
                }
                let Some(out) = self.val_exit_span[val] else {
                    // This span's value is not live-out of this block; ignore it.
                    continue;
                };
                self.coalesce_affinity(live_ranges, input, is_same_region, out, span);
            }

            // Create affinities between block-call arguments in this block and
            // their associated block parameters in the successor block.
            let succ_data = input.func.block(succ);
            for (arg, param) in block_data.successor_block_args(i).zip(succ_data.params()) {
                debug_assert_eq!(
                    input.func.value(arg).reg_class(),
                    input.func.value(param).reg_class()
                );
                let arg = output.with_repr(arg)?;
                let param = output.with_repr(param)?;
                let (Some(arg_span), Some(param_span)) =
                    (self.val_exit_span[arg], self.val_entry_span[param])
                else {
                    continue;
                };
                self.coalesce_affinity(live_ranges, input, is_same_region, arg_span, param_span);
            }

            self.val_entry_span.reset();
        }

        self.val_exit_span.reset();
        Ok(())
    }

    /// Given that `a` and `b` share an affinity: try merging them if they are in
    /// the same region, or otherwise remember the cross-region affinity for
    /// hinting.
    fn coalesce_affinity(
        &mut self,
        live_ranges: &LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
        is_same_region: bool,
        a: LiveSpan<E>,
        b: LiveSpan<E>,
    ) {
        if is_same_region {
            self.try_merge(input.machine, live_ranges, a, b);
        } else {
            self.cross_region_affinities.push((a, b));
        }
    }

    /// Merge the sets of the operands tied together by a `Reuse` constraint.
    fn coalesce_reuse_operands<'a>(
        &mut self,
        live_ranges: &LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
        output: &mut OutputInner<E>,
        block: Block<E>,
        input_block: &impl InputBlock<'a>,
    ) -> IResult<()> {
        for (inst, input_inst) in input_block.insts() {
            for j in 0..input_inst.operands_len() {
                let OperandConstraint::Reuse(i) = input_inst.operand(j).constraint() else {
                    continue;
                };
                debug_assert_eq!(
                    input.func.value(input_inst.operand(j).val()).reg_class(),
                    input.func.value(input_inst.operand(i).val()).reg_class()
                );
                let inst = output.with_repr(inst)?;
                let (Some(a), Some(b)) = (
                    live_ranges.inst_operand_span(block, inst, j),
                    live_ranges.inst_operand_span(block, inst, i),
                ) else {
                    continue;
                };
                // Always within one block, so always within one region.
                self.try_merge(input.machine, live_ranges, a, b);
            }
        }
        Ok(())
    }
}

/// Sort `region`'s blocks into the order in which coalescing should consider
/// them, most important first, and place them into `region_blocks`.
///
/// Because coalescing is not associative, the resulting bundles depend on merge
/// order, so this decides which of two conflicting affinities gets its move
/// removed. We prioritize merging spans in hotter blocks first, pushing moves
/// towards colder blocks.
///
/// This is the same approach that LLVM's greedy register allocator and
/// `regalloc3` take.
fn region_blocks_by_priority<E>(
    input: &Input<'_, impl InputFunction>,
    region_tree: &RegionTree<E>,
    region: Region<E>,
    region_blocks: &mut Vec<Block<E>>,
) where
    E: EntityRepr,
{
    debug_assert!(region_blocks.is_empty());
    region_blocks.extend(region_tree.blocks(region));

    // NB: use a stable sort for determinism.
    region_blocks.sort_by(|a, b| {
        let a = a.with_repr32();
        let b = b.with_repr32();

        let (ba, bb) = (input.func.block(a), input.func.block(b));

        // Compare by highest block frequency first.
        bb.frequency()
            .cmp(&ba.frequency())
            // Then compare by critical-edge splitting blocks, whose raison
            // d'etre is holding the moves that we are trying to remove via
            // coalescing. We don't require that the embedder has already split
            // the critical edges in the input function, letting the embedder
            // lazily split them on demand by returning `Edit::CriticalEdgeMove`
            // instead, so this comparison rarely affects the blocks
            // order. However, some embedders eagerly split critical edges
            // anyways, and if we didn't have this comparison tier, then these
            // blocks would tend to be placed last in the sort order (since they
            // are decreasing the number of edges a node has by definition),
            // which is the opposite of what we want.
            .then_with(|| {
                is_critical_edge_split_block(input.func, b)
                    .cmp(&is_critical_edge_split_block(input.func, a))
            })
            // Finally, favor blocks with the most incoming and outgoing edges,
            // which have the most affinities to coalesce.
            .then_with(|| {
                (bb.len_successors() + bb.len_predecessors())
                    .cmp(&(ba.len_successors() + ba.len_predecessors()))
            })
    });
}

/// Is `block` a block that exists only to split a critical edge and hold its
/// moves?
///
/// A critical edge is an edge from a block with multiple successors, to a block
/// with multiple predecessors. In the following example, the edge `B->C` is a
/// critical edge:
///
/// ```text
/// +---+           +---+
/// | A |           | B |
/// +---+           +---+
///      \         /     \
///       \       /       \
///        \     /         \
///         +---+           +---+
///         | C |           | D |
///         +---+           +---+
/// ```
///
/// If the register allocator needs to insert a move on that edge it has nowhere
/// to place the move:
///
/// * If the move is placed at the end of `B`, then the move will execute even
///   on the `B->D` path, where it isn't needed (or, worse, might clobber
///   something `D` requires!)
///
/// * Similarly, if the move is placed at the start of `C`, then it will
///   incorrectly execute on the `A->C` path as well.
///
/// The solution is to *split* the critical edge by introducing a new block
/// between `B` and `C`:
///
/// ```text
/// +---+               +---+
/// | A |               | B |
/// +---+               +---+
///      \             /     \
///       \        +---+      \
///        \       | S |       \
///         \      +---+        \
///          \     /             \
///           +---+               +---+
///           | C |               | D |
///           +---+               +---+
/// ```
///
/// Now moves that must only execute on the `B->C` path can be placed in the new
/// `S` block that split the critical edge.
///
/// This function identifies blocks that split critical edges by interrogating
/// their predecessors and successors: a critical edge splitting block has one
/// predecessor that has multiple successors, and one successor that has
/// multiple predecessors.
fn is_critical_edge_split_block(func: &impl InputFunction, block: Block) -> bool {
    let data = func.block(block);

    // One predecessor, which has multiple successors.
    let mut preds = data.predecessors();
    if let (Some(pred), None) = (preds.next(), preds.next())
        && func.block(pred).len_successors() > 1
    {
        // And one successor, which has multiple predecessors.
        let mut succs = data.successors();
        if let (Some(succ), None) = (succs.next(), succs.next()) {
            return func.block(succ).len_predecessors() > 1;
        }
    }

    false
}

/// The program point at which `block` begins.
fn block_start_point<E>(
    input: &Input<'_, impl InputFunction>,
    output: &mut OutputInner<E>,
    block: Block<E>,
) -> IResult<LivePoint<E>>
where
    E: EntityRepr,
{
    let first = block_first_inst(&input.func.block(block.with_repr32()));
    Ok(LivePoint::new(output.with_repr(first)?, Position::Early))
}

/// One program point past the end of `block`.
fn block_end_point<E>(
    input: &Input<'_, impl InputFunction>,
    output: &mut OutputInner<E>,
    block: Block<E>,
) -> IResult<LivePoint<E>>
where
    E: EntityRepr,
{
    let last = block_last_inst(&input.func.block(block.with_repr32()));
    Ok(LivePoint::new(output.with_repr(last)?, Position::Late).next_point())
}

/// Given that we've completed span set merging, create a bundle for each set.
fn build_bundles<E>(
    coalescing: &mut Coalescing<E>,
    region_tree: &RegionTree<E>,
    live_ranges: &mut LiveRanges<E>,
    counts: &mut crate::counts::Counts,
    output: &mut OutputInner<E>,
) -> IResult<()>
where
    E: EntityRepr,
{
    coalescing.region_stack.push(region_tree.root());
    while let Some(region) = coalescing.region_stack.pop() {
        coalescing.region_stack.extend(region_tree.children(region));

        let start = live_ranges.next_bundle(output)?;

        for block in region_tree.blocks(region) {
            for span in live_ranges.block_spans(block) {
                let root = coalescing.span_sets.find(span);
                if live_ranges.span_bundle(root).is_some() {
                    continue;
                }

                let head = coalescing.set_head[root];
                let constraint = coalescing.set_constraint[root];

                let next_span = &coalescing.next_span;
                let members = core::iter::successors(head, |&s| next_span[s]);

                // Minimality and spill weights are computed later, once
                // bundles are being allocated and split.
                live_ranges.push_bundle(output, region, constraint, false, 0.0, members)?;
            }
        }

        let end = live_ranges.next_bundle(output)?;
        live_ranges.set_region_bundles(region, EntityRange { start, end });
    }

    counts.bundles += live_ranges.len_bundles();
    Ok(())
}

/// Bias each parent region's bundle towards the registers its child region's
/// bundle wants.
///
/// This is the consolation prize for an affinity that crosses a region border,
/// across which we disallow merging. The hint travels up from child to parent:
/// child regions are executed more frequently than parent regions, so we want
/// the child region to remain unconstrained, making it more likely to get the
/// allocation it wants. Additionally, we only propagate hints *after* we have
/// coalesced bundles within each region, which keeps the inter-region hinting
/// from pessimizing intra-region allocation: avoiding moves and spills within a
/// region is much more important than potentially avoiding a move across
/// regions.
fn hint_across_regions<E>(
    coalescing: &Coalescing<E>,
    region_tree: &RegionTree<E>,
    live_ranges: &mut LiveRanges<E>,
    machine: &Machine,
) where
    E: EntityRepr,
{
    for i in 0..coalescing.cross_region_affinities.len() {
        let (a, b) = coalescing.cross_region_affinities[i];
        let (Some(bundle_a), Some(bundle_b)) =
            (live_ranges.span_bundle(a), live_ranges.span_bundle(b))
        else {
            unreachable!("all spans are assigned a bundle by now")
        };

        let region_a = live_ranges.bundle(bundle_a).region();
        let region_b = live_ranges.bundle(bundle_b).region();
        debug_assert_ne!(region_a, region_b);

        let (parent, child) = if region_tree.parent(region_b) == Some(region_a) {
            (bundle_a, bundle_b)
        } else if region_tree.parent(region_a) == Some(region_b) {
            (bundle_b, bundle_a)
        } else {
            // With irreducible control flow we can get edges between sibling
            // regions. Skip the hint in this case.
            continue;
        };

        let constraint = live_ranges.bundle(child).constraint();
        live_ranges.hint_bundle(machine, parent, constraint);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::RegClass;
    use crate::context::Context;
    use crate::entity::Inst;
    use crate::live_ranges::LiveBundle;
    use crate::test::{TestFunction, TestInput};
    use mutatis::check::{Check, CheckResult};
    use std::{
        collections::HashMap,
        format,
        string::{String, ToString},
        vec::Vec,
    };

    /// Run every analysis up through coalescing.
    fn coalesce_input(test_input: &TestInput) -> Result<Context, String> {
        let mut context = Context::new();
        let mut output = OutputInner::<u32>::new();
        assert!(context.is_reset());

        let result = test_input.with_input(|input| -> IResult<()> {
            let context = &mut context.context32;
            let func = input.func;
            context.region_tree.construct(
                func,
                &mut context.counts,
                &mut context.dfs,
                &mut output,
            )?;
            context
                .liveness
                .construct(func, &mut context.counts, &mut context.dfs, &mut output)?;
            context.live_ranges.construct(
                input,
                &mut context.counts,
                &mut context.liveness,
                &mut output,
            )?;
            coalesce(context, input, &mut output)
        });
        if result.is_err() {
            return Err(format!("coalescing failed: {:?}", output.take_error()));
        }

        Ok(context)
    }

    /// The half-open program point bounds of `block`: `[start, end)`.
    ///
    /// Read straight out of the block's instruction layout, so that it can
    /// stand as an oracle rather than repeating whatever the pass computed.
    fn block_points(func: &TestFunction, block: Block) -> (LivePoint<u32>, LivePoint<u32>) {
        let input_block = func.block(block);
        let mut insts = input_block.insts();
        let first = insts.next().unwrap().0;
        let last = match insts.next_back() {
            Some((inst, _)) => inst,
            None => first,
        };
        (
            LivePoint::new(first, Position::Early),
            LivePoint::new(last, Position::Late).next_point(),
        )
    }

    /// Which block each instruction belongs to.
    fn inst_blocks(func: &TestFunction) -> HashMap<Inst, Block> {
        let mut map = HashMap::new();
        for (block, input_block) in func.blocks() {
            for (inst, _) in input_block.insts() {
                map.insert(inst, block);
            }
        }
        map
    }

    /// The span of each value that reaches `block`'s exit.
    fn exit_spans(
        live_ranges: &LiveRanges<u32>,
        func: &TestFunction,
        block: Block,
    ) -> HashMap<Val, LiveSpan> {
        let (_, end) = block_points(func, block);
        let mut map = HashMap::new();
        for span in live_ranges.block_spans(block) {
            let data = live_ranges.span(span);
            if data.end() == end {
                map.insert(data.val(), span);
            }
        }
        map
    }

    /// The span of each value that is live at `block`'s entry.
    fn entry_spans(
        live_ranges: &LiveRanges<u32>,
        func: &TestFunction,
        block: Block,
    ) -> HashMap<Val, LiveSpan> {
        let (start, _) = block_points(func, block);
        let mut map = HashMap::new();
        for span in live_ranges.block_spans(block) {
            let data = live_ranges.span(span);
            if data.start() == start {
                map.entry(data.val()).or_insert(span);
            }
        }
        map
    }

    /// The span that records `inst`'s `operand`th operand as one of its uses.
    fn operand_span(
        live_ranges: &LiveRanges<u32>,
        block: Block,
        inst: Inst,
        operand: usize,
    ) -> Option<LiveSpan> {
        live_ranges.block_spans(block).into_iter().find(|&span| {
            live_ranges
                .uses(span)
                .iter()
                .any(|u| u.point().inst() == inst && u.operand() == operand)
        })
    }

    /// Every pair of spans that coalescing should have tried to merge, derived
    /// from the function rather than from anything the pass recorded.
    fn all_affinities(
        live_ranges: &LiveRanges<u32>,
        func: &TestFunction,
    ) -> Vec<(LiveSpan, LiveSpan)> {
        let mut affinities = Vec::new();

        for (block, input_block) in func.blocks() {
            // A def that must reuse one of its own operands' registers.
            for (inst, input_inst) in input_block.insts() {
                for j in 0..input_inst.operands_len() {
                    let OperandConstraint::Reuse(i) = input_inst.operand(j).constraint() else {
                        continue;
                    };
                    if let (Some(a), Some(b)) = (
                        operand_span(live_ranges, block, inst, j),
                        operand_span(live_ranges, block, inst, i),
                    ) {
                        affinities.push((a, b));
                    }
                }
            }

            let out = exit_spans(live_ranges, func, block);
            for (i, succ) in input_block.successors().enumerate() {
                let in_ = entry_spans(live_ranges, func, succ);

                // The same value live on both sides of the edge.
                for (val, &entry) in in_.iter() {
                    if let Some(&exit) = out.get(val) {
                        affinities.push((exit, entry));
                    }
                }

                // A block argument and the parameter it feeds.
                let succ_block = func.block(succ);
                for (arg, param) in input_block.successor_block_args(i).zip(succ_block.params()) {
                    if let (Some(&exit), Some(&entry)) = (out.get(&arg), in_.get(&param)) {
                        affinities.push((exit, entry));
                    }
                }
            }
        }

        affinities
    }

    /// Do these two bundles hold spans that are live at the same time?
    fn bundles_overlap(live_ranges: &LiveRanges<u32>, a: LiveBundle, b: LiveBundle) -> bool {
        live_ranges.bundle_spans(a).any(|x| {
            let x = live_ranges.span(x);
            live_ranges.bundle_spans(b).any(|y| {
                let y = live_ranges.span(y);
                x.start() < y.end() && y.start() < x.end()
            })
        })
    }

    #[test]
    fn coalescing_properties() -> CheckResult<TestInput> {
        Check::new()
            .iters(10_000)
            .run(|test_input: &TestInput| -> Result<(), String> {
                let func = &test_input.func;
                let mut context = coalesce_input(test_input)?;
                let inner = &context.context32;
                let live_ranges = &inner.live_ranges;
                let inst_block = inst_blocks(func);

                // 1. The bundles partition the spans: every span belongs to a
                // bundle, and every bundle lists exactly the spans that point
                // back at it.
                for (span, _) in live_ranges.spans() {
                    if live_ranges.span_bundle(span).is_none() {
                        return Err(format!("{span:?} was not put in any bundle"));
                    }
                }
                let mut total = 0;
                for (bundle, _) in live_ranges.bundles() {
                    for span in live_ranges.bundle_spans(bundle) {
                        total += 1;
                        if live_ranges.span_bundle(span) != Some(bundle) {
                            return Err(format!(
                                "{bundle:?} lists {span:?}, but {span:?} points at {:?}",
                                live_ranges.span_bundle(span),
                            ));
                        }
                    }
                }
                if total != live_ranges.len_spans() {
                    return Err(format!(
                        "the bundles hold {total} spans, but there are {} in all",
                        live_ranges.len_spans(),
                    ));
                }

                // 2. A bundle's spans are in ascending program order and no two
                // of them are live at the same time -- the whole point of a
                // bundle being allocatable to one location.
                for (bundle, _) in live_ranges.bundles() {
                    let mut previous: Option<LivePoint<u32>> = None;
                    for span in live_ranges.bundle_spans(bundle) {
                        let data = live_ranges.span(span);
                        if previous.is_some_and(|previous| previous > data.start()) {
                            return Err(format!(
                                "{bundle:?} holds a span starting at {:?} after one ending at \
                                 {previous:?}",
                                data.start(),
                            ));
                        }
                        previous = Some(data.end());
                    }
                }

                // 3. Every span in a bundle lies in the bundle's region.
                for (bundle, data) in live_ranges.bundles() {
                    for span in live_ranges.bundle_spans(bundle) {
                        let block = inst_block[&live_ranges.span(span).start().inst()];
                        let block = Block::try_new(block.index()).unwrap();
                        let region = inner.region_tree.block_region(block);
                        if region != data.region() {
                            return Err(format!(
                                "{bundle:?} is in {:?}, but holds {span:?}, which is in {region:?}",
                                data.region(),
                            ));
                        }
                    }
                }

                // 4. A bundle's constraint is the merge of its spans' resolved
                // use constraints, and so is never a `Reuse`.
                test_input.with_input(|input| -> Result<(), String> {
                    for (bundle, data) in live_ranges.bundles() {
                        if matches!(data.constraint(), OperandConstraint::Reuse(_)) {
                            return Err(format!("{bundle:?}'s constraint is unresolved"));
                        }
                        let mut expected = OperandConstraint::Any;
                        for span in live_ranges.bundle_spans(bundle) {
                            let span = live_ranges.span_constraint(input, span);
                            expected = expected
                                .merge(&span, input.machine, |_| unreachable!(), |_| unreachable!())
                                .ok_or_else(|| {
                                    format!("{bundle:?}'s spans have conflicting constraints")
                                })?;
                        }
                        if expected != data.constraint() {
                            return Err(format!(
                                "{bundle:?}'s constraint is {:?}, but its spans want {expected:?}",
                                data.constraint(),
                            ));
                        }
                    }
                    Ok(())
                })?;

                // 5. The bundles' span lists tile their shared storage: no
                // gaps, no overlap, nothing left over.
                let mut next = 0;
                for (bundle, data) in live_ranges.bundles() {
                    let spans = data.spans();
                    if spans.start.index() != next {
                        return Err(format!(
                            "{bundle:?}'s spans start at {}, but the bundle before it ended at \
                             {next}",
                            spans.start.index(),
                        ));
                    }
                    if spans.is_empty() {
                        return Err(format!("{bundle:?} holds no spans"));
                    }
                    next = spans.end.index();
                }
                if next != live_ranges.len_spans() {
                    return Err(format!(
                        "the bundles' span lists end at {next}, but hold {} spans",
                        live_ranges.len_spans(),
                    ));
                }

                // 6. Each region's recorded bundle range holds exactly the
                // bundles in that region, and the ranges tile the bundle
                // arena.
                let mut counted = 0;
                let mut regions = Vec::from([inner.region_tree.root()]);
                while let Some(region) = regions.pop() {
                    regions.extend(inner.region_tree.children(region));
                    for bundle in live_ranges.region_bundles(region) {
                        counted += 1;
                        let actual = live_ranges.bundle(bundle).region();
                        if actual != region {
                            return Err(format!(
                                "{region:?} lists {bundle:?} among its bundles, but that \
                                 bundle is in {actual:?}",
                            ));
                        }
                    }
                }
                if counted != live_ranges.len_bundles() {
                    return Err(format!(
                        "the regions' bundle ranges hold {counted} bundles, but there are \
                         {} in all",
                        live_ranges.len_bundles(),
                    ));
                }

                // 7. Coalescing did its job: for every affinity, either the
                // two spans share a bundle or there is a reason they cannot.
                // Aggressive coalescing is order-dependent, so "an earlier
                // merge made this one illegal" is one of those reasons -- but it
                // is only legitimate if it still shows up as a conflict now,
                // since bundles only ever grow.
                test_input.with_input(|input| -> Result<(), String> {
                    for (a, b) in all_affinities(live_ranges, func) {
                        let (Some(ba), Some(bb)) =
                            (live_ranges.span_bundle(a), live_ranges.span_bundle(b))
                        else {
                            return Err("an affinity's span has no bundle".to_string());
                        };
                        if ba == bb {
                            continue;
                        }
                        let (da, db) = (live_ranges.bundle(ba), live_ranges.bundle(bb));
                        if da.region() != db.region() {
                            continue;
                        }
                        if da
                            .constraint()
                            .merge(
                                &db.constraint(),
                                input.machine,
                                |_| unreachable!(),
                                |_| unreachable!(),
                            )
                            .is_none()
                        {
                            continue;
                        }
                        if bundles_overlap(live_ranges, ba, bb) {
                            continue;
                        }
                        return Err(format!(
                            "{a:?} and {b:?} have an affinity and nothing forbids merging \
                             {ba:?} and {bb:?}, but they are in different bundles",
                        ));
                    }
                    Ok(())
                })?;

                // 8. A register hint never widens what a bundle may be
                // allocated to, and only a cross-region affinity can put one
                // there in the first place.
                let cross_region: Vec<(LiveBundle, LiveBundle)> = test_input.with_input(|input| {
                    all_affinities(live_ranges, func)
                        .into_iter()
                        .filter_map(|(a, b)| {
                            let (ba, bb) = (
                                live_ranges.span_bundle(a).unwrap(),
                                live_ranges.span_bundle(b).unwrap(),
                            );
                            let (ra, rb) = (
                                live_ranges.bundle(ba).region(),
                                live_ranges.bundle(bb).region(),
                            );
                            let _ = input;
                            if inner.region_tree.parent(rb) == Some(ra) {
                                Some((ba, bb))
                            } else if inner.region_tree.parent(ra) == Some(rb) {
                                Some((bb, ba))
                            } else {
                                None
                            }
                        })
                        .collect()
                });
                test_input.with_input(|input| -> Result<(), String> {
                    for (bundle, data) in live_ranges.bundles() {
                        if data.preference().is_empty() {
                            continue;
                        }
                        if let OperandConstraint::Reg(class) = data.constraint() {
                            let members = &input.machine.classes[class].member_set;
                            if !data.preference().is_subset_of(members) {
                                return Err(format!(
                                    "{bundle:?} prefers registers outside its own class",
                                ));
                            }
                        }
                        if !cross_region.iter().any(|&(parent, _)| parent == bundle) {
                            return Err(format!(
                                "{bundle:?} has a register hint but no cross-region affinity \
                                 that could have given it one",
                            ));
                        }
                    }
                    Ok(())
                })?;

                // 9. Every span belongs to exactly one block's span list, and
                // lies inside that block's program points.
                let mut seen = 0;
                for (block, _) in func.blocks() {
                    let block_e = Block::try_new(block.index()).unwrap();
                    let (start, end) = block_points(func, block);
                    for span in live_ranges.block_spans(block_e) {
                        seen += 1;
                        let data = live_ranges.span(span);
                        if data.start() < start || data.end() > end {
                            return Err(format!(
                                "{span:?} is listed under {block:?}, but covers {:?}..{:?}, \
                                 outside {start:?}..{end:?}",
                                data.start(),
                                data.end(),
                            ));
                        }
                    }
                }
                if seen != live_ranges.len_spans() {
                    return Err(format!(
                        "the blocks' span lists hold {seen} spans, but there are {} in all",
                        live_ranges.len_spans(),
                    ));
                }

                // 10. Coalescing twice gives exactly the same bundles.
                let again = coalesce_input(test_input)?;
                let again = &again.context32.live_ranges;
                if again.len_bundles() != live_ranges.len_bundles() {
                    return Err("coalescing twice gave a different number of bundles".to_string());
                }
                for index in 0..live_ranges.len_bundles() {
                    let bundle = LiveBundle::try_new(index).unwrap();
                    let (first, second) = (live_ranges.bundle(bundle), again.bundle(bundle));
                    if first.region() != second.region()
                        || first.constraint() != second.constraint()
                        || first.preference() != second.preference()
                        || live_ranges
                            .bundle_spans(bundle)
                            .ne(again.bundle_spans(bundle))
                    {
                        return Err(format!(
                            "coalescing twice gave {bundle:?} different contents"
                        ));
                    }
                }

                // 11. Everything the pass touched resets cleanly.
                context.reset();
                if !context.is_reset() {
                    return Err("`Context::is_reset` is false after `reset`".to_string());
                }

                Ok(())
            })
    }

    /// The span of `val` in `block`, of which these hand-built functions only
    /// ever have one.
    fn only_span(live_ranges: &LiveRanges<u32>, block: usize, val: usize) -> LiveSpan {
        let block = Block::try_new(block).unwrap();
        let val = Val::try_new(val).unwrap();
        let mut found = live_ranges
            .block_spans(block)
            .into_iter()
            .filter(|&span| live_ranges.span(span).val() == val);
        let span = found.next().expect("the value has a span in the block");
        assert!(found.next().is_none(), "and only the one");
        span
    }

    /// The affinity a block argument makes with the parameter it feeds is the
    /// one coalescing exists to take.
    #[test]
    fn a_block_argument_is_coalesced_with_its_parameter() {
        let input =
            TestInput::with_block_arg_constraints(OperandConstraint::Any, OperandConstraint::Any);
        let context = coalesce_input(&input).unwrap();
        let live_ranges = &context.context32.live_ranges;

        let arg = only_span(live_ranges, 0, 0);
        let param = only_span(live_ranges, 1, 1);
        assert_eq!(
            live_ranges.span_bundle(arg),
            live_ranges.span_bundle(param),
            "the argument and the parameter should share a bundle",
        );
    }

    /// ... but not when the two ends want registers that no single register
    /// satisfies.
    #[test]
    fn a_block_argument_with_a_conflicting_parameter_is_not_coalesced() {
        let rc = |i| OperandConstraint::Reg(RegClass::try_new(i).unwrap());
        let input = TestInput::with_block_arg_constraints(rc(0), rc(1));
        let context = coalesce_input(&input).unwrap();
        let live_ranges = &context.context32.live_ranges;

        let arg = only_span(live_ranges, 0, 0);
        let param = only_span(live_ranges, 1, 1);
        let arg_bundle = live_ranges.span_bundle(arg).unwrap();
        assert_eq!(live_ranges.bundle(arg_bundle).constraint(), rc(0));
        assert_ne!(
            live_ranges.span_bundle(arg),
            live_ranges.span_bundle(param),
            "`rc0` and `rc1` are disjoint, so these may not share a location",
        );
    }
}
