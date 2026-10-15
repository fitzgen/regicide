//! Coalescing live spans into bundles.
//!
//! Merging spans into bundles is generally optional, and only exists to
//! optimistically try and allocate the same register across a number of related
//! spans, which is good for both code quality (less spills and moves) and
//! compile time (processes N spans all at once, instead of processing each of
//! them individually). However, there is one exception: two uses tied together
//! by a `Reuse` constraint **must** be in the same bundle because they must be
//! allocated to the same register. In this scenario, each use is of a different
//! value (because `Reuse` must define a new value) and therefore each use has a
//! different span -- these spans **must** be coalesced together (and, later on,
//! must never be split from each other).
//!
//! There are four ways two spans can have *affinity*, meaning that a move
//! between them is implied if they are not allocated to the same location:
//!
//! 1. a value flowing along a control-flow edge (live-out of a predecessor and
//!    live-in to a successor),
//!
//! 2. a block-call argument flowing into a block parameter,
//!
//! 3. a def that must reuse the register of one of its own operands, and
//!
//! 4. the pieces on either side of an overwrite split, which hold the same
//!    value across the definition that overwrites the copy between them.
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
//! Four things prevent merging:
//!
//! 1. Two spans in different regions may never share a bundle, because a bundle
//!    is allocated within one region.
//!
//! 2. Two spans whose uses want disjoint locations never merge, because a
//!    bundle has one location.
//!
//! 3. Two spans that overlap may not merge, because one location cannot hold
//!    two different values at the same time.
//!
//! 4. And two spans joined by an affinity across a control-flow edge with a
//!    cold block on either end never merge, because the move merging would
//!    remove hardly ever executes, while the merged bundle would be bigger and
//!    more constrained everywhere else, including on hot paths.
//!
//! Being aggressive makes the result order-dependent (i.e. non-associative):
//! performing one merge can be what makes a later one illegal. For example,
//! bundle `a` can merge into `b`, `b` can merge into `c`, but `a` and `c` have
//! conflicting constraints; therefore, after merging, we end up with either
//! bundles `ab` and `c` or bundles `a` and `bc` depending on our merge
//! order. Therefore, we sort blocks such that hot blocks are visited first, so
//! that when two merges conflict we take the one that will execute most often
//! (placing the conflict's implied move into the block that is colder). Rule 4
//! above is the same instinct taken to its conclusion: where that ordering
//! picks which of two moves to keep, rule 4 declines to spend anything at all
//! on a move that nobody pays for.
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

use crate::RegSet;
use crate::context::ContextInner;
use crate::entity::{Block, Entity, EntityRange, EntityRepr, Region, SecondaryMap, Val};
use crate::error::IResult;
use crate::events::{Affinity, EventsLog, RefusedReason};
use crate::input::{
    Input, InputBlock, InputFunction, InputInst, InputValue, OperandConstraint, Position,
};
use crate::interval_sets::{Fuel, IntervalSet, IntervalSetArena, Refused};
use crate::live_ranges::{HintStrength, LivePoint, LiveRanges, LiveSpan, Reservation};
use crate::liveness::{block_first_inst, block_last_inst};
use crate::machine::{Machine, RegClassMembers};
use crate::output::{OutputInner, RegAllocation};
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

    /// The disjoint-interval set for each set representative.
    ///
    /// Only meaningful for set representatives.
    interval_set: SecondaryMap<LiveSpan<E>, Option<IntervalSet<LiveSpan<E>>>>,

    /// Storage for the disjoint-interval sets.
    interval_set_arena: IntervalSetArena<LiveSpan<E>, LivePoint<E>>,

    /// Fuel for checking span overlap within this region.
    overlap_fuel: RegionFuel,

    /// The number of out-of-fuel merge refusals we have seen thus far, to be
    /// added to `Counts` later.
    out_of_fuel: u64,

    /// A map from the set representative to where that set may be allocated:
    /// the merge of the constraints of every use of every span in the set.
    ///
    /// Always resolved to remove `Reuse` constraints.
    set_constraint: SecondaryMap<LiveSpan<E>, OperandConstraint>,

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
    /// register hints. Region allocation reads them back as it goes: it visits
    /// children before parents, so by the time a parent region is allocated,
    /// the child on the far side of the border already holds a register, and
    /// the hint can name *that* register rather than the whole class.
    pub(crate) cross_region_affinities: Vec<(LiveSpan<E>, LiveSpan<E>)>,

    /// Scratch space holding one block's reservations in
    /// `hint_reserved_registers`.
    hint_scratch: Vec<(LivePoint<E>, Val<E>, Reservation<E>)>,
}

impl<E> Coalescing<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        Coalescing {
            span_sets: UnionFind::new(),
            interval_set_arena: IntervalSetArena::new(),
            interval_set: SecondaryMap::new(None),
            overlap_fuel: RegionFuel::EMPTY,
            out_of_fuel: 0,
            set_constraint: SecondaryMap::new(OperandConstraint::Any),
            region_blocks: Vec::new(),
            val_exit_span: SecondaryMap::new(None),
            val_entry_span: SecondaryMap::new(None),
            cross_region_affinities: Vec::new(),
            hint_scratch: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            span_sets,
            interval_set_arena: sets,
            interval_set: set_of_root,
            overlap_fuel: fuel,
            out_of_fuel,
            set_constraint,
            region_blocks,
            val_exit_span,
            val_entry_span,
            cross_region_affinities,
            hint_scratch,
        } = self;
        span_sets.reset();
        sets.reset();
        set_of_root.reset();
        *fuel = RegionFuel::EMPTY;
        *out_of_fuel = 0;
        set_constraint.reset();
        val_exit_span.reset();
        val_entry_span.reset();
        region_blocks.clear();
        cross_region_affinities.clear();
        hint_scratch.clear();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            span_sets,
            interval_set_arena: sets,
            interval_set: set_of_root,
            overlap_fuel: fuel,
            out_of_fuel,
            set_constraint,
            region_blocks,
            val_exit_span,
            val_entry_span,
            cross_region_affinities,
            hint_scratch,
        } = self;
        span_sets.is_reset()
            && sets.is_reset()
            && set_of_root.is_reset()
            && *fuel == RegionFuel::EMPTY
            && *out_of_fuel == 0
            && set_constraint.is_reset()
            && region_blocks.is_empty()
            && val_exit_span.is_reset()
            && val_entry_span.is_reset()
            && cross_region_affinities.is_empty()
            && hint_scratch.is_empty()
    }

    /// Put `span` in a set of its own.
    fn seed(
        &mut self,
        live_ranges: &LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
        span: LiveSpan<E>,
    ) {
        let set = IntervalSet::singleton(
            &mut self.interval_set_arena,
            span,
            span.start(live_ranges),
            span.end(live_ranges),
        );
        self.interval_set[span] = Some(set);
        self.set_constraint[span] = span.constraint(live_ranges, input);
    }

    /// Cross-checks `try_union`. `None` if too many pairs.
    fn overlap_by_brute_force(
        &self,
        live_ranges: &LiveRanges<E>,
        a: IntervalSet<LiveSpan<E>>,
        b: IntervalSet<LiveSpan<E>>,
    ) -> Option<bool> {
        const MAX_PAIRS: usize = 4096;
        let len = |set: IntervalSet<_>| {
            set.iter(&self.interval_set_arena)
                .take(MAX_PAIRS + 1)
                .count()
        };
        let (len_a, len_b) = (len(a), len(b));
        if len_a.saturating_mul(len_b) > MAX_PAIRS {
            return None;
        }
        Some(a.iter(&self.interval_set_arena).any(|x| {
            b.iter(&self.interval_set_arena)
                .any(|y| x.overlaps(live_ranges, y))
        }))
    }

    /// Try to merge `a` and `b` into the same set.
    ///
    /// Returns `true` if they were merged, `false` if they were not.
    fn try_merge(
        &mut self,
        machine: &Machine,
        live_ranges: &LiveRanges<E>,
        events: &mut EventsLog<E>,
        affinity: Affinity,
        span_a: LiveSpan<E>,
        span_b: LiveSpan<E>,
    ) -> bool {
        // NB: this method must not mutate any state until after it is sure that
        // merging will succeed. We cannot leave half-merged state behind after
        // refusing to merge the sets! `try_union` is all-or-nothing.

        let a = self.span_sets.find(span_a);
        let b = self.span_sets.find(span_b);
        if a == b {
            return true;
        }

        let Some(constraint) =
            self.set_constraint[a].merge_resolved(&self.set_constraint[b], machine)
        else {
            event!(
                events,
                CoalesceRefused {
                    a: span_a,
                    b: span_b,
                    affinity,
                    reason: RefusedReason::ConstraintConflict,
                }
            );
            return false;
        };

        // A reuse tie must merge, so it is never refused for cost.
        let mandatory = affinity == Affinity::ReuseOperand;
        let limit = match mandatory {
            true => u64::MAX,
            false => self.overlap_fuel.allowance(),
        };
        let (set_a, set_b) = (self.interval_set[a].unwrap(), self.interval_set[b].unwrap());
        let mut fuel = Fuel::new(limit);
        let result = set_a.try_union(&mut self.interval_set_arena, set_b, &mut fuel);
        self.overlap_fuel
            .charge(fuel.spent(), result.is_err() && !mandatory);
        let set = match result {
            Ok(set) => set,
            Err(refused) => {
                debug_assert!(
                    refused != Refused::Overlap
                        || self.overlap_by_brute_force(live_ranges, set_a, set_b) != Some(false),
                    "refused {a:?} and {b:?} as overlapping, but they are disjoint",
                );
                let reason = match refused {
                    Refused::Overlap => RefusedReason::Overlap,
                    Refused::OutOfFuel => {
                        self.out_of_fuel += 1;
                        RefusedReason::OutOfFuel
                    }
                };
                event!(
                    events,
                    CoalesceRefused {
                        a: span_a,
                        b: span_b,
                        affinity,
                        reason,
                    }
                );
                return false;
            }
        };

        let root = self.span_sets.union(a, b);
        self.interval_set[root] = Some(set);
        self.set_constraint[root] = constraint;
        event!(
            events,
            SpansCoalesced {
                a: span_a,
                b: span_b,
                affinity,
            }
        );
        true
    }
}

/// One region's overlap-check budget.
///
/// Merges bound their own work, so only optional refusals charge `budget`;
/// `safety_net` charges everything.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RegionFuel {
    budget: u64,
    safety_net: u64,
}

impl RegionFuel {
    const PER_SPAN: u64 = 32;
    const BASE: u64 = 1024;
    const FLOOR: u64 = 64;

    const EMPTY: Self = RegionFuel {
        budget: 0,
        safety_net: 0,
    };

    fn new(num_spans: usize) -> Self {
        RegionFuel {
            budget: Self::PER_SPAN * num_spans as u64 + Self::BASE,
            safety_net: Fuel::safety_net(num_spans),
        }
    }

    fn allowance(&self) -> u64 {
        self.budget.max(Self::FLOOR).min(self.safety_net)
    }

    fn charge(&mut self, spent: u64, wasted: bool) {
        debug_assert!(
            !wasted || spent < self.safety_net,
            "the coalescing safety net ran out, which no realistic input should do",
        );
        self.safety_net = self.safety_net.saturating_sub(spent);
        if wasted {
            self.budget = self.budget.saturating_sub(spent);
        }
    }
}

/// Run the coalescing pass, grouping spans into bundles.
pub(crate) fn coalesce<E>(
    context: &mut ContextInner<E>,
    input: &Input<'_, impl InputFunction>,
) -> IResult<()>
where
    E: EntityRepr,
{
    let _timing = Timing::new("coalesce");

    debug_assert!(context.coalescing.is_reset());

    // Merge spans into sets within each region.
    for region in context.region_tree.pre_order_iter() {
        context.coalescing.coalesce_region(
            &context.region_tree,
            &context.live_ranges,
            input,
            &mut context.events,
            &mut context.output,
            region,
        )?;
    }

    context.counts.coalesce_out_of_fuel += core::mem::take(&mut context.coalescing.out_of_fuel);

    // Then build our bundles from the merged span sets.
    build_bundles(
        &mut context.coalescing,
        &context.region_tree,
        &mut context.live_ranges,
        &mut context.counts,
        &mut context.events,
        input,
        &mut context.output,
    )?;

    // Cross-region hints are *not* propagated here. They are propagated by
    // region allocation, which visits children before parents and so knows
    // which register the child actually got; see
    // `RegionAllocation::hint_across_regions`. Hinting here could only name
    // the child's constraint, which is almost always its whole register class
    // and so constrains nothing.

    // And finally bias each reserved value's bundle towards its register.
    for region in context.region_tree.pre_order_iter() {
        for block in region.blocks(&context.region_tree) {
            let reservations = block.reservations(&context.live_ranges);
            if reservations.is_empty() {
                continue;
            }
            hint_reserved_registers(
                input,
                &mut context.live_ranges,
                &mut context.events,
                &mut context.coalescing.hint_scratch,
                block,
                reservations,
            );
        }
    }

    // `cross_region_affinities` deliberately survives this pass: region
    // allocation consumes it and clears it.
    debug_assert!(
        context.coalescing.region_blocks.is_empty() && context.coalescing.hint_scratch.is_empty(),
        "a completed coalescing leaves no scratch behind",
    );
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
        events: &mut EventsLog<E>,
        output: &mut OutputInner<E>,
        region: Region<E>,
    ) -> IResult<()> {
        // Seed each span into its own set.
        let mut num_spans = 0;
        for block in region.blocks(&region_tree) {
            for span in block.spans(live_ranges) {
                self.seed(live_ranges, input, span);
                num_spans += 1;
            }
        }
        self.overlap_fuel = RegionFuel::new(num_spans);

        // Temporarily take `region_blocks` out to avoid borrow issues.
        let mut region_blocks = core::mem::take(&mut self.region_blocks);

        // Coalesce spans starting from each block in the region, hottest first
        // (coalescing is order-dependent; see the module-level doc comments for
        // details).
        region_blocks_by_priority(input, region_tree, region, &mut region_blocks);
        for block in region_blocks.iter() {
            self.coalesce_block(
                region_tree,
                live_ranges,
                input,
                events,
                output,
                region,
                *block,
            )?;
        }

        region_blocks.clear();
        debug_assert!(self.region_blocks.is_empty());
        self.region_blocks = region_blocks;
        self.overlap_fuel = RegionFuel::EMPTY;

        Ok(())
    }

    /// Merge the sets joined by an affinity that starts in `block`.
    fn coalesce_block(
        &mut self,
        region_tree: &RegionTree<E>,
        live_ranges: &LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
        events: &mut EventsLog<E>,
        output: &mut OutputInner<E>,
        region: Region<E>,
        block: Block<E>,
    ) -> IResult<()> {
        let block_end = block_end_point(input, output, block)?;

        self.coalesce_reuse_operands(
            live_ranges,
            input,
            events,
            output,
            block,
            &input.func.block(block.with_repr32()),
        )?;

        // Build a map from this block's live-out values to their final spans in
        // this block.
        debug_assert_eq!(self.val_exit_span.len(), 0);
        for span in block.live_out_spans(live_ranges) {
            debug_assert_eq!(span.end(live_ranges), block_end);
            self.val_exit_span[span.val(live_ranges)] = Some(span);
        }

        let block_data = input.func.block(block.with_repr32());
        let block_is_cold = block_data.frequency().is_cold();
        for (i, succ) in block_data.successors().enumerate() {
            let succ_repr = output.with_repr(succ)?;
            let is_same_region = succ_repr.region(&region_tree) == region;
            let succ_data = input.func.block(succ);
            let edge_is_cold = block_is_cold || succ_data.frequency().is_cold();

            // Build a map from the successor's live-in values to their initial
            // spans in the successor.
            debug_assert_eq!(self.val_entry_span.len(), 0);
            let succ_start = block_start_point(input, output, succ_repr)?;
            for span in succ_repr.live_in_spans(live_ranges) {
                debug_assert_eq!(span.start(live_ranges), succ_start);
                let val = span.val(live_ranges);
                // A value can be live-in in several places at once, e.g. due to
                // conflicting uses at the first instruction, or a tie there, so
                // take the entry span that reaches furthest, which gives us the
                // most bang for our buck.
                match self.val_entry_span[val] {
                    Some(prev) if prev.end(live_ranges) >= span.end(live_ranges) => {}
                    _ => self.val_entry_span[val] = Some(span),
                }
            }

            // Create affinities between the spans of a value that is both live-in
            // to the successor and live-out of this block.
            for span in succ_repr.live_in_spans(live_ranges) {
                let val = span.val(live_ranges);
                if self.val_entry_span[val] != Some(span) {
                    // This span's value is not live-in to the successor; ignore it.
                    continue;
                }
                let Some(out) = self.val_exit_span[val] else {
                    // This span's value is not live-out of this block; ignore it.
                    continue;
                };
                self.coalesce_affinity(
                    live_ranges,
                    input,
                    events,
                    Affinity::CrossEdge,
                    is_same_region,
                    edge_is_cold,
                    out,
                    span,
                );
            }

            // Create affinities between block-call arguments in this block and
            // their associated block parameters in the successor block.
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
                self.coalesce_affinity(
                    live_ranges,
                    input,
                    events,
                    Affinity::BlockCallArg,
                    is_same_region,
                    edge_is_cold,
                    arg_span,
                    param_span,
                );
            }

            self.val_entry_span.reset();
        }

        self.val_exit_span.reset();
        Ok(())
    }

    /// Given that `a` and `b` share an affinity across a control-flow edge: try
    /// merging them if they are in the same region and the edge is not cold, or
    /// otherwise remember the cross-region affinity for hinting.
    fn coalesce_affinity(
        &mut self,
        live_ranges: &LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
        events: &mut EventsLog<E>,
        affinity: Affinity,
        is_same_region: bool,
        edge_is_cold: bool,
        a: LiveSpan<E>,
        b: LiveSpan<E>,
    ) {
        if !is_same_region {
            self.cross_region_affinities.push((a, b));
            event!(events, CrossRegionAffinity { a, b });
        } else if !edge_is_cold {
            self.try_merge(input.machine, live_ranges, events, affinity, a, b);
        }
    }

    /// Merge the sets of the operands tied together by a `Reuse` constraint,
    /// and those of the pieces on either side of every split construction made
    /// around a definition overwriting the register behind a read.
    fn coalesce_reuse_operands<'a>(
        &mut self,
        live_ranges: &LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
        events: &mut EventsLog<E>,
        output: &mut OutputInner<E>,
        block: Block<E>,
        input_block: &impl InputBlock<'a>,
    ) -> IResult<()> {
        for (inst, input_inst) in input_block.insts() {
            for j in 0..input_inst.operands_len() {
                let OperandConstraint::Reuse(i) = input_inst.operand(j).constraint() else {
                    continue;
                };
                let target = input_inst.operand(i);

                let target_val = target.val().unwrap();
                debug_assert_eq!(
                    input
                        .func
                        .value(input_inst.operand(j).val().unwrap())
                        .reg_class(),
                    input.func.value(target_val).reg_class()
                );

                let target_val = output.with_repr(target_val)?;
                let inst = output.with_repr(inst)?;
                let (Some(a), Some(b)) = (
                    inst.operand_span(live_ranges, block, j),
                    inst.operand_span(live_ranges, block, i),
                ) else {
                    continue;
                };
                let merged = self.try_merge(
                    input.machine,
                    live_ranges,
                    events,
                    Affinity::ReuseOperand,
                    a,
                    b,
                );
                debug_assert!(
                    merged
                        || crate::live_ranges::fixed_operand_of(
                            input.func,
                            input.machine,
                            inst.with_repr32(),
                            i
                        )
                        .is_some(),
                    "operand {j} of {inst:?} reuses operand {i}, but their spans \
                     ({a:?} and {b:?}) could not be coalesced into one bundle"
                );

                debug_assert_eq!(target.pos(), Position::Early);
                self.coalesce_across_overwrite_split(
                    live_ranges,
                    input,
                    events,
                    block,
                    target_val,
                    LivePoint::new(inst, Position::Early),
                );
            }
        }
        Ok(())
    }

    /// Merge the pieces on either side of an overwrite split at `at`.
    ///
    /// Of the three pieces `push_span_and_split_conflicts` makes, only the
    /// middle one (the doomed copy that the definition overwrites)
    /// fundamentally requires a copy, so coalescing the other two parts into
    /// one bundle can avoid an additional, unnecessary copy.
    ///
    /// Always within one block, so always within one region.
    fn coalesce_across_overwrite_split(
        &mut self,
        live_ranges: &LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
        events: &mut EventsLog<E>,
        block: Block<E>,
        val: Val<E>,
        at: LivePoint<E>,
    ) {
        // `head` ends where the tied instruction begins. There is none here
        // when `val` arrives live-in and the tie is at the first instruction:
        // that piece is empty, and construction pushes nothing for it. Joining
        // `head` to `tail` across the edge is then `coalesce_block`'s job.
        let Some(head) = block
            .spans(live_ranges)
            .into_iter()
            .find(|span| span.val(live_ranges) == val && span.end(live_ranges) == at)
        else {
            return;
        };

        // A surviving piece begins at the tie and continues past the
        // instruction. There can be several, since conflicting uses split the
        // survivor into overlapping alternatives; each takes its value from
        // `head`, so keep the first whose constraints allow the merge.
        let after_inst = at.next_point();
        for tail in block.spans(live_ranges) {
            let survives = tail.val(live_ranges) == val
                && tail.start(live_ranges) == at
                && tail.end(live_ranges) > after_inst;
            if survives
                && self.try_merge(
                    input.machine,
                    live_ranges,
                    events,
                    Affinity::OverwriteSplit,
                    head,
                    tail,
                )
            {
                break;
            }
        }
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
    region_blocks.extend(region.blocks(&region_tree));

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
            // lazily split them on demand by returning `Edit::CriticalEdge`
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
    events: &mut EventsLog<E>,
    input: &Input<'_, impl InputFunction>,
    output: &mut OutputInner<E>,
) -> IResult<()>
where
    E: EntityRepr,
{
    for region in region_tree.pre_order_iter() {
        let start = live_ranges.next_bundle(output)?;

        for block in region.blocks(&region_tree) {
            for span in block.spans(live_ranges) {
                let root = coalescing.span_sets.find(span);
                if root.bundle(live_ranges).is_some() {
                    continue;
                }

                let set = coalescing.interval_set[root].unwrap();
                let constraint = coalescing.set_constraint[root];
                let members = set.iter(&coalescing.interval_set_arena);

                let bundle = live_ranges.push_bundle(input, output, region, constraint, members)?;
                event!(
                    events,
                    BundleConstructed {
                        bundle,
                        region,
                        num_spans: bundle.spans(live_ranges).len(),
                        num_vals: bundle.num_vals(live_ranges),
                        constraint,
                    }
                );
            }
        }

        let end = live_ranges.next_bundle(output)?;
        region.set_bundles(live_ranges, EntityRange { start, end });
    }

    counts.bundles += live_ranges.len_bundles();
    Ok(())
}

/// Bias each reserved value's bundle towards the register held for it.
///
/// The bundle to bias is the one owning the span that records the fixed
/// operand as a use, so walking the block's uses finds exactly them.
///
/// This hint is what usually elides the move connecting the value to its
/// reserved register; nothing depends on it for correctness, however.
fn hint_reserved_registers<E>(
    input: &Input<'_, impl InputFunction>,
    live_ranges: &mut LiveRanges<E>,
    events: &mut EventsLog<E>,
    scratch: &mut Vec<(LivePoint<E>, Val<E>, Reservation<E>)>,
    block: Block<E>,
    reservations: EntityRange<Reservation<E>>,
) where
    E: EntityRepr,
{
    // The join key, once, so the index and its lookups agree. A clobber has
    // no value to bias any bundle towards it.
    fn key<E>(live_ranges: &LiveRanges<E>, r: Reservation<E>) -> Option<(LivePoint<E>, Val<E>)>
    where
        E: EntityRepr,
    {
        Some((r.start(live_ranges), r.val(live_ranges)?))
    }

    debug_assert!(scratch.is_empty());

    // Index the block's reservations by the join key.
    scratch.extend(reservations.into_iter().filter_map(|r| {
        // Can only hint for single-reg (not group) fixed uses.
        let RegAllocation::Reg(_) = r.reg(live_ranges) else {
            return None;
        };
        let (point, val) = key(live_ranges, r)?;
        Some((point, val, r))
    }));
    scratch.sort_unstable_by_key(|&(point, val, _)| (point, val));

    for u in block.uses(live_ranges) {
        let span = u.span(live_ranges);
        let bundle = span.bundle(live_ranges).unwrap();
        let point = u.point(live_ranges);
        let val = span.val(live_ranges);

        // Every reservation this use matches, a run of the sorted index: one
        // value may be delivered into several registers at once.
        let first = scratch.partition_point(|&(p, v, _)| (p, v) < (point, val));
        for &(_, _, reservation) in scratch[first..]
            .iter()
            .take_while(|&&(p, v, _)| (p, v) == (point, val))
        {
            let RegAllocation::Reg(reg) = reservation.reg(live_ranges) else {
                unreachable!("groups were filtered out of the index");
            };

            let class = match bundle.constraint(live_ranges) {
                OperandConstraint::Any => bundle.value_reg_class(live_ranges, input),
                OperandConstraint::Reg(rc) => rc,
                OperandConstraint::Stack => continue,
                OperandConstraint::Reuse(_) => unreachable!("constraints are already resolved"),
            };
            let RegClassMembers::Regs(members) = class.members(input.machine) else {
                continue;
            };
            if !members.contains(&reg.with_repr32()) {
                continue;
            }

            let mut hint = RegSet::new();
            hint.insert(reg.with_repr32());
            // Speculative, although the reservation is committed: it binds
            // a register at this one instruction, while a settled hint binds
            // one across a region edge that usually runs many times, so the
            // edge outranks it when the two disagree.
            bundle.add_hint(live_ranges, events, &hint, None, HintStrength::Speculative);
        }
    }

    scratch.clear();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::RegClass;
    use crate::context::Context;
    use crate::entity::Inst;
    use crate::input::BlockFrequency;
    use crate::live_ranges::{
        LiveBundle, is_minimal_bundle, normalize_spill_weight, remat_scale,
        round_bundle_spill_weight, touch_mid_inst,
    };
    use crate::test::{TestFunction, TestInput, TestMachine};
    use mutatis::{
        check::{Check, CheckResult},
        mutators as m,
    };
    use std::{
        collections::{HashMap, hash_map},
        format,
        string::{String, ToString},
        vec::Vec,
    };

    /// A run that bailed with `EntityReprTooSmall` never reached the cleanup
    /// at the end of its walk, and `Context::reset` resets that abandoned
    /// context too, so `reset` has to clear the scratch rather than assume it.
    #[test]
    fn reset_clears_scratch_from_an_abandoned_run() {
        let mut coalescing = Coalescing::<u8>::new();

        coalescing.region_blocks.push(Block::try_new(0).unwrap());
        coalescing
            .cross_region_affinities
            .push((LiveSpan::try_new(0).unwrap(), LiveSpan::try_new(1).unwrap()));
        coalescing.hint_scratch.push((
            LivePoint::new(Inst::try_new(0).unwrap(), Position::Early),
            Val::try_new(0).unwrap(),
            Reservation::try_new(0).unwrap(),
        ));
        assert!(!coalescing.is_reset());

        coalescing.reset();
        assert!(coalescing.is_reset());
    }

    /// Run every analysis that coalescing depends on.
    fn analyze(context: &mut ContextInner<u32>, input: &Input<'_, TestFunction>) -> IResult<()> {
        let func = input.func;
        context
            .rpo
            .construct(func, &mut context.dfs, &mut context.output)?;
        context.region_tree.construct(
            func,
            &mut context.counts,
            &mut context.dfs,
            &mut context.output,
        )?;
        context
            .liveness
            .construct(func, &mut context.counts, &context.rpo, &mut context.output)?;
        context.live_ranges.construct(
            input,
            &mut context.counts,
            &mut context.events,
            &mut context.liveness,
            &mut context.output,
        )
    }

    /// Run every analysis up through coalescing.
    fn coalesce_input(test_input: &TestInput) -> Result<Context, String> {
        let mut context = Context::new();
        assert!(context.is_reset());

        let result = test_input.with_input(|input| -> IResult<()> {
            let context = &mut context.context32;
            analyze(context, input)?;
            coalesce(context, input)
        });
        if result.is_err() {
            return Err(format!(
                "coalescing failed: {:?}",
                context.context32.output.take_error()
            ));
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
        for span in block.spans(live_ranges) {
            if span.end(live_ranges) == end {
                map.insert(span.val(live_ranges), span);
            }
        }
        map
    }

    /// The span of each value that is live at `block`'s entry.
    ///
    /// A value can begin the block in several places at once; like
    /// `coalesce_block`, this takes the span that reaches furthest.
    fn entry_spans(
        live_ranges: &LiveRanges<u32>,
        func: &TestFunction,
        block: Block,
    ) -> HashMap<Val, LiveSpan> {
        let (start, _) = block_points(func, block);
        let mut map = HashMap::new();
        for span in block.spans(live_ranges) {
            if span.start(live_ranges) == start {
                match map.entry(span.val(live_ranges)) {
                    hash_map::Entry::Vacant(entry) => {
                        entry.insert(span);
                    }
                    hash_map::Entry::Occupied(mut entry) => {
                        let prev: LiveSpan = *entry.get();
                        if span.end(live_ranges) > prev.end(live_ranges) {
                            entry.insert(span);
                        }
                    }
                }
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
        block.spans(live_ranges).into_iter().find(|&span| {
            span.uses(live_ranges)
                .into_iter()
                .any(|u| u.point(live_ranges).inst() == inst && u.operand(live_ranges) == operand)
        })
    }

    /// Record the affinity between the pieces on either side of the overwrite
    /// split `inst` made in `val`: the one ending where the instruction begins
    /// and every one starting there that outlives the instruction.
    fn across_the_overwrite_split(
        live_ranges: &LiveRanges<u32>,
        block: Block,
        inst: Inst,
        val: Val,
        affinities: &mut Vec<(LiveSpan, LiveSpan, bool)>,
    ) {
        let at = LivePoint::new(inst, Position::Early);
        let Some(span1) = block
            .spans(live_ranges)
            .into_iter()
            .find(|span| span.val(live_ranges) == val && span.end(live_ranges) == at)
        else {
            return;
        };
        for span3 in block.spans(live_ranges) {
            if span3.val(live_ranges) == val
                && span3.start(live_ranges) == at
                && span3.end(live_ranges) > at.next_point()
            {
                affinities.push((span1, span3, true));
            }
        }
    }

    /// Every pair of spans that coalescing should have tried to merge, derived
    /// from the function rather than from anything the pass recorded, as well
    /// as whether coalescing was allowed to take the affinity.
    fn all_affinities(
        live_ranges: &LiveRanges<u32>,
        func: &TestFunction,
    ) -> Vec<(LiveSpan, LiveSpan, bool)> {
        let mut affinities = Vec::new();

        for (block, input_block) in func.blocks() {
            // A def that must reuse one of its own operands' registers. Within
            // one instruction, so no edge and no frequency to consider.
            for (inst, input_inst) in input_block.insts() {
                for j in 0..input_inst.operands_len() {
                    let OperandConstraint::Reuse(i) = input_inst.operand(j).constraint() else {
                        continue;
                    };
                    if let (Some(a), Some(b)) = (
                        operand_span(live_ranges, block, inst, j),
                        operand_span(live_ranges, block, inst, i),
                    ) {
                        affinities.push((a, b, true));
                    }

                    // And the pieces on either side of the overwrite split.
                    // See `Coalescing::coalesce_across_overwrite_split`.
                    across_the_overwrite_split(
                        live_ranges,
                        block,
                        inst,
                        input_inst.operand(i).val().unwrap(),
                        &mut affinities,
                    );
                }
            }

            let block_is_cold = input_block.frequency().is_cold();
            let out = exit_spans(live_ranges, func, block);
            for (i, succ) in input_block.successors().enumerate() {
                let in_ = entry_spans(live_ranges, func, succ);
                let succ_block = func.block(succ);
                let mergeable = !(block_is_cold || succ_block.frequency().is_cold());

                // The same value live on both sides of the edge.
                for (val, &entry) in in_.iter() {
                    if let Some(&exit) = out.get(val) {
                        affinities.push((exit, entry, mergeable));
                    }
                }

                // A block argument and the parameter it feeds.
                for (arg, param) in input_block.successor_block_args(i).zip(succ_block.params()) {
                    if let (Some(&exit), Some(&entry)) = (out.get(&arg), in_.get(&param)) {
                        affinities.push((exit, entry, mergeable));
                    }
                }
            }
        }

        affinities
    }

    /// Do these two bundles hold spans that are live at the same time?
    fn bundles_overlap(live_ranges: &LiveRanges<u32>, a: LiveBundle, b: LiveBundle) -> bool {
        a.spans(live_ranges).any(|x| {
            b.spans(live_ranges).any(|y| {
                x.start(live_ranges) < y.end(live_ranges)
                    && y.start(live_ranges) < x.end(live_ranges)
            })
        })
    }

    #[test]
    fn coalescing_properties() -> CheckResult<TestInput> {
        Check::new().min_iters(2_000).min_duration(std::time::Duration::from_secs(2)).run_with(
            m::default::<TestInput>(),
            crate::test::corpus(),
            |test_input: &TestInput| -> Result<(), String> {
                let func = &test_input.func;
                let mut context = coalesce_input(test_input)?;
                let inner = &context.context32;
                let live_ranges = &inner.live_ranges;
                let inst_block = inst_blocks(func);

                // 1. The bundles partition the spans: every span belongs to a
                // bundle, and every bundle lists exactly the spans that point
                // back at it.
                for span in live_ranges.spans() {
                    if span.bundle(live_ranges).is_none() {
                        return Err(format!("{span:?} was not put in any bundle"));
                    }
                }
                let mut total = 0;
                for bundle in live_ranges.bundles() {
                    for span in bundle.spans(live_ranges) {
                        total += 1;
                        if span.bundle(live_ranges) != Some(bundle) {
                            return Err(format!(
                                "{bundle:?} lists {span:?}, but {span:?} points at {:?}",
                                span.bundle(live_ranges),
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
                for bundle in live_ranges.bundles() {
                    let mut previous: Option<LivePoint<u32>> = None;
                    for span in bundle.spans(live_ranges) {
                        let start = span.start(live_ranges);
                        if previous.is_some_and(|previous| previous > start) {
                            return Err(format!(
                                "{bundle:?} holds a span starting at {start:?} after one ending \
                                 at {previous:?}",
                            ));
                        }
                        previous = Some(span.end(live_ranges));
                    }
                }

                // 3. Every span in a bundle lies in the bundle's region.
                for bundle in live_ranges.bundles() {
                    for span in bundle.spans(live_ranges) {
                        let block = inst_block[&span.start(live_ranges).inst()];
                        let block = Block::try_new(block.index()).unwrap();
                        let region = block.region(&inner.region_tree);
                        if region != bundle.region(live_ranges) {
                            return Err(format!(
                                "{bundle:?} is in {:?}, but holds {span:?}, which is in {region:?}",
                                bundle.region(live_ranges),
                            ));
                        }
                    }
                }

                // 4. A bundle's constraint is the merge of its spans' resolved
                // use constraints, and so is never a `Reuse`.
                test_input.with_input(|input| -> Result<(), String> {
                    for bundle in live_ranges.bundles() {
                        if matches!(bundle.constraint(live_ranges), OperandConstraint::Reuse(_)) {
                            return Err(format!("{bundle:?}'s constraint is unresolved"));
                        }
                        let mut expected = OperandConstraint::Any;
                        for span in bundle.spans(live_ranges) {
                            let span = span.constraint(live_ranges, input);
                            expected =
                                expected
                                    .merge_resolved(&span, input.machine)
                                    .ok_or_else(|| {
                                        format!("{bundle:?}'s spans have conflicting constraints")
                                    })?;
                        }
                        if expected != bundle.constraint(live_ranges) {
                            return Err(format!(
                                "{bundle:?}'s constraint is {:?}, but its spans want {expected:?}",
                                bundle.constraint(live_ranges),
                            ));
                        }
                    }
                    Ok(())
                })?;

                // 5. The bundles' span lists tile their shared storage: no
                // gaps, no overlap, nothing left over.
                let mut next = 0;
                for bundle in live_ranges.bundles() {
                    let spans = bundle.spans_storage(live_ranges);
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
                    regions.extend(region.children(&inner.region_tree));
                    for bundle in region.bundles(live_ranges) {
                        counted += 1;
                        let actual = bundle.region(live_ranges);
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

                // 7. Coalescing did its job: for every affinity it was allowed
                // to take, either the two spans share a bundle or there is a
                // reason they cannot. Aggressive coalescing is order-dependent,
                // so "an earlier merge made this one illegal" is one of those
                // reasons -- but it is only legitimate if it still shows up as a
                // conflict now, since bundles only ever grow.
                test_input.with_input(|input| -> Result<(), String> {
                    for (a, b, mergeable) in all_affinities(live_ranges, func) {
                        let (Some(ba), Some(bb)) = (a.bundle(live_ranges), b.bundle(live_ranges))
                        else {
                            return Err("an affinity's span has no bundle".to_string());
                        };
                        if ba == bb {
                            continue;
                        }
                        if !mergeable {
                            continue;
                        }
                        if ba.region(live_ranges) != bb.region(live_ranges) {
                            continue;
                        }
                        if ba
                            .constraint(live_ranges)
                            .merge_resolved(&bb.constraint(live_ranges), input.machine)
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

                // 7b. And it did it for every reuse tie it had to. Property 7
                // waives an affinity whose bundles' constraints conflict; a tie
                // cannot be waived, since one bundle is the only thing that
                // satisfies it, unless a reservation satisfies it instead.
                test_input.with_input(|input| -> Result<(), String> {
                for (block, input_block) in func.blocks() {
                    for (inst, input_inst) in input_block.insts() {
                        for j in 0..input_inst.operands_len() {
                            let OperandConstraint::Reuse(i) = input_inst.operand(j).constraint()
                            else {
                                continue;
                            };
                            if crate::live_ranges::fixed_operand_of(
                                input.func,
                                input.machine,
                                inst,
                                i,
                            )
                            .is_some()
                            {
                                continue;
                            }
                            let (Some(a), Some(b)) = (
                                operand_span(live_ranges, block, inst, j),
                                operand_span(live_ranges, block, inst, i),
                            ) else {
                                continue;
                            };
                            if a.bundle(live_ranges) != b.bundle(live_ranges) {
                                return Err(format!(
                                    "operand {j} of {inst:?} reuses operand {i}, but their \
                                     spans {a:?} and {b:?} are in {:?} and {:?}",
                                    a.bundle(live_ranges),
                                    b.bundle(live_ranges),
                                ));
                            }
                        }
                    }
                }
                Ok(())
                })?;

                // 8. A register hint never widens what a bundle may be
                // allocated to, and only a cross-region affinity or a
                // reservation can put one there in the first place.
                let cross_region: Vec<(LiveBundle, LiveBundle)> = test_input.with_input(|input| {
                    all_affinities(live_ranges, func)
                        .into_iter()
                        .filter_map(|(a, b, _)| {
                            let (ba, bb) = (
                                a.bundle(live_ranges).unwrap(),
                                b.bundle(live_ranges).unwrap(),
                            );
                            let (ra, rb) = (ba.region(live_ranges), bb.region(live_ranges));
                            let _ = input;
                            if rb.parent(&inner.region_tree) == Some(ra) {
                                Some((ba, bb))
                            } else if ra.parent(&inner.region_tree) == Some(rb) {
                                Some((bb, ba))
                            } else {
                                None
                            }
                        })
                        .collect()
                });
                test_input.with_input(|input| -> Result<(), String> {
                    for bundle in live_ranges.bundles() {
                        if bundle.preference(live_ranges).is_empty() {
                            continue;
                        }
                        if let OperandConstraint::Reg(class) = bundle.constraint(live_ranges) {
                            let members = class.member_set(input.machine);
                            if !bundle.preference(live_ranges).union().is_subset_of(members) {
                                return Err(format!(
                                    "{bundle:?} prefers registers outside its own class",
                                ));
                            }
                        }

                        // Hints stay inside the class its values live in.
                        for span in bundle.spans(live_ranges) {
                            let val = span.val(live_ranges);
                            let class = input.func.value(val).reg_class();
                            let members = class.member_set(input.machine);
                            if !bundle.preference(live_ranges).union().is_subset_of(members) {
                                return Err(format!(
                                    "{bundle:?} prefers registers that {val:?}, one of its own \
                                     values, may not live in",
                                ));
                            }
                        }
                        let reserved = bundle.spans(live_ranges).any(|span| {
                            let val = span.val(live_ranges);
                            span.uses(live_ranges).into_iter().any(|u| {
                                let point = u.point(live_ranges);
                                live_ranges.reservations().any(|r| {
                                    matches!(r.reg(live_ranges), RegAllocation::Reg(_))
                                        && r.start(live_ranges) == point
                                        && r.val(live_ranges) == Some(val)
                                })
                            })
                        });
                        if !reserved && !cross_region.iter().any(|&(parent, _)| parent == bundle) {
                            return Err(format!(
                                "{bundle:?} has a register hint but no cross-region affinity or \
                                 reservation that could have given it one",
                            ));
                        }
                    }
                    Ok(())
                })?;

                // 9. A logged cross-region affinity really does cross
                // regions.
                #[cfg(feature = "visualizer")]
                for (_, event) in context.context32.events.iter() {
                    let crate::events::Event::CrossRegionAffinity { a, b } = event else {
                        continue;
                    };
                    let (ra, rb) = (
                        a.bundle(live_ranges).unwrap().region(live_ranges),
                        b.bundle(live_ranges).unwrap().region(live_ranges),
                    );
                    if ra == rb {
                        return Err(format!(
                            "{a:?} and {b:?} were logged as a cross-region affinity, but both                              ended up in {ra:?}",
                        ));
                    }
                }

                // 10. Every span belongs to exactly one block's span list, and
                // lies inside that block's program points.
                let mut seen = 0;
                for (block, _) in func.blocks() {
                    let block_e = Block::try_new(block.index()).unwrap();
                    let (start, end) = block_points(func, block);
                    for span in block_e.spans(live_ranges) {
                        seen += 1;
                        if span.start(live_ranges) < start || span.end(live_ranges) > end {
                            return Err(format!(
                                "{span:?} is listed under {block:?}, but covers {:?}..{:?}, \
                                 outside {start:?}..{end:?}",
                                span.start(live_ranges),
                                span.end(live_ranges),
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

                // 11. Coalescing twice gives exactly the same bundles.
                let again = coalesce_input(test_input)?;
                let again = &again.context32.live_ranges;
                if again.len_bundles() != live_ranges.len_bundles() {
                    return Err("coalescing twice gave a different number of bundles".to_string());
                }
                for index in 0..live_ranges.len_bundles() {
                    let bundle = LiveBundle::try_new(index).unwrap();
                    if bundle.region(live_ranges) != bundle.region(again)
                        || bundle.constraint(live_ranges) != bundle.constraint(again)
                        || bundle.preference(live_ranges) != bundle.preference(again)
                        || bundle.spans(live_ranges).ne(bundle.spans(again))
                    {
                        return Err(format!(
                            "coalescing twice gave {bundle:?} different contents"
                        ));
                    }
                }

                // 11. A bundle's weight, its fixed-use flag, and its minimality
                // are exactly what its spans say they are: the flag is the OR
                // of theirs, the weight is their uses' weights over their
                // summed length, normalized, and the minimality is
                // `is_minimal_bundle` of the gaps a cut could go in, their
                // uses' count, and the instructions they actually cover. A
                // bundle that is not minimal also discounts each span's uses by
                // its value's remat cost. Recomputing the weight from the
                // *packed* per-use weights and rounding the result the way the
                // bundle does makes that one an equality rather than an
                // approximation.
                test_input.with_input(|input| -> Result<(), String> {
                for bundle in live_ranges.bundles() {
                    let mut total_cost = 0.0;
                    let mut discounted_cost = 0.0;
                    let mut num_insts = 0;
                    let num_spans = bundle.spans(live_ranges).len();
                    let mut num_uses = 0;

                    // A gap between two spans takes a cut unless they touch in
                    // the middle of an instruction and something across the gap
                    // needs a move, and two spans touching like that both cover
                    // the instruction they touch in.
                    let mut num_cuttable_gaps = 0;
                    let mut shared_insts = 0;
                    let mut prev: Option<LiveSpan> = None;

                    for span in bundle.spans(live_ranges) {
                        let uses = span.uses(live_ranges);
                        num_uses += uses.len();
                        let span_cost = uses
                            .into_iter()
                            .map(|u| u.weight(live_ranges).as_f32())
                            .sum::<f32>();
                        total_cost += span_cost;
                        let remat = input.func.value(span.val(live_ranges)).remat_cost();
                        discounted_cost += span_cost * remat_scale(remat);
                        num_insts += span.len_insts(live_ranges);

                        if let Some(prev) = prev {
                            let tied = span.is_tied_to(live_ranges, input, prev);
                            if touch_mid_inst(prev.end(live_ranges), span.start(live_ranges)) {
                                shared_insts += 1;
                            }
                            if !tied {
                                num_cuttable_gaps += 1;
                            }
                        }
                        prev = Some(span);
                    }

                    let distinct_insts = num_insts - shared_insts;
                    let expected_minimal =
                        is_minimal_bundle(num_cuttable_gaps, num_uses, distinct_insts);

                    // A minimal bundle has no length left to give up, so its
                    // uses pay full price.
                    let expected_cost = if expected_minimal {
                        total_cost
                    } else {
                        discounted_cost
                    };
                    let expected =
                        round_bundle_spill_weight(normalize_spill_weight(expected_cost, num_insts));
                    let actual = bundle.spill_weight(live_ranges);
                    if actual != expected {
                        return Err(format!(
                            "{bundle:?} weighs {actual}, but its {num_insts} instructions and \
                             {expected_cost} of use cost come to {expected}",
                        ));
                    }
                    if !actual.is_finite() || actual < 0.0 {
                        return Err(format!("{bundle:?} weighs {actual}, which is not a weight"));
                    }

                    if bundle.is_minimal(live_ranges) != expected_minimal {
                        return Err(format!(
                            "{bundle:?} reports is_minimal = {}, but it holds {num_spans} spans \
                             with {num_cuttable_gaps} cuttable gaps between them and {num_uses} \
                             uses across {distinct_insts} instructions",
                            bundle.is_minimal(live_ranges),
                        ));
                    }
                    // Implied by the definition, but worth stating: a minimal
                    // bundle is never a set of spans that could be handed out
                    // one bundle each. It may still be more than one span, when
                    // two of them touch at a `Late` point that a cut cannot go
                    // at.
                    if expected_minimal && num_spans != 1 + shared_insts {
                        return Err(format!(
                            "{bundle:?} is minimal but holds {num_spans} spans, only \
                             {shared_insts} of whose gaps are uncuttable, so the rest could be \
                             split into one bundle each",
                        ));
                    }
                }
                Ok(())
                })?;

                // 12. Everything the pass touched resets cleanly.
                context.reset();
                if !context.is_reset() {
                    return Err("`Context::is_reset` is false after `reset`".to_string());
                }

                Ok(())
            },
        )
    }

    /// The span of `val` in `block`, of which these hand-built functions only
    /// ever have one.
    fn only_span(live_ranges: &LiveRanges<u32>, block: usize, val: usize) -> LiveSpan {
        let block = Block::try_new(block).unwrap();
        let val = Val::try_new(val).unwrap();
        let mut found = block
            .spans(live_ranges)
            .into_iter()
            .filter(|&span| span.val(live_ranges) == val);
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
            arg.bundle(live_ranges),
            param.bundle(live_ranges),
            "the argument and the parameter should share a bundle",
        );
    }

    /// ... but not when the two ends want locations that no single location
    /// satisfies.
    ///
    /// The conflict must be between constraints the bundles actually carry: a
    /// fixed operand holds its register instead of constraining its value's
    /// bundle.
    #[test]
    fn a_block_argument_with_a_conflicting_parameter_is_not_coalesced() {
        let both = OperandConstraint::Reg(
            RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap(),
        );
        let input = TestInput::with_block_arg_constraints(both, OperandConstraint::Stack);
        let context = coalesce_input(&input).unwrap();
        let live_ranges = &context.context32.live_ranges;

        let arg = only_span(live_ranges, 0, 0);
        let param = only_span(live_ranges, 1, 1);
        let arg_bundle = arg.bundle(live_ranges).unwrap();
        assert_eq!(arg_bundle.constraint(live_ranges), both);
        assert_ne!(
            arg.bundle(live_ranges),
            param.bundle(live_ranges),
            "a register and the stack are disjoint, so these may not share a \
             location",
        );
    }

    /// ... and not when the edge the argument travels along is cold, however
    /// happily the two ends would otherwise share a location: the move we would
    /// be removing hardly ever runs.
    #[test]
    fn a_block_argument_is_not_coalesced_across_a_cold_edge() {
        let mut input =
            TestInput::with_block_arg_constraints(OperandConstraint::Any, OperandConstraint::Any);
        input.set_block_frequencies(BlockFrequency::COLD);
        let context = coalesce_input(&input).unwrap();
        let live_ranges = &context.context32.live_ranges;

        let arg = only_span(live_ranges, 0, 0);
        let param = only_span(live_ranges, 1, 1);
        assert_ne!(
            arg.bundle(live_ranges),
            param.bundle(live_ranges),
            "the edge is cold, so the argument and the parameter should not share a bundle",
        );
    }

    /// One cold end is enough, whichever end it is.
    #[test]
    fn a_block_argument_is_not_coalesced_when_only_one_end_of_the_edge_is_cold() {
        for cold in [0, 1] {
            let mut input = TestInput::with_block_arg_constraints(
                OperandConstraint::Any,
                OperandConstraint::Any,
            );
            input.set_block_frequency(Block::try_new(cold).unwrap(), BlockFrequency::COLD);
            let context = coalesce_input(&input).unwrap();
            let live_ranges = &context.context32.live_ranges;

            let arg = only_span(live_ranges, 0, 0);
            let param = only_span(live_ranges, 1, 1);
            assert_ne!(
                arg.bundle(live_ranges),
                param.bundle(live_ranges),
                "block {cold} is cold, which makes the edge between them cold",
            );
        }
    }

    /// The cold rule is about edges, so it leaves a reuse affinity alone: that
    /// one ties two operands of a single instruction, and a move between them
    /// would run exactly as often as the instruction itself.
    #[test]
    fn a_reuse_operand_is_still_coalesced_inside_a_cold_block() {
        let mut input = TestInput::with_reuse_def(OperandConstraint::Any);
        input.set_block_frequencies(BlockFrequency::COLD);
        let context = coalesce_input(&input).unwrap();
        let live_ranges = &context.context32.live_ranges;

        let spans: Vec<LiveSpan> = live_ranges.spans().collect();
        assert_eq!(spans.len(), 2, "{spans:#?}");
        assert_eq!(
            spans[0].bundle(live_ranges),
            spans[1].bundle(live_ranges),
            "the tied def and the operand it reuses should still share a bundle",
        );
    }

    /// Of the three pieces a reuse split leaves, the middle one goes to the
    /// definition and the outer two go together, so the value stays put.
    #[test]
    fn the_pieces_on_either_side_of_a_reuse_split_are_coalesced() {
        let input = TestInput::with_reuse_of_a_surviving_value();

        // The tie is on `inst1`: operand 1 defines over operand 0's place.
        let (survivor, defined) = input.with_input(|input| {
            let inst = input.func.inst(Inst::try_new(1).unwrap());
            (
                inst.operand(0).val().unwrap(),
                inst.operand(1).val().unwrap(),
            )
        });

        let context = coalesce_input(&input).unwrap();
        let live_ranges = &context.context32.live_ranges;
        let block = Block::try_new(0).unwrap();

        let mut pieces: Vec<LiveSpan> = block
            .spans(live_ranges)
            .into_iter()
            .filter(|&span| span.val(live_ranges) == survivor)
            .collect();
        pieces.sort_by_key(|span| (span.start(live_ranges), span.end(live_ranges)));
        assert_eq!(pieces.len(), 3, "{pieces:#?}");
        let (span1, span2, span3) = (pieces[0], pieces[1], pieces[2]);

        assert_eq!(
            span1.bundle(live_ranges),
            span3.bundle(live_ranges),
            "the pieces on either side of the tie should share a bundle",
        );
        assert_eq!(
            span2.bundle(live_ranges),
            only_span(live_ranges, 0, defined.index()).bundle(live_ranges),
            "the piece the definition overwrites should share the definition's bundle",
        );
        assert_ne!(
            span1.bundle(live_ranges),
            span2.bundle(live_ranges),
            "the surviving value and the definition that overwrites one copy of \
             it may not share a location",
        );
    }

    /// A read pinned to the one register its own instruction's definition
    /// overwrites leaves coalescing nothing to do.
    ///
    /// The read used to be split into three pieces, two of which had to be
    /// coalesced back together. A reservation holds the register now, so the
    /// value is never cut up.
    #[test]
    fn a_fixed_overwrite_leaves_nothing_to_coalesce() {
        let input = TestInput::with_a_read_overwritten_by_a_fixed_def();

        // `inst1` reads the survivor from the register its own operand 1
        // defines into.
        let (survivor, defined) = input.with_input(|input| {
            let inst = input.func.inst(Inst::try_new(1).unwrap());
            (
                inst.operand(0).val().unwrap(),
                inst.operand(1).val().unwrap(),
            )
        });

        let context = coalesce_input(&input).unwrap();
        let live_ranges = &context.context32.live_ranges;
        let block = Block::try_new(0).unwrap();

        let pieces: Vec<LiveSpan> = block
            .spans(live_ranges)
            .into_iter()
            .filter(|&span| span.val(live_ranges) == survivor)
            .collect();
        assert_eq!(pieces.len(), 1, "{pieces:#?}");

        assert_ne!(
            pieces[0].bundle(live_ranges),
            only_span(live_ranges, 0, defined.index()).bundle(live_ranges),
            "the survivor is live across the definition that takes the \
             register from it, so the two may not share a location",
        );
    }

    /// The bundle for `val` in `block`, which these hand-built functions always
    /// have.
    fn only_bundle(live_ranges: &LiveRanges<u32>, block: usize, val: usize) -> LiveBundle<u32> {
        only_span(live_ranges, block, val)
            .bundle(live_ranges)
            .expect("the span is in a bundle")
    }

    /// A value defined by one instruction and used by the next reaches across
    /// the boundary between them, and a move can go there, so its bundle is not
    /// minimal: the splitter still has work it can do.
    #[test]
    fn a_bundle_reaching_between_two_instructions_is_not_minimal() {
        let input = TestInput::with_use_constraints(&[OperandConstraint::Any]);
        let context = coalesce_input(&input).unwrap();
        let live_ranges = &context.context32.live_ranges;

        let span = only_span(live_ranges, 0, 0);
        assert_eq!(
            span.len_insts(live_ranges),
            2,
            "the def and the use are on different instructions",
        );
        assert!(!only_bundle(live_ranges, 0, 0).is_minimal(live_ranges));
    }

    /// A bundle of several spans covers all of them.
    #[test]
    fn a_bundle_of_several_spans_is_not_minimal() {
        let input =
            TestInput::with_block_arg_constraints(OperandConstraint::Any, OperandConstraint::Any);
        let context = coalesce_input(&input).unwrap();
        let live_ranges = &context.context32.live_ranges;

        let arg = only_span(live_ranges, 0, 0);
        let param = only_span(live_ranges, 1, 1);
        let bundle = arg.bundle(live_ranges).expect("the span is in a bundle");
        assert_eq!(
            param.bundle(live_ranges),
            Some(bundle),
            "coalescing puts the argument and the parameter in one bundle",
        );
        assert_eq!(
            param.len_insts(live_ranges),
            1,
            "the parameter's span sits inside the one instruction that defines it",
        );
        assert!(
            !bundle.is_minimal(live_ranges),
            "a bundle holding more than one span always has a bundle-per-span split left",
        );
    }

    /// Splitting a span whose uses conflict leaves pieces of different sizes,
    /// and each is judged on its own.
    #[test]
    fn a_conflict_split_leaves_one_minimal_piece_and_one_that_is_not() {
        let both = OperandConstraint::Reg(
            RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap(),
        );
        let input = TestInput::with_use_constraints(&[both, OperandConstraint::Stack]);
        let context = coalesce_input(&input).unwrap();
        let live_ranges = &context.context32.live_ranges;

        let spans: Vec<LiveSpan> = live_ranges.spans().collect();
        assert_eq!(spans.len(), 2, "{spans:#?}");
        let (first, second) = (spans[0], spans[1]);

        // The def through the second use, cut just before the conflict: two
        // instructions, and a boundary between them to cut at.
        assert_eq!(first.len_insts(live_ranges), 2);
        let first_bundle = first.bundle(live_ranges).expect("the span is in a bundle");
        assert!(!first_bundle.is_minimal(live_ranges));

        // The tail, holding only the conflicting use.
        assert_eq!(second.len_insts(live_ranges), 1);
        let second_bundle = second.bundle(live_ranges).expect("the span is in a bundle");
        assert!(second_bundle.is_minimal(live_ranges));

        assert_ne!(
            first_bundle, second_bundle,
            "a register and the stack are disjoint, so the pieces cannot share \
             a bundle",
        );
    }

    /// A merge that happens says which two spans it joined and why.
    #[test]
    #[cfg(feature = "visualizer")]
    fn coalesced_spans_are_logged() {
        use crate::events::Event;

        let input =
            TestInput::with_block_arg_constraints(OperandConstraint::Any, OperandConstraint::Any);
        let context = coalesce_input(&input).unwrap();
        let live_ranges = &context.context32.live_ranges;

        let arg = only_span(live_ranges, 0, 0);
        let param = only_span(live_ranges, 1, 1);

        let merges: Vec<_> = context
            .context32
            .events
            .iter()
            .filter_map(|(_, e)| match e {
                Event::SpansCoalesced { a, b, affinity } => Some((*a, *b, *affinity)),
                _ => None,
            })
            .collect();
        assert!(
            merges
                .iter()
                .any(|&(a, b, affinity)| (a, b) == (arg, param)
                    && affinity == Affinity::BlockCallArg),
            "{merges:#?}",
        );
    }

    /// So does a merge that is refused, which is the more interesting half.
    #[test]
    #[cfg(feature = "visualizer")]
    fn refused_coalesces_are_logged() {
        use crate::events::Event;

        let both = OperandConstraint::Reg(
            RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap(),
        );
        let input = TestInput::with_block_arg_constraints(both, OperandConstraint::Stack);
        let context = coalesce_input(&input).unwrap();
        let live_ranges = &context.context32.live_ranges;

        let arg = only_span(live_ranges, 0, 0);
        let param = only_span(live_ranges, 1, 1);

        let refusals: Vec<_> = context
            .context32
            .events
            .iter()
            .filter_map(|(_, e)| match e {
                Event::CoalesceRefused {
                    a,
                    b,
                    affinity,
                    reason,
                } => Some((*a, *b, *affinity, *reason)),
                _ => None,
            })
            .collect();
        assert!(
            refusals.iter().any(|&(a, b, affinity, reason)| {
                (a, b) == (arg, param)
                    && affinity == Affinity::BlockCallArg
                    && reason == RefusedReason::ConstraintConflict
            }),
            "{refusals:#?}",
        );
    }

    /// Every bundle coalescing built is logged, with the shape it was built
    /// with.
    #[test]
    #[cfg(feature = "visualizer")]
    fn constructed_bundles_are_logged() {
        use crate::events::Event;

        let input = TestInput::with_reuse_of_a_surviving_value();
        let context = coalesce_input(&input).unwrap();
        let live_ranges = &context.context32.live_ranges;

        let logged: Vec<_> = context
            .context32
            .events
            .iter()
            .filter_map(|(_, e)| match e {
                Event::BundleConstructed {
                    bundle,
                    region,
                    num_spans,
                    num_vals,
                    constraint,
                } => Some((*bundle, *region, *num_spans, *num_vals, *constraint)),
                _ => None,
            })
            .collect();

        let bundles: Vec<LiveBundle> = live_ranges.bundles().collect();
        assert!(!bundles.is_empty());
        assert_eq!(logged.len(), bundles.len(), "{logged:#?}");
        for (bundle, region, num_spans, num_vals, constraint) in logged {
            assert_eq!(region, bundle.region(live_ranges));
            assert_eq!(constraint, bundle.constraint(live_ranges));
            assert_eq!(num_spans, bundle.spans(live_ranges).len());
            assert_eq!(num_vals, bundle.num_vals(live_ranges));
        }
    }

    /// However many arms, each value's loop spans share one bundle.
    #[test]
    fn values_live_through_a_wide_switch_are_each_one_bundle_in_the_loop() {
        let (arms, vals) = (1_000, 20);
        let input = TestInput::with_a_loop_around_a_wide_switch(arms, vals);
        let context = coalesce_input(&input).unwrap();
        let live_ranges = &context.context32.live_ranges;
        let header = Block::try_new(1).unwrap();
        let loop_region = header.region(&context.context32.region_tree);

        for v in 0..vals {
            let val = Val::try_new(v).unwrap();
            let mut bundles: Vec<LiveBundle> = live_ranges
                .spans()
                .filter(|span| span.val(live_ranges) == val)
                .map(|span| span.bundle(live_ranges).unwrap())
                .filter(|bundle| bundle.region(live_ranges) == loop_region)
                .collect();
            bundles.dedup();
            assert_eq!(
                bundles.len(),
                1,
                "{val:?} is in {} bundles inside the loop",
                bundles.len(),
            );
            // Header, arms, latch.
            assert_eq!(bundles[0].spans(live_ranges).len(), 2 * arms + 2);
        }

        #[cfg(feature = "visualizer")]
        for (_, event) in context.context32.events.iter() {
            if let crate::events::Event::CoalesceRefused { reason, .. } = event {
                assert_ne!(*reason, RefusedReason::Overlap);
                assert_ne!(*reason, RefusedReason::OutOfFuel);
            }
        }
    }

    /// `n` one-point intervals at `first, first + 2, ..`, as one set.
    fn every_other_point(
        sets: &mut IntervalSetArena<LiveSpan, u32>,
        spans: core::ops::Range<usize>,
        first: u32,
    ) -> IntervalSet<LiveSpan> {
        use crate::interval_sets::Fuel;
        let mut set: Option<IntervalSet<LiveSpan>> = None;
        for (i, k) in spans.enumerate() {
            let start = first + 2 * u32::try_from(i).unwrap();
            let one = IntervalSet::singleton(sets, LiveSpan::try_new(k).unwrap(), start, start + 1);
            set = Some(match set {
                None => one,
                Some(set) => set.try_union(sets, one, &mut Fuel::new(u64::MAX)).unwrap(),
            });
        }
        set.unwrap()
    }

    /// Refusing a set that sits in one gap of a large set, but for its last
    /// span, costs `O(log n)` however often it is repeated.
    #[test]
    fn refusing_a_set_inside_one_gap_of_a_large_set_is_cheap() {
        use crate::interval_sets::{Fuel, Refused};

        let n = 4_096;
        let mut sets = IntervalSetArena::<LiveSpan, u32>::new();
        let large = every_other_point(&mut sets, 0..n, 10);
        let end = 10 + 2 * u32::try_from(n).unwrap();
        let small = IntervalSet::singleton(&mut sets, LiveSpan::try_new(n).unwrap(), 0, 1);
        let last = IntervalSet::singleton(
            &mut sets,
            LiveSpan::try_new(n + 1).unwrap(),
            end - 3,
            end + 2,
        );
        let small = small
            .try_union(&mut sets, last, &mut Fuel::new(u64::MAX))
            .unwrap();

        let cheap = 2 * u64::from(n.ilog2()) + 8;
        assert!(cheap < RegionFuel::FLOOR);
        let mut fuel = RegionFuel::new(n + 2);
        for _ in 0..n {
            let mut check = Fuel::new(fuel.allowance());
            assert_eq!(
                large.try_union(&mut sets, small, &mut check),
                Err(Refused::Overlap)
            );
            assert!(check.spent() <= cheap, "spent {}", check.spent());
            fuel.charge(check.spent(), true);
        }
    }

    /// A merge at `FLOOR` fuel still affords a modestly interleaved pair.
    ///
    /// `last_ending_by`'s one `next` step is what keeps a boundary O(1) in
    /// fuel here: descending from the root instead costs `O(log n)` per
    /// boundary, which at `FLOOR` refuses pairs this test merges. A region
    /// whose budget is spent is one under pressure, so these are exactly the
    /// merges whose loss shows up as a register-register move.
    #[test]
    fn a_modest_interleaving_still_merges_at_the_floor() {
        use crate::interval_sets::Fuel;

        // Interleaved at stride 4: `a` at 0, 4, 8, ..., `b` at 2, 6, 10, ...,
        // so the two cross at every element and `check_disjoint` walks a
        // boundary for each.
        for n in [2usize, 4, 8, 16] {
            let mut sets = IntervalSetArena::<LiveSpan, u32>::new();
            let build = |sets: &mut IntervalSetArena<LiveSpan, u32>, base: usize, first: u32| {
                let mut set: Option<IntervalSet<LiveSpan>> = None;
                for i in 0..n {
                    let k = LiveSpan::try_new(base + i).unwrap();
                    let start = first + 4 * u32::try_from(i).unwrap();
                    let one = IntervalSet::singleton(&mut *sets, k, start, start + 1);
                    set = Some(match set {
                        None => one,
                        Some(set) => set
                            .try_union(&mut *sets, one, &mut Fuel::new(u64::MAX))
                            .unwrap(),
                    });
                }
                set.unwrap()
            };
            let a = build(&mut sets, 0, 0);
            let b = build(&mut sets, n, 2);

            let mut check = Fuel::new(RegionFuel::FLOOR);
            assert!(
                a.try_union(&mut sets, b, &mut check).is_ok(),
                "{n} interleaved elements per set ran out of fuel at FLOOR, \
                 spending {}",
                check.spent(),
            );
        }
    }

    /// Two finely interleaved sets cost far more than `FLOOR` to refuse, so
    /// once a region's budget is gone, repeated refusals stop at `FLOOR`.
    #[test]
    fn repeated_costly_refusals_are_capped_at_the_floor() {
        use crate::interval_sets::{Fuel, Refused};

        let n = 4_096;
        let mut sets = IntervalSetArena::<LiveSpan, u32>::new();
        let a = every_other_point(&mut sets, 0..n, 0);
        let b = every_other_point(&mut sets, n..2 * n, 1);
        let end = 2 * u32::try_from(n).unwrap();
        let one =
            IntervalSet::singleton(&mut sets, LiveSpan::try_new(2 * n).unwrap(), end, end + 2);
        let a = a
            .try_union(&mut sets, one, &mut Fuel::new(u64::MAX))
            .unwrap();
        let one = IntervalSet::singleton(
            &mut sets,
            LiveSpan::try_new(2 * n + 1).unwrap(),
            end + 1,
            end + 3,
        );
        let b = b
            .try_union(&mut sets, one, &mut Fuel::new(u64::MAX))
            .unwrap();

        let mut unlimited = Fuel::new(u64::MAX);
        assert_eq!(
            a.try_union(&mut sets, b, &mut unlimited),
            Err(Refused::Overlap)
        );
        assert!(unlimited.spent() > 2 * u64::try_from(n).unwrap());

        let mut fuel = RegionFuel::new(2 * n + 2);
        let mut out_of_fuel = 0;
        for _ in 0..2 * n {
            let allowance = fuel.allowance();
            let mut check = Fuel::new(allowance);
            assert!(a.try_union(&mut sets, b, &mut check).is_err());
            fuel.charge(check.spent(), true);
            if allowance == RegionFuel::FLOOR {
                assert_eq!(check.spent(), RegionFuel::FLOOR);
                out_of_fuel += 1;
            }
        }
        assert_eq!(fuel.budget, 0);
        assert!(out_of_fuel > n, "only {out_of_fuel} checks were capped");
    }

    /// A reuse tie merges even when the region has no fuel left.
    #[test]
    fn a_reuse_tie_is_merged_with_no_fuel_left() {
        use crate::interval_sets::{Fuel, Refused};

        let input = TestInput::with_reuse_of_a_surviving_value();
        let (survivor, defined) = input.with_input(|input| {
            let inst = input.func.inst(Inst::try_new(1).unwrap());
            (
                inst.operand(0).val().unwrap(),
                inst.operand(1).val().unwrap(),
            )
        });

        let mut context = Context::new();
        input.with_input(|input| {
            let inner = &mut context.context32;
            analyze(inner, input).unwrap();
            let ContextInner {
                coalescing,
                live_ranges,
                events,
                ..
            } = inner;
            for span in live_ranges.spans() {
                coalescing.seed(live_ranges, input, span);
            }

            let mut pieces: Vec<LiveSpan> = live_ranges
                .spans()
                .filter(|&span| span.val(live_ranges) == survivor)
                .collect();
            pieces.sort_by_key(|span| (span.start(live_ranges), span.end(live_ranges)));
            let (before, overwritten) = (pieces[0], pieces[1]);
            let def = only_span(live_ranges, 0, defined.index());

            // Surround `overwritten` with `def`'s set, so the tie misses the
            // check's constant-time path.
            coalescing.overlap_fuel = RegionFuel::new(live_ranges.len_spans());
            let mut merge = |coalescing: &mut Coalescing<u32>, affinity, a, b| {
                coalescing.try_merge(input.machine, live_ranges, events, affinity, a, b)
            };
            assert!(merge(coalescing, Affinity::CrossEdge, before, def));

            // Without fuel, the check cannot decide.
            let set = |coalescing: &mut Coalescing<u32>, span| {
                let root = coalescing.span_sets.find(span);
                coalescing.interval_set[root].unwrap()
            };
            let (a, b) = (set(coalescing, overwritten), set(coalescing, def));
            assert_eq!(
                a.try_union(&mut coalescing.interval_set_arena, b, &mut Fuel::new(0)),
                Err(Refused::OutOfFuel),
            );

            coalescing.overlap_fuel = RegionFuel::EMPTY;
            assert!(merge(coalescing, Affinity::ReuseOperand, overwritten, def));
        });
    }

    /// The whole log must survive `serde_json`, which is what catches a
    /// non-finite float or a variant that internal tagging rejects.
    #[test]
    #[cfg(feature = "visualizer")]
    fn the_event_log_round_trips_through_json() {
        for input in [
            TestInput::with_reuse_of_a_surviving_value(),
            TestInput::with_a_self_looping_entry_block(),
            TestInput::with_a_critical_edge(),
        ] {
            let context = coalesce_input(&input).unwrap();
            let json = serde_json::to_string(&context.context32.events).unwrap();
            assert!(json.starts_with('['), "{json}");
        }
    }
}
