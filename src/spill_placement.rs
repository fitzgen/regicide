//! Spill placement.
//!
//! Region allocation decided which bundles are allocated on the stack and spill
//! slot allocation decided which slot each spilled value gets; this pass
//! decides where the spill goes.
//!
//! The only correctness requirements are that every reload is dominated by a
//! spill (there need not be only one!), and a spill must be dominated by the
//! value's definition and placed at a point where we have the value in a
//! register. But not all spill locations are equal:
//!
//! 1. On one end of the spectrum, it would be sound to spill once, immediately
//!    after defining the value, however if not all control paths require the
//!    spill, then we've pessimized the runtime of those paths by introducing a
//!    partial redundancy (some code that always executes but is not always
//!    used).
//!
//! 2. On the other end of the spectrum, we could insert a spill at the latest
//!    point possible before each reload. This avoids as much partial redundancy
//!    as possible, but emits a spill for every control-flow path to a reload in
//!    the worst case, inflating code size.
//!
//! Additionally, we'd like to place spills on cold paths and outside loops
//! whenever possible.
//!
//! This pass starts from somewhere near the (2) side of the spectrum and then
//! pushes spills backwards (up the dominator tree) towards (1). This means we
//! start from minimal partial redundancy and then try to improve our placements
//! by coalescing and removing redundant spills as much as we can.
//!
//! Concretely, what this pass does is, for each stack-alocated span, walk up
//! the dominator tree to the first legal placement of the spill that is in the
//! same region as the value's definition, and then keep hoisting it up while
//! our current block's immediate dominator has only one successor (this block)
//! and it is legal to place the spill in the immediate dominator. This
//! prioritizes never spilling inside loops (via the region guards) and then
//! avoiding introducing new partial redundancies while lifting spills up the
//! dominator tree, where they can deduplicate with other spills. (Ideally we
//! would walk up the dominator tree until the stack-allocated span's block no
//! longer post-dominates the current block, but we don't have a post-dominator
//! tree here.)
//!
//! A union-find over blocks records the site each walked block resolved to, so
//! a later walk short-cuts upon reaching an earlier walk's trail and we
//! collapse duplicate spills as they appear.
//!
//! We could additionally post-process our spills to remove any dominated by
//! another, but we don't do that here. Move elimination will remove these
//! redundant spills, along with any other redundant move.

use crate::{
    Block, Entity as _, Val,
    context::ContextInner,
    counts::Counts,
    entity::{EntityRepr, EntitySet, Region, SecondaryMap},
    error::IResult,
    events::EventsLog,
    input::{
        DefUse, Input, InputBlock as _, InputFunction, InputInst as _, InputValue as _, Position,
        RematCost,
    },
    live_ranges::{LiveBundle, LivePoint, LiveRanges, LiveSpan, Use},
    liveness::block_first_inst,
    output::OutputInner,
    region_allocation::RegionAllocation,
    region_tree::RegionTree,
    rpo::Rpo,
    spill_slot_allocation::SpillSlots,
    timing::Timing,
    union_find::UnionFind,
};
use alloc::vec::Vec;

/// Run the spill placement pass.
pub(crate) fn place_spills<E>(
    context: &mut ContextInner<E>,
    input: &Input<'_, impl InputFunction>,
) -> IResult<()>
where
    E: EntityRepr,
{
    let _timing = Timing::new("place spills");

    let ContextInner {
        counts,
        events,
        rpo,
        region_tree,
        live_ranges,
        region_allocation,
        spill_slots,
        spill_placement,
        output,
        ..
    } = context;

    spill_placement.place(
        input,
        counts,
        events,
        rpo,
        region_tree,
        live_ranges,
        region_allocation,
        spill_slots,
        output,
    )
}

/// One store of a spilled value into its stack slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SpillSite<E>
where
    E: EntityRepr,
{
    /// The program point to place this spill at.
    ///
    /// Note that this point does not necessarily name the block the spill
    /// belongs to. When the def is its block's terminator, the boundary just
    /// after it is the first point of the next block in layout order, and the
    /// spill goes on the defining block's outgoing edges. Use
    /// `SpillSite::block` instead, which reads the block out of `span`.
    point: LivePoint<E>,

    /// The span that holds the value in a register at `point`.
    span: LiveSpan<E>,
}

impl<E> SpillSite<E>
where
    E: EntityRepr,
{
    /// The program point to spill at.
    #[allow(dead_code, reason = "consumed by the phases that are still to come")]
    pub(crate) fn point(self) -> LivePoint<E> {
        self.point
    }

    /// The block that this spill site is in.
    #[cfg(test)]
    fn block(self, func: &impl InputFunction, live_ranges: &LiveRanges<E>) -> Block<E> {
        self.span.block(func, live_ranges)
    }

    /// The span holding the value in a register at this spill's point, and
    /// therefore the source of the spill.
    #[allow(dead_code, reason = "consumed by the phases that are still to come")]
    pub(crate) fn span(self) -> LiveSpan<E> {
        self.span
    }

    /// The value being spilled.
    #[allow(dead_code, reason = "consumed by the phases that are still to come")]
    pub(crate) fn val(self, live_ranges: &LiveRanges<E>) -> Val<E> {
        self.span.val(live_ranges)
    }
}

/// Where a value is defined.
#[derive(Clone, Copy, Debug)]
struct Def<E>
where
    E: EntityRepr,
{
    /// The program point the value is defined at.
    point: LivePoint<E>,

    /// What kind of definition this is, and whatever else that kind knows.
    kind: DefKind<E>,
}

#[derive(Clone, Copy, Debug)]
enum DefKind<E>
where
    E: EntityRepr,
{
    /// The value is a parameter of `Def::point`'s block.
    BlockParam {
        /// The span that holds the value where it is defined.
        ///
        /// Filled in by `place_value`.
        span: Option<LiveSpan<E>>,
    },

    /// The value is defined by an operand of `Def::point`'s instruction.
    InstResult { def: Use<E> },
}

impl<E> Def<E>
where
    E: EntityRepr,
{
    /// The block that defines the value.
    fn block(self, input: &Input<'_, impl InputFunction>) -> Block<E> {
        input
            .func
            .inst(self.point.inst().with_repr32())
            .block()
            .with_repr::<E>()
            .expect("every block index already fit in `E` in the earlier passes")
    }

    /// The span that holds the value where it is defined, if we know it yet.
    fn span(self, live_ranges: &LiveRanges<E>) -> Option<LiveSpan<E>> {
        match self.kind {
            DefKind::BlockParam { span } => span,
            DefKind::InstResult { def: def_use } => Some(def_use.span(live_ranges)),
        }
    }

    /// Where a spill in this definition's own block goes: as early in the block
    /// as the definition allows.
    fn spill_point(self) -> LivePoint<E> {
        match self.kind {
            // A block parameter is already defined at the block's entry, so the
            // spill goes there.
            DefKind::BlockParam { .. } => self.point,
            // Spill as soon as the definition has run.
            DefKind::InstResult { .. } => self.point.inst_boundary_after(),
        }
    }
}

/// Where each spilled value is spilled into its stack slot.
pub struct SpillPlacement<E>
where
    E: EntityRepr,
{
    /// The spills we decided to place: this pass's result.
    spills: Vec<SpillSite<E>>,

    /// The bundles that region allocation could not keep in a register.
    stack_bundles: EntitySet<LiveBundle<E>>,

    /// Where each spilled value is defined.
    defs: SecondaryMap<Val<E>, Option<Def<E>>>,

    /// Every span of every spilled value, ordered so that each value's spans
    /// are contiguous and in program order.
    spans: Vec<LiveSpan<E>>,

    /// For the value currently being placed, the register span that starts at
    /// the entry of each block that has one.
    ///
    /// This is the legality test for every block but the value's defining
    /// block, and it doubles as the spill's source span.
    legal: SecondaryMap<Block<E>, Option<LiveSpan<E>>>,

    /// For the value currently being placed, the site each already-walked block
    /// resolved to.
    union_find: UnionFind<Block<E>>,

    /// For the value currently being placed, the blocks that are spill sites.
    ///
    /// `union_find` cannot answer this on its own: a block that is its own root
    /// is either a site or a block no walk has reached yet.
    is_spill_site: EntitySet<Block<E>>,

    /// The same blocks as `is_spill_site`, in the order we found them.
    spill_site_blocks: Vec<Block<E>>,

    /// For the value currently being placed, the blocks it arrives in from
    /// nowhere.
    ///
    /// A predecessor carries the value across the edge in a span that holds it
    /// nowhere, so the value only lands in a register once the
    /// rematerialization at the block's entry has run, which is after any
    /// store we would place there.
    arrives_from_nowhere: EntitySet<Block<E>>,
}

impl<E> Default for SpillPlacement<E>
where
    E: EntityRepr,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<E> SpillPlacement<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        SpillPlacement {
            spills: Vec::new(),
            stack_bundles: EntitySet::new(),
            defs: SecondaryMap::new(None),
            spans: Vec::new(),
            legal: SecondaryMap::new(None),
            union_find: UnionFind::new(),
            is_spill_site: EntitySet::new(),
            spill_site_blocks: Vec::new(),
            arrives_from_nowhere: EntitySet::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            spills,
            stack_bundles,
            defs,
            spans,
            legal,
            union_find,
            is_spill_site,
            spill_site_blocks,
            arrives_from_nowhere,
        } = self;
        spills.clear();
        stack_bundles.reset();
        defs.reset();
        legal.reset();
        union_find.reset();
        debug_assert!(spans.is_empty());
        debug_assert!(is_spill_site.is_empty());
        debug_assert!(spill_site_blocks.is_empty());
        debug_assert!(arrives_from_nowhere.is_empty());
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            spills,
            stack_bundles,
            defs,
            spans,
            legal,
            union_find,
            is_spill_site,
            spill_site_blocks,
            arrives_from_nowhere,
        } = self;
        spills.is_empty()
            && stack_bundles.is_reset()
            && defs.is_reset()
            && spans.is_empty()
            && legal.is_reset()
            && union_find.is_reset()
            && is_spill_site.is_empty()
            && spill_site_blocks.is_empty()
            && arrives_from_nowhere.is_empty()
    }

    /// The spills we placed.
    #[allow(dead_code, reason = "consumed by the phases that are still to come")]
    pub(crate) fn spills(&self) -> &[SpillSite<E>] {
        &self.spills
    }

    /// Decide where to spill each spilled value into its slot.
    fn place(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        rpo: &Rpo<E>,
        region_tree: &RegionTree<E>,
        live_ranges: &LiveRanges<E>,
        region_allocation: &RegionAllocation<E>,
        spill_slots: &SpillSlots<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        debug_assert!(self.is_reset());

        for bundle in region_allocation.stack_bundles().iter().copied() {
            self.stack_bundles.insert(bundle);
        }

        let spilled = spill_slots.spilled();
        self.collect_block_param_defs(input, rpo, spilled, output)?;
        self.collect_spilled_value_spans(input, live_ranges, spilled);

        let spans = core::mem::take(&mut self.spans);

        for val_spans in spans.chunk_by(|a, b| a.val(live_ranges) == b.val(live_ranges)) {
            self.place_spills_for_value(
                input,
                counts,
                events,
                region_tree,
                live_ranges,
                spill_slots,
                val_spans,
            );
        }

        self.spans = spans;
        self.spans.clear();

        Ok(())
    }

    /// Find where every spilled block parameter is defined.
    fn collect_block_param_defs(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        rpo: &Rpo<E>,
        spilled: &EntitySet<Val<E>>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        for block in rpo.iter() {
            let input_block = input.func.block(block.with_repr32());

            // A block parameter is defined upon entry to its block.
            let first_inst = output.with_repr(block_first_inst(&input_block))?;
            let entry = LivePoint::new(first_inst, Position::Early);
            for param in input_block.params() {
                let val = output.with_repr(param)?;
                if spilled.contains(val) {
                    self.defs[val] = Some(Def {
                        point: entry,
                        kind: DefKind::BlockParam { span: None },
                    });
                }
            }
        }

        Ok(())
    }

    /// Collect every span of every spilled value (even spans where the value is
    /// not on the stack) and place them, sorted by value and then location, in
    /// `self.spans`. Additionally, record the instruction that defined each
    /// spilled value in `self.defs`, if any.
    fn collect_spilled_value_spans(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        live_ranges: &LiveRanges<E>,
        spilled: &EntitySet<Val<E>>,
    ) {
        for span in live_ranges.spans() {
            let val = span.val(live_ranges);
            if !spilled.contains(val) {
                continue;
            }

            for u in span.uses(live_ranges) {
                let point = u.point(live_ranges);
                let input_inst = input.func.inst(point.inst().with_repr32());
                if input_inst.operand(u.operand(live_ranges)).kind() == DefUse::Def {
                    debug_assert!(self.defs[val].is_none(), "SSA gives a value one def");
                    self.defs[val] = Some(Def {
                        point,
                        kind: DefKind::InstResult { def: u },
                    });
                }
            }

            self.spans.push(span);
        }

        self.spans.sort_unstable_by_key(|&span| {
            (
                span.val(live_ranges),
                span.start(live_ranges),
                span.end(live_ranges),
            )
        });
    }

    /// Place the spills for a spilled value, given all of that value's spans.
    fn place_spills_for_value(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        events: &mut EventsLog<E>,
        region_tree: &RegionTree<E>,
        live_ranges: &LiveRanges<E>,
        spill_slots: &SpillSlots<E>,
        val_spans: &[LiveSpan<E>],
    ) {
        let val = val_spans[0].val(live_ranges);
        debug_assert!(val_spans.iter().all(|&span| span.val(live_ranges) == val));

        let mut def = self.defs[val].expect("every spilled value is defined somewhere");
        let def_block = def.block(input);

        // A block parameter has no def operand, so use its first span (which
        // covers the start of the block).
        if let DefKind::BlockParam { span } = &mut def.kind {
            debug_assert!(span.is_none(), "we place each value's spills once");
            *span = val_spans.iter().copied().find(|&span| {
                span.start(live_ranges) <= def.point && def.point < span.end(live_ranges)
            });
            self.defs[val] = Some(def);
        }

        let def_span = def
            .span(live_ranges)
            .expect("a live value's definition is covered by one of its spans");

        // If defining the value writes it into its stack slot, it is already
        // spilled.
        if self.on_stack(def_span, live_ranges) {
            trace!("spill placement: {val:?} is defined on the stack; already spilled");
            return;
        }

        self.find_legal_spill_blocks(input, events, live_ranges, val_spans);

        // Spills belong in the region that defines the value: a legal block
        // in a nested region is inside a loop the definition is outside of, so
        // a spill there would run once per iteration.
        let def_region = def_block.region(region_tree);

        // Place the spill for each on-stack span.
        for &span in val_spans {
            if self.on_stack(span, live_ranges) {
                self.place_one_spill(
                    input,
                    region_tree,
                    def_block,
                    def_region,
                    span.block(input.func, live_ranges),
                );
            }
        }

        // Gather the deduplicated spill blocks and construct our `SpillSite`s
        // for them.
        for block in self.spill_site_blocks.drain(..) {
            let (point, span) = if block == def_block {
                (def.spill_point(), def_span)
            } else {
                let span = self.legal[block].expect("a site is a legal placement");
                (span.start(live_ranges), span)
            };

            trace!("spill placement: spill {val:?} in {block:?} at {point:?}");
            self.spills.push(SpillSite { point, span });
            counts.spills_placed.inc();
            event!(
                events,
                SpillPlaced {
                    val,
                    span,
                    at: point,
                    block,
                    slot: val
                        .stack_home(spill_slots)
                        .expect("a value we are spilling has a stack home"),
                }
            );
        }

        self.legal.reset();
        self.is_spill_site.reset();
        self.union_find.reset();
        self.arrives_from_nowhere.reset();
    }

    /// Find every block where it is legal to spill the associated value and
    /// record them in `self.legal`.
    ///
    /// This is every block where the value is live and in a register at the
    /// start of the block, before any of the block's own moves or
    /// rematerializations have run.
    fn find_legal_spill_blocks(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        events: &mut EventsLog<E>,
        live_ranges: &LiveRanges<E>,
        val_spans: &[LiveSpan<E>],
    ) {
        let val = val_spans[0].val(live_ranges);

        // Values that we can always rematerialize can be spilled whever we
        // want, so don't waste time or space on recording their legal spill
        // blocks.
        if input.func.value(val.with_repr32()).remat_cost() == Some(RematCost::AlwaysRemat) {
            return;
        }

        // Blocks the value arrives in from nowhere are not legal spill
        // locations because the rematerialization that puts the value in a
        // register runs at the block's entry, after the spill we would place
        // there.
        for &span in val_spans {
            let block = span.block(input.func, live_ranges);
            if span.end(live_ranges) != block.end_point(input)
                || !span
                    .bundle(live_ranges)
                    .unwrap()
                    .is_rematerialized(live_ranges)
            {
                continue;
            }
            for succ in input.func.block(block.with_repr32()).successors() {
                let succ = succ
                    .with_repr::<E>()
                    .expect("every block index already fit in `E` in the earlier passes");
                self.arrives_from_nowhere.insert(succ);
            }
        }

        let mut num_candidates = 0;
        let mut prev_block = None;
        for &span in val_spans {
            let block = span.block(input.func, live_ranges);
            if prev_block == Some(block) {
                continue;
            }
            prev_block = Some(block);

            if !self.on_stack(span, live_ranges)
                && !span
                    .bundle(live_ranges)
                    .unwrap()
                    .is_rematerialized(live_ranges)
                && span.start(live_ranges) == block.start_point(input)
                && !self.arrives_from_nowhere.contains(block)
            {
                self.legal[block] = Some(span);
                num_candidates += 1;
            }
        }

        // A second walk, so that every event can say how many candidates there
        // were in the end. Compiled away when nothing is listening.
        if cfg!(any(
            feature = "trace-log",
            debug_assertions,
            feature = "visualizer",
        )) {
            let mut prev_block = None;
            for &span in val_spans {
                let block = span.block(input.func, live_ranges);
                if prev_block == Some(block) {
                    continue;
                }
                prev_block = Some(block);

                if self.legal[block].is_some() {
                    event!(
                        events,
                        SpillBlockChosen {
                            val,
                            block,
                            num_candidates,
                        }
                    );
                }
            }
        }
    }

    /// Resolve the block of one on-stack span to the site that spills the value
    /// for it.
    fn place_one_spill(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        region_tree: &RegionTree<E>,
        def_block: Block<E>,
        def_region: Region<E>,
        stack_block: Block<E>,
    ) {
        let stack_block = self.union_find.find(stack_block);
        if self.is_spill_site.contains(stack_block) {
            // An earlier span of this value already walked from here.
            return;
        }

        let spill_block = self.first_legal_placement_up_dom_tree(
            input,
            region_tree,
            def_block,
            def_region,
            stack_block,
        );
        let spill_block = self.push_up_dom_tree_without_redundancy(input, def_block, spill_block);

        if self.is_spill_site.insert(spill_block) {
            self.spill_site_blocks.push(spill_block);
        }
    }

    /// Walk up the dominator tree from `stack_block` to the first block in
    /// the definition's region that a spill could be legally placed within.
    ///
    /// The defining block is always a legal placement and is trivially in its
    /// own region, so the walk never climbs past it and this method always
    /// terminates.
    fn first_legal_placement_up_dom_tree(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        region_tree: &RegionTree<E>,
        def_block: Block<E>,
        def_region: Region<E>,
        stack_block: Block<E>,
    ) -> Block<E> {
        let mut spill_block = stack_block;
        loop {
            spill_block = self.union_find.find(spill_block);
            debug_assert!(
                input
                    .func
                    .block(def_block.with_repr32())
                    .dominates(spill_block.with_repr32()),
                "the walk never climbs above the defining block",
            );

            // Keep climbing the dominator tree until we a legal spill location
            // that is also in the definition's region (i.e. outside of a loop).
            if self.is_legal_spill_block(spill_block, def_block)
                && spill_block.region(region_tree) == def_region
            {
                return spill_block;
            }

            let parent = idom(input, spill_block).expect(
                "the defining block is a legal placement in its own region and dominates every \
                 block the value is live in, so the walk stops before the dominator tree's root",
            );

            self.union_find.union(parent, spill_block);
            spill_block = parent;
        }
    }

    /// Keep pushing the spill block up the dominator tree until pushing any
    /// more would introduce partial redundancy.
    ///
    /// Doing this costs nothing and potentially deduplicates spills.
    fn push_up_dom_tree_without_redundancy(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        def_block: Block<E>,
        mut spill_block: Block<E>,
    ) -> Block<E> {
        while spill_block != def_block
            && let Some(parent) = idom(input, spill_block)
        {
            let parent = self.union_find.find(parent);

            // If the parent branches anywhere other than to our block, pushing
            // up any further might introduce partial redundancies.
            if input
                .func
                .block(parent.with_repr32())
                .successors()
                .any(|s| s != spill_block.with_repr32())
            {
                break;
            }

            if !self.is_legal_spill_block(parent, def_block) {
                break;
            }

            self.union_find.union(parent, spill_block);
            spill_block = parent;
        }

        spill_block
    }

    /// Can we spill the value into its slot in `block`?
    fn is_legal_spill_block(&self, block: Block<E>, def_block: Block<E>) -> bool {
        block == def_block || self.legal[block].is_some()
    }

    /// Did region allocation leave this span on the stack?
    fn on_stack(&self, span: LiveSpan<E>, live_ranges: &LiveRanges<E>) -> bool {
        let bundle = span.bundle(live_ranges).unwrap();
        self.stack_bundles.contains(bundle)
    }
}

/// The immediate dominator of `block`, or `None` for the entry block.
fn idom<E>(input: &Input<'_, impl InputFunction>, block: Block<E>) -> Option<Block<E>>
where
    E: EntityRepr,
{
    input
        .func
        .block(block.with_repr32())
        .immediate_dominator()
        .map(|idom| {
            idom.with_repr::<E>()
                .expect("every block index already fit in `E` in the earlier passes")
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        RegClass,
        context::Context,
        error::{Error, InternalError},
        input::OperandConstraint,
        test::{TestInput, TestMachine},
    };
    use core::sync::atomic::{AtomicUsize, Ordering};
    use mutatis::{
        check::{Check, CheckResult},
        mutators as m,
    };
    use std::{
        collections::{BTreeMap, BTreeSet},
        format,
        string::String,
        vec,
        vec::Vec,
    };

    #[cfg(feature = "visualizer")]
    use crate::events::Event as LoggedEvent;

    /// Run every phase up through spill placement.
    ///
    /// Returns `None` when register allocation itself gave up on this input,
    /// e.g. because the function needs more registers at once than the machine
    /// has; there are no spills to check in that case.
    fn place(test_input: &TestInput) -> Result<Option<Context>, String> {
        let mut context = Context::new();
        assert!(context.is_reset());

        let result = test_input.with_input(|input| -> IResult<()> {
            let context = &mut context.context32;
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
                } = &mut *context;
                let func = input.func;
                rpo.construct(func, dfs, output)?;
                region_tree.construct(func, counts, dfs, output)?;
                liveness.construct(func, counts, rpo, output)?;
                live_ranges.construct(input, counts, events, liveness, output)?;
            }
            crate::coalescing::coalesce(context, input)?;
            crate::region_allocation::region_allocate(context, input)?;
            crate::spill_slot_allocation::allocate_spill_slots(context, input)?;
            place_spills(context, input)
        });

        if result.is_err() {
            return match context.context32.output.take_error() {
                // Not every function can be allocated on every machine, and
                // that is not this pass's problem.
                InternalError::Error(Error::TooManyLiveRegs) => Ok(None),
                error => Err(format!("allocation failed: {error:?}")),
            };
        }

        Ok(Some(context))
    }

    /// Every placed spill was logged, against a value the log already said
    /// was going to the stack and a span that is still in a register there.
    #[cfg(feature = "visualizer")]
    #[test]
    fn every_spill_is_logged() -> CheckResult<TestInput> {
        Check::new()
            .iters(1_000)
            .run(|test_input: &TestInput| -> Result<(), String> {
                let Some(context) = place(test_input)? else {
                    return Ok(());
                };
                // A second build of the same input, only so that the checks
                // below can ask which block a point is in.
                test_input.with_input(|input| -> Result<(), String> {
                    let inner = &context.context32;
                    let live_ranges = &inner.live_ranges;
                    let spill_slots = &inner.spill_slots;

                    let mut on_stack: BTreeSet<LiveBundle<u32>> = BTreeSet::new();
                    let mut spilled: BTreeSet<Val<u32>> = BTreeSet::new();
                    let mut placed: Vec<(LivePoint<u32>, LiveSpan<u32>)> = Vec::new();

                    for (_, event) in inner.events.iter() {
                        match *event {
                            LoggedEvent::BundleSpilledToStack { bundle, .. } => {
                                on_stack.insert(bundle);
                            }
                            LoggedEvent::ValueSpilled { val, .. } => {
                                spilled.insert(val);
                            }
                            LoggedEvent::SpillPlaced {
                                val,
                                span,
                                at,
                                block,
                                slot,
                            } => {
                                if span.val(live_ranges) != val {
                                    return Err(format!("{span:?} does not hold {val:?}"));
                                }
                                if Some(slot) != val.stack_home(spill_slots) {
                                    return Err(format!(
                                        "{val:?} was spilled to {slot:?}, but lives at {:?}",
                                        val.stack_home(spill_slots),
                                    ));
                                }
                                if block != span.block(input.func, live_ranges) {
                                    return Err(format!(
                                        "{span:?} is in {:?}, not {block:?}",
                                        span.block(input.func, live_ranges),
                                    ));
                                }
                                if !spilled.contains(&val) {
                                    return Err(format!(
                                        "{val:?} is spilled at {at:?}, but was never logged as \
                                         going to the stack"
                                    ));
                                }
                                placed.push((at, span));
                            }
                            LoggedEvent::SpillBlockChosen { num_candidates, .. } => {
                                if num_candidates == 0 {
                                    return Err(String::from(
                                        "a legal spill block was logged with no candidates",
                                    ));
                                }
                            }
                            _ => {}
                        }
                    }

                    // Every spill the pass recorded was logged, and nothing else
                    // was.
                    let mut want: Vec<(LivePoint<u32>, LiveSpan<u32>)> = inner
                        .spill_placement
                        .spills()
                        .iter()
                        .map(|site| (site.point, site.span))
                        .collect();
                    want.sort_unstable();
                    placed.sort_unstable();
                    if placed != want {
                        return Err(format!("logged spills {placed:?}, but placed {want:?}"));
                    }

                    // And each one names the span that still holds the value
                    // in a register there, which is what the store reads from.
                    for &(_, span) in &placed {
                        let bundle = span
                            .bundle(live_ranges)
                            .expect("a live span belongs to a bundle");
                        if on_stack.contains(&bundle) {
                            return Err(format!(
                                "{span:?} is already on the stack in {bundle:?}, so there is \
                                 nothing to store from"
                            ));
                        }
                    }

                    Ok(())
                })
            })
    }

    /// What a run of the property check below saw, so that it can tell whether
    /// its inputs ever reached the cases it is meant to be about.
    #[derive(Default)]
    struct Seen {
        spills: usize,
        merge_param_spills: usize,
        spills_hoisted_out_of_a_region: usize,
    }

    /// The inputs the property check starts from.
    fn seeds() -> Vec<TestInput> {
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();
        let group_class = RegClass::try_new(usize::from(TestMachine::GROUP_CLASS)).unwrap();
        vec![
            TestInput::default(),
            // A merge block's parameter that spills: the spill has to land in
            // the block itself, not on one of the edges into it.
            TestInput::with_spilled_merge_param(),
            TestInput::with_use_constraints(&[OperandConstraint::Reg(class)]),
            TestInput::with_use_constraints(&[OperandConstraint::Stack]),
            TestInput::with_use_constraints(&[
                OperandConstraint::Stack,
                OperandConstraint::Reg(class),
            ]),
            TestInput::with_group_use_constraints(&[
                OperandConstraint::Stack,
                OperandConstraint::Reg(group_class),
            ]),
            TestInput::with_reuse_def(OperandConstraint::Any),
            TestInput::with_block_arg_constraints(OperandConstraint::Any, OperandConstraint::Stack),
            TestInput::with_stack_param_and_arg(),
            TestInput::with_a_value_spilled_inside_a_loop(),
        ]
    }

    /// Place the spills for `test_input` and check every property the placement
    /// is supposed to have.
    ///
    /// The dominance oracle is the test harness's own dominator tree, and the
    /// definitions are read back out of the operands, so neither is the pass's
    /// own bookkeeping repeated back at itself.
    fn check_placement(test_input: &TestInput) -> Result<Seen, String> {
        let Some(mut context) = place(test_input)? else {
            return Ok(Seen::default());
        };

        let seen = test_input.with_input(|input| -> Result<Seen, String> {
            let ctx = &context.context32;
            let func = input.func;
            let live_ranges = &ctx.live_ranges;
            let dominators = test_input.func.dominators();
            // Regions come from the region tree, which is a different pass's
            // output rather than this one's bookkeeping repeated back at
            // itself, and has property checks of its own.
            let region_tree = &ctx.region_tree;

            // How many spills the region guard actually lifted out of a loop.
            let mut hoisted_out_of_a_region = 0;

            let stack_bundles: BTreeSet<LiveBundle<u32>> = ctx
                .region_allocation
                .stack_bundles()
                .iter()
                .copied()
                .collect();
            let on_stack = |span: LiveSpan<u32>| {
                span.bundle(live_ranges)
                    .is_some_and(|bundle| stack_bundles.contains(&bundle))
            };
            let block_of = |span: LiveSpan<u32>| func.inst(span.start(live_ranges).inst()).block();
            let entry_of = |block: Block| {
                LivePoint::new(block_first_inst(&func.block(block)), Position::Early)
            };

            // Where each value is defined, taken from the operands.
            let mut def_block: BTreeMap<Val<u32>, Block> = BTreeMap::new();
            let mut def_point: BTreeMap<Val<u32>, LivePoint<u32>> = BTreeMap::new();
            // Where a spill in the defining block belongs: right after the def
            // instruction, or at the block's entry for a block parameter.
            let mut def_spill: BTreeMap<Val<u32>, LivePoint<u32>> = BTreeMap::new();
            for (block, input_block) in func.blocks() {
                for param in input_block.params() {
                    def_block.insert(param, block);
                    def_point.insert(param, entry_of(block));
                    def_spill.insert(param, entry_of(block));
                }
                for (inst, input_inst) in input_block.insts() {
                    for operand in input_inst.operands() {
                        if let (DefUse::Def, Some(val)) = (operand.kind(), operand.val()) {
                            let point = LivePoint::new(inst, operand.pos());
                            def_block.insert(val, block);
                            def_point.insert(val, point);
                            def_spill.insert(val, point.inst_boundary_after());
                        }
                    }
                }
            }

            let mut spans_of: BTreeMap<Val<u32>, Vec<LiveSpan<u32>>> = BTreeMap::new();
            for span in live_ranges.spans() {
                spans_of
                    .entry(span.val(live_ranges))
                    .or_default()
                    .push(span);
            }
            for spans in spans_of.values_mut() {
                spans
                    .sort_unstable_by_key(|&span| (span.start(live_ranges), span.end(live_ranges)));
            }

            let mut sites_of: BTreeMap<Val<u32>, Vec<SpillSite<u32>>> = BTreeMap::new();
            for &site in ctx.spill_placement.spills() {
                sites_of
                    .entry(site.val(live_ranges))
                    .or_default()
                    .push(site);
            }

            // Property 1: we only ever spill a value that was spilled.
            for (val, sites) in &sites_of {
                if !ctx.spill_slots.spilled().contains(*val) {
                    return Err(format!(
                        "{val:?} was never spilled, but we placed the spills {sites:?} for it"
                    ));
                }
            }

            let no_sites = Vec::new();
            for val in ctx.spill_slots.spilled().iter() {
                let no_spans = Vec::new();
                let spans = spans_of.get(&val).unwrap_or(&no_spans);
                let sites = sites_of.get(&val).unwrap_or(&no_sites);

                let Some(&def_b) = def_block.get(&val) else {
                    return Err(format!("{val:?} is spilled but is never defined"));
                };
                let def_p = def_point[&val];
                let def_span = spans.iter().copied().find(|&span| {
                    span.start(live_ranges) <= def_p && def_p < span.end(live_ranges)
                });

                // Property 2: a value that is defined straight into its slot is
                // already there, and needs no spill of its own.
                if def_span.is_some_and(on_stack) {
                    if !sites.is_empty() {
                        return Err(format!(
                            "{val:?} is defined on the stack, but we still placed the spills \
                             {sites:?} for it"
                        ));
                    }
                    continue;
                }

                for &site in sites {
                    // Property 3: a spill reads a register, and reads it at a
                    // point where the span it names holds the value.
                    if on_stack(site.span()) {
                        return Err(format!(
                            "the spill {site:?} for {val:?} reads a span that is on the stack"
                        ));
                    }
                    let (start, end) =
                        (site.span().start(live_ranges), site.span().end(live_ranges));
                    if site.point() < start || site.point() > end {
                        return Err(format!(
                            "the spill {site:?} for {val:?} is at {:?}, outside the span \
                             {start:?}..{end:?} it reads",
                            site.point(),
                        ));
                    }

                    // Property 4: a spill goes as early in its block as it
                    // can: just past the def in the defining block, and at the
                    // block's entry everywhere else.
                    let block = site.block(func, live_ranges);
                    let expected = if block == def_b {
                        def_spill[&val]
                    } else {
                        entry_of(block)
                    };
                    if site.point() != expected {
                        return Err(format!(
                            "the spill {site:?} for {val:?} is at {:?} in {block:?}, but belongs                              at {expected:?}",
                            site.point(),
                        ));
                    }

                    // Property 5: a spill is dominated by the definition of the
                    // value it spills.
                    if !def_b.dominates(dominators, site.block(func, live_ranges)) {
                        return Err(format!(
                            "the spill {site:?} for {val:?} is not dominated by its definition \
                             in {def_b:?}"
                        ));
                    }

                    // Property 7: a spill is in the same region as the
                    // definition of the value it spills, so it never sits
                    // inside a loop the definition is outside of.
                    let site_region = site.block(func, live_ranges).region(region_tree);
                    if site_region != def_b.region(region_tree) {
                        return Err(format!(
                            "the spill {site:?} for {val:?} is in {site_region:?}, but its \
                             definition in {def_b:?} is in {:?}",
                            def_b.region(region_tree),
                        ));
                    }
                }

                // Property 6: every point where the value is read from its
                // slot has a spill before it on every path. Dominance is what
                // makes this "on every path" and not "on some path", which is
                // what rules out a spill that only some of a merge block's
                // predecessors reach.
                for &span in spans {
                    if !on_stack(span) {
                        continue;
                    }
                    let block = block_of(span);
                    let covered = sites.iter().any(|&site| {
                        site.block(func, live_ranges).dominates(dominators, block)
                            && (site.block(func, live_ranges) != block
                                || site.point() <= span.start(live_ranges))
                    });
                    if !covered {
                        return Err(format!(
                            "{val:?} is on the stack in {block:?} at {:?}, but none of its \
                             spills {sites:?} reaches that point",
                            span.start(live_ranges),
                        ));
                    }

                    // The value is on the stack inside a region its definition
                    // is outside of, and Property 7 just said the spill is out
                    // there with the definition: the region guard earned its
                    // keep here.
                    if block.region(region_tree) != def_b.region(region_tree) {
                        hoisted_out_of_a_region += 1;
                    }
                }
            }

            // Not a property of the pass, but of the inputs: the counts that
            // let the property check say its inputs were not all trivial.
            let mut seen = Seen {
                spills: ctx.spill_placement.spills().len(),
                merge_param_spills: 0,
                spills_hoisted_out_of_a_region: hoisted_out_of_a_region,
            };
            for &site in ctx.spill_placement.spills() {
                let val = site.val(live_ranges);
                let merge_param = func.blocks().any(|(_, block)| {
                    block.len_predecessors() > 1 && block.params().any(|param| param == val)
                });
                if merge_param {
                    seen.merge_param_spills += 1;
                }
            }

            Ok(seen)
        })?;

        // Property 8: the pass leaves nothing behind that a reset does not
        // clean up.
        context.reset();
        assert!(context.is_reset());

        Ok(seen)
    }

    /// Running the whole pipeline, up to and including this pass, never panics
    /// and never trips a debug assertion.
    #[test]
    fn the_whole_pipeline_runs() -> CheckResult<TestInput> {
        Check::new()
            .iters(10_000)
            .run(|test_input: &TestInput| -> Result<(), String> {
                place(test_input)?;
                Ok(())
            })
    }

    /// The placement has every property it is supposed to have. The counters
    /// make sure the inputs really reached the cases those properties are
    /// about, so that a run that checks nothing cannot pass.
    ///
    /// The counting happens inside this check rather than in a check of its
    /// own: a separate check is a separate random walk, and its coverage would
    /// say nothing about the inputs *this* one saw.
    #[test]
    fn spill_placement_properties() -> CheckResult<TestInput> {
        static SPILLS: AtomicUsize = AtomicUsize::new(0);
        static MERGE_PARAM_SPILLS: AtomicUsize = AtomicUsize::new(0);
        static HOISTED_OUT_OF_A_REGION: AtomicUsize = AtomicUsize::new(0);
        SPILLS.store(0, Ordering::Relaxed);
        MERGE_PARAM_SPILLS.store(0, Ordering::Relaxed);
        HOISTED_OUT_OF_A_REGION.store(0, Ordering::Relaxed);

        let result = Check::new().iters(10_000).run_with(
            m::default::<TestInput>(),
            seeds(),
            |test_input: &TestInput| -> Result<(), String> {
                let seen = check_placement(test_input)?;
                SPILLS.fetch_add(seen.spills, Ordering::Relaxed);
                MERGE_PARAM_SPILLS.fetch_add(seen.merge_param_spills, Ordering::Relaxed);
                HOISTED_OUT_OF_A_REGION
                    .fetch_add(seen.spills_hoisted_out_of_a_region, Ordering::Relaxed);
                Ok(())
            },
        );

        if result.is_ok() {
            for (what, counter) in [
                ("spill", &SPILLS),
                ("spilled parameter of a merge block", &MERGE_PARAM_SPILLS),
                (
                    "spill hoisted out of the region it is read in",
                    &HOISTED_OUT_OF_A_REGION,
                ),
            ] {
                assert!(
                    counter.load(Ordering::Relaxed) > 0,
                    "no input produced a {what}, so the placement properties are vacuous",
                );
            }
        }

        result
    }

    /// Nothing spills when every use can be satisfied in a register, so there
    /// is nothing to spill.
    #[test]
    fn no_spills_when_nothing_spills() {
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();
        let test_input = TestInput::with_use_constraints(&[OperandConstraint::Reg(class)]);
        let context = place(&test_input).unwrap().unwrap();
        assert!(context.context32.spill_placement.spills().is_empty());
    }

    /// A spilled block parameter is spilled inside its own block, so the spill
    /// runs no matter which predecessor we came from.
    ///
    /// A block parameter is really defined on the edges into its block, so the
    /// shape to worry about is a spill that lands on one of those edges: the
    /// slot would then be filled along that predecessor and left stale along
    /// the others. The spill goes at the parameter's block's entry instead,
    /// which every edge into the block reaches.
    #[test]
    fn a_block_parameter_is_spilled_in_its_own_block() {
        let test_input = TestInput::with_spilled_merge_param();
        let context = place(&test_input).unwrap().unwrap();

        test_input.with_input(|input| {
            let ctx = &context.context32;
            let func = input.func;
            let live_ranges = &ctx.live_ranges;

            let param = Val::<u32>::try_new(1).unwrap();
            let merge = Block::<u32>::try_new(3).unwrap();
            assert!(func.block(merge).params().any(|p| p == param));
            assert_eq!(
                func.block(merge).len_predecessors(),
                2,
                "the point of this input is a parameter with more than one edge into it",
            );
            assert!(ctx.spill_slots.spilled().contains(param));

            let sites = ctx.spill_placement.spills();
            assert_eq!(sites.len(), 1, "expected a single spill, got {sites:?}");
            let site = sites[0];
            assert_eq!(site.val(live_ranges), param);
            assert_eq!(site.block(func, live_ranges), merge);
            assert_eq!(
                site.point(),
                LivePoint::new(block_first_inst(&func.block(merge)), Position::Early),
                "the spill belongs at the merge block\'s entry, not on an edge into it",
            );
        });
    }

    /// A value defined outside a loop and read off the stack inside it is
    /// spilled outside the loop, not once per iteration.
    ///
    /// The loop header is a legal placement and is the first one the walk up
    /// the dominator tree meets, and the defining block's branch has a second
    /// successor, so the single-successor hoist cannot lift the spill out on
    /// its own. Only the region guard does.
    #[test]
    fn a_spill_is_hoisted_out_of_a_loop() {
        let test_input = TestInput::with_a_value_spilled_inside_a_loop();
        let context = place(&test_input).unwrap().unwrap();

        test_input.with_input(|input| {
            let ctx = &context.context32;
            let func = input.func;
            let live_ranges = &ctx.live_ranges;

            let val = Val::<u32>::try_new(0).unwrap();
            let def_block = Block::<u32>::try_new(0).unwrap();
            let header = Block::<u32>::try_new(1).unwrap();
            let body = Block::<u32>::try_new(2).unwrap();

            assert!(ctx.spill_slots.spilled().contains(val));

            // The premise of the test: the loop really is a region of its own,
            // and the definition is outside it.
            let region_tree = &ctx.region_tree;
            assert_eq!(header.region(region_tree), body.region(region_tree));
            assert_ne!(
                def_block.region(region_tree),
                header.region(region_tree),
                "the loop has to be its own region for the guard to have anything to say",
            );

            // And the loop header really is a legal placement, so that the
            // walk has something to climb past. Without this the test would
            // pass for the wrong reason.
            let stack_bundles: BTreeSet<LiveBundle<u32>> = ctx
                .region_allocation
                .stack_bundles()
                .iter()
                .copied()
                .collect();
            let header_is_legal = live_ranges.spans().any(|span| {
                span.val(live_ranges) == val
                    && span.block(func, live_ranges) == header
                    && span.start(live_ranges) == header.start_point(input)
                    && !span
                        .bundle(live_ranges)
                        .is_some_and(|bundle| stack_bundles.contains(&bundle))
            });
            assert!(
                header_is_legal,
                "the loop header has to be a legal placement for the guard to have to skip it",
            );

            let sites = ctx.spill_placement.spills();
            assert_eq!(sites.len(), 1, "expected a single spill, got {sites:?}");
            let site = sites[0];
            assert_eq!(site.val(live_ranges), val);
            assert_eq!(
                site.block(func, live_ranges),
                def_block,
                "the spill belongs outside the loop, in the defining block",
            );
            assert_eq!(
                site.point(),
                LivePoint::new(block_first_inst(&func.block(def_block)), Position::Late)
                    .inst_boundary_after(),
                "and as early in that block as the definition allows",
            );
        });
    }

    /// A block whose span of the value holds it nowhere at all is not a place
    /// we can spill it from: a stack-constrained use gives the value a slot,
    /// while the crossing piece is at its block's entry and not on the stack --
    /// everything the walk used to ask for -- with nothing there to store.
    #[test]
    fn no_spill_from_a_span_that_holds_the_value_nowhere() {
        let mut test_input = TestInput::with_a_value_read_on_the_stack_past_a_crowded_block();
        test_input.set_remat_costs(Some(RematCost::CheaperThanReload));
        let context = place(&test_input).unwrap().unwrap();

        test_input.with_input(|input| {
            let ctx = &context.context32;
            let func = input.func;
            let live_ranges = &ctx.live_ranges;

            let val = Val::<u32>::try_new(0).unwrap();
            let crowded = Block::<u32>::try_new(1).unwrap();
            assert!(
                ctx.spill_slots.spilled().contains(val),
                "the stack-constrained read has to give the value a slot, or there is no spill \
                 to place at all",
            );

            // The premise: the crossing piece is the shape the walk would
            // otherwise pick up.
            let nowhere = live_ranges
                .spans()
                .filter(|span| {
                    span.val(live_ranges) == val && span.block(func, live_ranges) == crowded
                })
                .collect::<Vec<_>>();
            assert_eq!(
                nowhere.len(),
                1,
                "expected one crossing piece, got {nowhere:?}"
            );
            let nowhere = nowhere[0];
            let bundle = nowhere
                .bundle(live_ranges)
                .expect("a live span belongs to a bundle");
            assert!(bundle.is_rematerialized(live_ranges));
            assert!(bundle.reg_allocation(live_ranges).is_none());
            assert_eq!(nowhere.start(live_ranges), crowded.start_point(input));

            // So nothing is spilled there, and every spill reads a register.
            for site in ctx.spill_placement.spills() {
                assert_ne!(
                    site.block(func, live_ranges),
                    crowded,
                    "{site:?} stores the value from a span that does not hold it",
                );
                assert!(
                    site.span
                        .bundle(live_ranges)
                        .expect("a live span belongs to a bundle")
                        .reg_allocation(live_ranges)
                        .is_some(),
                    "{site:?} has no register to store from",
                );
            }

            // And it was never even a candidate.
            #[cfg(feature = "visualizer")]
            for (_, event) in ctx.events.iter() {
                if let LoggedEvent::SpillBlockChosen { block, .. } = *event {
                    assert_ne!(block, crowded, "{crowded:?} is not a legal spill block");
                }
            }
        });
    }

    /// A block the value arrives in from a span that holds it nowhere is no
    /// better: the store would go at that block's start, sharing the position
    /// with the incoming edge's moves, and the rematerialization that puts the
    /// value in a register there runs after every one of them.
    #[test]
    fn no_spill_where_the_value_arrives_from_nowhere() {
        let mut test_input = TestInput::with_a_value_stored_where_it_arrives_from_nowhere();
        test_input.set_remat_costs(Some(RematCost::CheaperThanReload));
        let context = place(&test_input).unwrap().unwrap();

        test_input.with_input(|input| {
            let ctx = &context.context32;
            let func = input.func;
            let live_ranges = &ctx.live_ranges;

            let val = Val::<u32>::try_new(0).unwrap();
            let def_block = Block::<u32>::try_new(0).unwrap();
            let arrival = Block::<u32>::try_new(1).unwrap();
            assert!(
                ctx.spill_slots.spilled().contains(val),
                "the stack-constrained read has to give the value a slot, or there is no spill \
                 to place at all",
            );

            // The premise: the value leaves its defining block in a piece that
            // holds it nowhere, and the next block takes it from there.
            let crossing = live_ranges
                .spans()
                .filter(|span| {
                    span.val(live_ranges) == val
                        && span.block(func, live_ranges) == def_block
                        && span.end(live_ranges) == def_block.end_point(input)
                })
                .collect::<Vec<_>>();
            assert_eq!(
                crossing.len(),
                1,
                "expected one crossing piece, got {crossing:?}"
            );
            let bundle = crossing[0]
                .bundle(live_ranges)
                .expect("a live span belongs to a bundle");
            assert!(bundle.is_rematerialized(live_ranges));
            assert!(bundle.reg_allocation(live_ranges).is_none());

            // And the block it arrives in is otherwise everything the walk
            // looks for: a span at the block's entry, in a register.
            let arriving = live_ranges
                .spans()
                .filter(|span| {
                    span.val(live_ranges) == val
                        && span.block(func, live_ranges) == arrival
                        && span.start(live_ranges) == arrival.start_point(input)
                })
                .collect::<Vec<_>>();
            assert_eq!(
                arriving.len(),
                1,
                "expected one arriving piece, got {arriving:?}"
            );
            assert!(
                arriving[0]
                    .bundle(live_ranges)
                    .expect("a live span belongs to a bundle")
                    .reg_allocation(live_ranges)
                    .is_some(),
                "the arriving piece has to be in a register for the guard to have to skip it",
            );

            // So the store stays behind in the defining block, as early as the
            // definition allows.
            let sites = ctx.spill_placement.spills();
            assert_eq!(sites.len(), 1, "expected a single spill, got {sites:?}");
            let site = sites[0];
            assert_eq!(site.val(live_ranges), val);
            assert_eq!(
                site.block(func, live_ranges),
                def_block,
                "the spill belongs where the value still has a register",
            );
            assert_eq!(
                site.point(),
                LivePoint::new(block_first_inst(&func.block(def_block)), Position::Late)
                    .inst_boundary_after(),
            );

            // And the block it arrives in was never even a candidate.
            #[cfg(feature = "visualizer")]
            for (_, event) in ctx.events.iter() {
                if let LoggedEvent::SpillBlockChosen { block, .. } = *event {
                    assert_ne!(block, arrival, "{arrival:?} is not a legal spill block");
                }
            }
        });
    }

    /// A value whose only use must be on the stack is written straight into its
    /// slot by its defining instruction, so it needs no spill of its own.
    #[test]
    fn no_spill_when_the_definition_is_already_on_the_stack() {
        let test_input = TestInput::with_use_constraints(&[OperandConstraint::Stack]);
        let context = place(&test_input).unwrap().unwrap();
        let context = &context.context32;

        let val = Val::<u32>::try_new(0).unwrap();
        assert!(context.spill_slots.spilled().contains(val));
        assert!(context.spill_placement.spills().is_empty());
    }
}
