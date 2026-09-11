//! Everything the visualizer's JavaScript needs that is cheaper or more
//! reliable to compute here: per-entity and per-kind event indexes, the
//! parentage of split spans and bundles, and the histograms.
//!
//! All of it runs once, when the visualization is written, and never during
//! allocation.

use crate::{
    context::ContextInner,
    entity::{Block, Entity, EntityRepr, Inst, Region, SecondaryMap, Val},
    events::{EntityRef, Event, EventIndex},
    input::{Input, InputBlock, InputFunction},
    live_ranges::{LiveBundle, LivePoint, LiveSpan, Use},
    machine::{Reg, RegClass, RegGroup},
    spill_slot_allocation::{SpillSlot, SpillSlotGroup},
};
use alloc::{
    collections::{BTreeMap, BTreeSet},
    format,
    string::String,
    vec::Vec,
};

/// Everything precomputed for the visualizer.
#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
pub(crate) struct Index<E>
where
    E: EntityRepr,
{
    /// The event indexes, which the visualization holds under its `index` key.
    #[serde(rename = "index")]
    pub(crate) indexes: EventIndexes<E>,

    /// The histograms, which it holds under its `histograms` key.
    pub(crate) histograms: Vec<Histogram>,
}

/// The ways the event log can be looked up by something other than position.
#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
#[serde(rename_all = "camelCase")]
pub(crate) struct EventIndexes<E>
where
    E: EntityRepr,
{
    /// The events each entity is named by, one typed map per entity kind.
    by_entity: ByEntity<E>,

    /// The events of each kind, keyed by the kind's name.
    ///
    /// Kind names are not entities, so this one stays string-keyed.
    by_kind: BTreeMap<&'static str, Vec<EventIndex>>,

    /// Where each span that came out of a split was cut out of.
    span_parents: SecondaryMap<LiveSpan<E>, Option<SpanParent<E>>>,

    /// Which bundle each bundle that came out of a split was cut out of.
    bundle_parents: SecondaryMap<LiveBundle<E>, Option<LiveBundle<E>>>,
}

/// Where a span came from, for the details pane's "split off of" field.
#[derive(Clone, Copy, Debug, serde::Serialize)]
#[serde(bound = "")]
pub(crate) struct SpanParent<E>
where
    E: EntityRepr,
{
    /// The span this one was cut out of.
    parent: LiveSpan<E>,

    /// Where the cut was.
    at: LivePoint<E>,
}

impl<E> EventIndexes<E>
where
    E: EntityRepr,
{
    /// Where `span` was cut out of, if it came out of a split.
    ///
    /// The IR skeleton repeats this so that the details pane can render a span
    /// without consulting the index.
    pub(crate) fn span_parent(&self, span: LiveSpan<E>) -> Option<SpanParent<E>> {
        self.span_parents[span]
    }

    /// Which bundle `bundle` was cut out of, if it came out of a split.
    pub(crate) fn bundle_parent(&self, bundle: LiveBundle<E>) -> Option<LiveBundle<E>> {
        self.bundle_parents[bundle]
    }
}

/// The per-entity indexes.
///
/// One typed map per entity kind an event can name, side by side under
/// `byEntity` and keyed by the entity type's own name, so that the lookup on
/// the JavaScript side is `secondary(byEntity[kind], index)`: no key
/// construction and no string parsing.
macro_rules! by_entity {
    ( $(
        $field:ident: $key:ty = $name:literal as $variant:ident;
    )* ) => {
        #[derive(Debug, serde::Serialize)]
        #[serde(bound = "")]
        struct ByEntity<E>
        where
            E: EntityRepr,
        {
            $(
                #[serde(rename = $name)]
                $field: SecondaryMap<$key, Vec<EventIndex>>,
            )*
        }

        impl<E> ByEntity<E>
        where
            E: EntityRepr,
        {
            fn new() -> Self {
                Self {
                    $( $field: SecondaryMap::new(Vec::new()), )*
                }
            }

            /// Record that `event` names `entity`.
            ///
            /// An event that names the same entity twice joins its list once:
            /// the pass runs in order, so a repeat is always the entry just
            /// pushed.
            fn push(&mut self, entity: EntityRef<E>, event: EventIndex) {
                let list = match entity {
                    $( EntityRef::$variant(key) => &mut self.$field[key], )*
                };
                if list.last() != Some(&event) {
                    list.push(event);
                }
            }

            /// Visit every list in this index, with the entity it belongs to.
            #[cfg(test)]
            fn for_each_list(&self, f: &mut impl FnMut(EntityRef<E>, &[EventIndex])) {
                $(
                    for (key, list) in self.$field.iter() {
                        f(EntityRef::$variant(key), list);
                    }
                )*
            }

            /// Those keys really are the entity types' own names, which is
            /// what lets the JavaScript look a kind up by the name it parsed
            /// out of a label.
            #[cfg(test)]
            fn check_names() {
                $( assert_eq!($name, <$key as crate::entity::VisualizedEntity>::KIND); )*
            }
        }
    };
}

by_entity! {
    val: Val<E> = "Val" as Val;
    span: LiveSpan<E> = "LiveSpan" as Span;
    bundle: LiveBundle<E> = "LiveBundle" as Bundle;
    block: Block<E> = "Block" as Block;
    region: Region<E> = "Region" as Region;
    inst: Inst<E> = "Inst" as Inst;
    use_: Use<E> = "Use" as Use;
    spill_slot: SpillSlot<E> = "SpillSlot" as SpillSlot;
    spill_slot_group: SpillSlotGroup<E> = "SpillSlotGroup" as SpillSlotGroup;
    reg: Reg = "Reg" as Reg;
    reg_group: RegGroup = "RegGroup" as RegGroup;
    reg_class: RegClass = "RegClass" as RegClass;
}

impl<E> Index<E>
where
    E: EntityRepr,
{
    /// Index `context`'s event log and summarize its results.
    pub(crate) fn build(input: &Input<'_, impl InputFunction>, context: &ContextInner<E>) -> Self {
        let mut by_entity = ByEntity::new();
        let mut by_kind = BTreeMap::<_, Vec<_>>::new();
        let mut span_parents = SecondaryMap::new(None);
        let mut bundle_parents = SecondaryMap::new(None);

        for (index, event) in context.events.iter() {
            event.visit_entities(&mut |entity| by_entity.push(entity, index));
            by_kind.entry(event.kind()).or_default().push(index);

            // Nothing in a span or a bundle records where it was split out of;
            // these events are the only source.
            match event {
                Event::SpanSplit {
                    parent, second, at, ..
                } => {
                    span_parents[*second] = Some(SpanParent {
                        parent: *parent,
                        at: *at,
                    });
                }
                Event::BundleSplit { parent, child, .. } => {
                    bundle_parents[*child] = Some(*parent);
                }
                _ => {}
            }
        }

        let histograms = histograms(input, context);

        // The visualizer's table of contents is keyed by these ids: a duplicate
        // would silently drop a chart, and an id the table of contents has
        // never heard of would land in its trailing "Other" group. The set is
        // pinned here, and `model.js` asserts that every id its grouping names
        // is one of these, which is the pair that keeps the two from drifting.
        let mut ids = BTreeSet::new();
        for histogram in &histograms {
            assert!(
                ids.insert(histogram.id),
                "duplicate histogram id {}",
                histogram.id,
            );
        }
        assert!(
            ids.iter().copied().eq(HISTOGRAM_IDS.iter().copied()),
            "the histograms are no longer {HISTOGRAM_IDS:?} but {ids:?}; \
             update `HISTOGRAM_IDS` here and the grouping in `visualizer/js/model.js`",
        );

        Self {
            indexes: EventIndexes {
                by_entity,
                by_kind,
                span_parents,
                bundle_parents,
            },
            histograms,
        }
    }
}

/// Every histogram id, in sorted order.
///
/// Pinned so that adding, removing, or renaming one is a deliberate act that
/// also visits the visualizer's grouping rather than a silent change nobody
/// notices until a chart is missing from the page.
const HISTOGRAM_IDS: &[&str] = &[
    "between-span-splits-per-bundle",
    "blocks-per-region",
    "bundles-per-region",
    "evictions-per-bundle",
    "incoming-edges-per-block",
    "incoming-edges-per-region",
    "instructions-per-bundle",
    "instructions-per-span",
    "live-in-spans-per-block",
    "live-in-values-per-block",
    "live-out-spans-per-block",
    "live-out-values-per-block",
    "outgoing-edges-per-block",
    "outgoing-edges-per-region",
    "parallel-moves-per-solve",
    "queue-pops-per-bundle",
    "queue-pops-per-region",
    "region-depth",
    "spans-per-bundle",
    "spans-per-value",
    "spills-per-bundle",
    "spills-per-value",
    "total-splits-per-bundle",
    "uses-per-bundle",
    "uses-per-span",
    "values-per-bundle",
    "within-span-splits-per-bundle",
];

/// How many buckets a histogram that does not get one per distinct value has.
const NUM_BUCKETS: u64 = 16;

/// A distribution of counts, summarized.
#[derive(Debug, serde::Serialize)]
pub(crate) struct Histogram {
    /// The anchor commit 12's table of contents links to.
    id: &'static str,

    /// The name to display.
    title: String,

    /// How many samples there are.
    count: u64,

    /// The smallest sample.
    min: u64,

    /// The largest.
    max: u64,

    /// The arithmetic mean, which is always finite: `serde_json` refuses to
    /// write a `NaN`.
    mean: f64,

    /// The median.
    p50: u64,

    /// The 90th percentile.
    p90: u64,

    /// The 99th percentile.
    p99: u64,

    /// The bars, covering `min..=max` with no gaps.
    buckets: Vec<Bucket>,
}

/// One bar of a [`Histogram`].
#[derive(Debug, serde::Serialize)]
struct Bucket {
    /// The lowest sample value this bar counts.
    lo: u64,

    /// The highest, inclusive.
    hi: u64,

    /// How many samples fell in it.
    count: u64,
}

impl Histogram {
    /// Summarize `samples`.
    ///
    /// No samples at all is legal — a function with no spills has no spills to
    /// distribute — and gives a zeroed histogram with no buckets for the
    /// JavaScript to render as "no samples".
    fn from_samples(id: &'static str, title: &str, mut samples: Vec<u64>) -> Self {
        let title = String::from(title);
        let count = u64::try_from(samples.len()).unwrap();
        if samples.is_empty() {
            return Self {
                id,
                title,
                count: 0,
                min: 0,
                max: 0,
                mean: 0.0,
                p50: 0,
                p90: 0,
                p99: 0,
                buckets: Vec::new(),
            };
        }

        samples.sort_unstable();
        let min = samples[0];
        let max = samples[samples.len() - 1];
        let sum = samples.iter().copied().map(u128::from).sum::<u128>();
        let mean = (sum as f64) / (count as f64);

        // Nearest rank, never interpolated: every sample is a count, and a
        // fractional "1.7 spans" reads as a bug.
        let percentile = |p: u64| {
            let rank = (p * count).div_ceil(100).max(1);
            samples[usize::try_from(rank - 1).unwrap()]
        };

        // A narrow distribution gets one bucket per distinct value; a wide one
        // gets a fixed number of them, so that its x-axis does not jump around
        // as the numbers change.
        let width = max - min + 1;
        let (width, num_buckets) = if width <= NUM_BUCKETS {
            (1, width)
        } else {
            (width.div_ceil(NUM_BUCKETS).next_power_of_two(), NUM_BUCKETS)
        };

        // Empty buckets are kept, for the same stable x-axis.
        let mut buckets = Vec::from_iter((0..num_buckets).map(|i| {
            let lo = min + i * width;
            Bucket {
                lo,
                hi: lo + width - 1,
                count: 0,
            }
        }));
        for sample in &samples {
            let i = usize::try_from((sample - min) / width).unwrap();
            buckets[i].count += 1;
        }

        Self {
            id,
            title,
            count,
            min,
            max,
            mean,
            p50: percentile(50),
            p90: percentile(90),
            p99: percentile(99),
            buckets,
        }
    }
}

/// One sample per entity of `K`, so that entities that were never counted
/// contribute their zero.
fn per_entity<K>(counts: &SecondaryMap<K, u64>, len: usize) -> Vec<u64>
where
    K: Entity,
{
    Vec::from_iter((0..len).map(|i| counts[K::try_new(i).unwrap()]))
}

/// Summarize the allocation, as the histograms tab displays it.
fn histograms<E>(input: &Input<'_, impl InputFunction>, context: &ContextInner<E>) -> Vec<Histogram>
where
    E: EntityRepr,
{
    let mut histograms = Vec::new();
    ir_histograms(input, context, &mut histograms);
    event_histograms(input, context, &mut histograms);
    histograms
}

/// The histograms of the final IR: the regions, blocks, spans, and bundles
/// that allocation ended up with.
fn ir_histograms<E>(
    input: &Input<'_, impl InputFunction>,
    context: &ContextInner<E>,
    histograms: &mut Vec<Histogram>,
) where
    E: EntityRepr,
{
    let func = input.func;
    let region_tree = &context.region_tree;
    let live_ranges = &context.live_ranges;
    let liveness = &context.liveness;

    let widen = |block: crate::Block| {
        block
            .with_repr::<E>()
            .expect("every block index already fit in `E` in the earlier passes")
    };

    let regions = Vec::from_iter(region_tree.pre_order_iter());

    // The region tree has no depth of its own, and adding one would be a
    // public API change for a single consumer. A pre-order walk reaches a
    // region only after its parent, so one pass is enough.
    let mut depth = SecondaryMap::<Region<E>, u64>::new(0);
    for &region in &regions {
        if let Some(parent) = region.parent(region_tree) {
            depth[region] = depth[parent] + 1;
        }
    }

    let mut bundles_per_region = SecondaryMap::<Region<E>, u64>::new(0);
    for bundle in live_ranges.bundles() {
        // `Region::bundles` only covers the bundles coalescing created, so the
        // count has to come from the bundles themselves.
        bundles_per_region[bundle.region(live_ranges)] += 1;
    }

    let mut region_incoming = Vec::new();
    let mut region_outgoing = Vec::new();
    for &region in &regions {
        let mut incoming = 0;
        let mut outgoing = 0;
        for block in region.blocks(region_tree) {
            let block = func.block(block.with_repr32());
            // A block belongs to exactly one region, so an edge leaves this
            // region exactly when its other end belongs to another.
            incoming += block
                .predecessors()
                .filter(|&pred| widen(pred).region(region_tree) != region)
                .count();
            outgoing += block
                .successors()
                .filter(|&succ| widen(succ).region(region_tree) != region)
                .count();
        }
        region_incoming.push(u64::try_from(incoming).unwrap());
        region_outgoing.push(u64::try_from(outgoing).unwrap());
    }

    histograms.push(Histogram::from_samples(
        "blocks-per-region",
        "Blocks per region",
        Vec::from_iter(
            regions
                .iter()
                .map(|region| u64::try_from(region.blocks(region_tree).len()).unwrap()),
        ),
    ));
    histograms.push(Histogram::from_samples(
        "region-depth",
        "Region depth",
        Vec::from_iter(regions.iter().map(|&region| depth[region])),
    ));
    histograms.push(Histogram::from_samples(
        "incoming-edges-per-region",
        "Incoming edges per region",
        region_incoming,
    ));
    histograms.push(Histogram::from_samples(
        "outgoing-edges-per-region",
        "Outgoing edges per region",
        region_outgoing,
    ));
    histograms.push(Histogram::from_samples(
        "bundles-per-region",
        "Bundles per region",
        Vec::from_iter(regions.iter().map(|&region| bundles_per_region[region])),
    ));

    // Values are live in and out of a block at value granularity, which
    // splitting does not invalidate, so these two come straight from liveness.
    // Their span-level counterparts do not; see below.
    let mut live_in_vals = Vec::new();
    let mut live_out_vals = Vec::new();
    let mut block_incoming = Vec::new();
    let mut block_outgoing = Vec::new();
    for (block, input_block) in func.blocks() {
        let block = widen(block);
        live_in_vals.push(u64::try_from(block.len_live_in(liveness)).unwrap());
        live_out_vals.push(u64::try_from(block.len_live_out(liveness)).unwrap());
        block_incoming.push(u64::try_from(input_block.len_predecessors()).unwrap());
        block_outgoing.push(u64::try_from(input_block.len_successors()).unwrap());
    }

    histograms.push(Histogram::from_samples(
        "incoming-edges-per-block",
        "Incoming edges per block",
        block_incoming,
    ));
    histograms.push(Histogram::from_samples(
        "outgoing-edges-per-block",
        "Outgoing edges per block",
        block_outgoing,
    ));
    histograms.push(Histogram::from_samples(
        "live-in-values-per-block",
        "Live-in values per block",
        live_in_vals,
    ));
    histograms.push(Histogram::from_samples(
        "live-out-values-per-block",
        "Live-out values per block",
        live_out_vals,
    ));

    // `Block::live_in_spans` and `Block::live_out_spans` are documented as
    // valid only before any span is split, which region allocation has long
    // since done by the time the index is built, so these are recomputed from
    // the final spans rather than read out of those stale maps. Do not
    // "simplify" this back to the accessors.
    let mut live_in_spans = SecondaryMap::<Block<E>, u64>::new(0);
    let mut live_out_spans = SecondaryMap::<Block<E>, u64>::new(0);
    let mut spans_per_val = SecondaryMap::<Val<E>, u64>::new(0);
    let mut span_insts = Vec::new();
    let mut span_uses = Vec::new();
    for span in live_ranges.spans() {
        let val = span.val(live_ranges);
        spans_per_val[val] += 1;
        span_insts.push(u64::try_from(span.len_insts(live_ranges)).unwrap());
        span_uses.push(u64::try_from(span.uses(live_ranges).len()).unwrap());

        // A span lies within one block, so it reaches that block's boundary or
        // no block's, and it is live across the boundary only if its value is.
        let block = span.block(func, live_ranges);
        if span.start(live_ranges) == block.start_point(input) && block.is_live_in(liveness, val) {
            live_in_spans[block] += 1;
        }
        if span.end(live_ranges) == block.end_point(input) && block.is_live_out(liveness, val) {
            live_out_spans[block] += 1;
        }
    }

    histograms.push(Histogram::from_samples(
        "live-in-spans-per-block",
        "Live-in spans per block",
        per_entity(&live_in_spans, func.len_blocks()),
    ));
    histograms.push(Histogram::from_samples(
        "live-out-spans-per-block",
        "Live-out spans per block",
        per_entity(&live_out_spans, func.len_blocks()),
    ));
    histograms.push(Histogram::from_samples(
        "spans-per-value",
        "Spans per value",
        per_entity(&spans_per_val, func.len_values()),
    ));
    histograms.push(Histogram::from_samples(
        "instructions-per-span",
        "Instructions per span",
        span_insts,
    ));
    histograms.push(Histogram::from_samples(
        "uses-per-span",
        "Uses per span",
        span_uses,
    ));

    let mut bundle_spans = Vec::new();
    let mut bundle_vals = Vec::new();
    let mut bundle_insts = Vec::new();
    let mut bundle_uses = Vec::new();
    for bundle in live_ranges.bundles() {
        let spans = bundle.spans(live_ranges);
        bundle_spans.push(u64::try_from(spans.len()).unwrap());
        bundle_vals.push(u64::try_from(bundle.num_vals(live_ranges)).unwrap());
        bundle_uses.push(
            spans
                .clone()
                .map(|span| u64::try_from(span.uses(live_ranges).len()).unwrap())
                .sum(),
        );

        // The union, not the sum: two spans of one bundle can share an
        // instruction, when the split that separated them fell inside one.
        let mut ranges = Vec::from_iter(spans.map(|span| {
            let first = span.start(live_ranges).inst().index();
            let last = span.end(live_ranges).prev_point().inst().index();
            (first, last)
        }));
        ranges.sort_unstable();
        let mut insts = 0;
        let mut counted_through = None;
        for (first, last) in ranges {
            let first = match counted_through {
                Some(through) if through >= first => through + 1,
                _ => first,
            };
            if first <= last {
                insts += last - first + 1;
                counted_through = Some(last);
            }
        }
        bundle_insts.push(u64::try_from(insts).unwrap());
    }

    histograms.push(Histogram::from_samples(
        "spans-per-bundle",
        "Spans per bundle",
        bundle_spans,
    ));
    histograms.push(Histogram::from_samples(
        "values-per-bundle",
        "Values per bundle",
        bundle_vals,
    ));
    histograms.push(Histogram::from_samples(
        "instructions-per-bundle",
        "Instructions per bundle",
        bundle_insts,
    ));
    histograms.push(Histogram::from_samples(
        "uses-per-bundle",
        "Uses per bundle",
        bundle_uses,
    ));
}

/// The histograms of what happened, rather than of what came out: one pass
/// over the event log, counting.
fn event_histograms<E>(
    input: &Input<'_, impl InputFunction>,
    context: &ContextInner<E>,
    histograms: &mut Vec<Histogram>,
) where
    E: EntityRepr,
{
    let func = input.func;
    let live_ranges = &context.live_ranges;
    let regions = Vec::from_iter(context.region_tree.pre_order_iter());

    let mut evictions = SecondaryMap::<LiveBundle<E>, u64>::new(0);
    let mut splits_within = SecondaryMap::<LiveBundle<E>, u64>::new(0);
    let mut splits_between = SecondaryMap::<LiveBundle<E>, u64>::new(0);
    let mut pops_per_bundle = SecondaryMap::<LiveBundle<E>, u64>::new(0);
    let mut pops_per_region = SecondaryMap::<Region<E>, u64>::new(0);
    let mut spills_per_val = SecondaryMap::<Val<E>, u64>::new(0);
    let mut spills_per_bundle = SecondaryMap::<LiveBundle<E>, u64>::new(0);
    let mut unbundled_spills = 0_u64;
    let mut parallel_moves = Vec::new();

    for (_, event) in context.events.iter() {
        match event {
            Event::BundleEvicted { bundle, .. } => evictions[*bundle] += 1,
            Event::BundleSplitWithinSpan { bundle, .. } => splits_within[*bundle] += 1,
            Event::BundleSplitBetweenSpans { bundle, .. } => splits_between[*bundle] += 1,
            Event::BundleQueuePopped { bundle, region, .. } => {
                pops_per_bundle[*bundle] += 1;
                pops_per_region[*region] += 1;
            }
            Event::SpillPlaced { val, span, .. } => {
                spills_per_val[*val] += 1;
                match span.bundle(live_ranges) {
                    Some(bundle) => spills_per_bundle[bundle] += 1,
                    // A span that was spilled outright never joined a bundle,
                    // so its spill belongs to none. Counted rather than
                    // silently dropped, and reported in the title below.
                    None => unbundled_spills += 1,
                }
            }
            Event::ParallelMoveBatchSolved {
                num_input_moves, ..
            } => parallel_moves.push(u64::try_from(*num_input_moves).unwrap()),
            _ => {}
        }
    }

    let num_bundles = live_ranges.len_bundles();
    histograms.push(Histogram::from_samples(
        "evictions-per-bundle",
        "Evictions per bundle",
        per_entity(&evictions, num_bundles),
    ));
    histograms.push(Histogram::from_samples(
        "total-splits-per-bundle",
        "Total splits per bundle",
        Vec::from_iter((0..num_bundles).map(|i| {
            let bundle = LiveBundle::try_new(i).unwrap();
            splits_within[bundle] + splits_between[bundle]
        })),
    ));
    histograms.push(Histogram::from_samples(
        "within-span-splits-per-bundle",
        "Within-span splits per bundle",
        per_entity(&splits_within, num_bundles),
    ));
    histograms.push(Histogram::from_samples(
        "between-span-splits-per-bundle",
        "Between-span splits per bundle",
        per_entity(&splits_between, num_bundles),
    ));
    histograms.push(Histogram::from_samples(
        "queue-pops-per-bundle",
        "Priority queue pops per bundle",
        per_entity(&pops_per_bundle, num_bundles),
    ));
    histograms.push(Histogram::from_samples(
        "queue-pops-per-region",
        "Priority queue pops per region",
        Vec::from_iter(regions.iter().map(|&region| pops_per_region[region])),
    ));
    histograms.push(Histogram::from_samples(
        "spills-per-value",
        "Spills per value",
        per_entity(&spills_per_val, func.len_values()),
    ));
    histograms.push(Histogram::from_samples(
        "spills-per-bundle",
        &if unbundled_spills == 0 {
            String::from("Spills per bundle")
        } else {
            format!("Spills per bundle ({unbundled_spills} in no bundle)")
        },
        per_entity(&spills_per_bundle, num_bundles),
    ));
    histograms.push(Histogram::from_samples(
        "parallel-moves-per-solve",
        "Parallel moves per solver invocation",
        parallel_moves,
    ));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        context::Context,
        error::{Error, InternalError},
        machine::RegSet,
        test::{TestFunction, TestInput},
    };
    use mutatis::check::{Check, CheckResult};
    use std::{collections::BTreeSet, string::ToString, vec};

    /// Allocate `test_input` and index the result.
    ///
    /// Returns `None` when the input is one the allocator legitimately cannot
    /// handle, which the caller should skip rather than fail on.
    fn with_indexed<R>(
        test_input: &TestInput,
        f: impl FnOnce(&Input<'_, TestFunction>, &ContextInner<u32>, &Index<u32>) -> R,
    ) -> Result<Option<R>, String> {
        let mut context = Context::new();
        test_input.with_input(|input| {
            if crate::run_inner(&mut context.context32, input).is_err() {
                return match context.context32.output.take_error() {
                    InternalError::Error(Error::TooManyLiveRegs) => Ok(None),
                    error => Err(format!("allocation failed: {error:?}")),
                };
            }
            let inner = &context.context32;
            let index = Index::build(input, inner);
            Ok(Some(f(input, inner, &index)))
        })
    }

    #[test]
    fn by_entity_keys_are_entity_kinds() {
        ByEntity::<u32>::check_names();
    }

    /// Every `byEntity` entry names an event that really does mention that
    /// entity, and every entity an event mentions has that event in its list.
    #[test]
    fn by_entity_is_exactly_the_events_that_name_each_entity() -> CheckResult<TestInput> {
        Check::new()
            .iters(1_000)
            .run(|test_input: &TestInput| -> Result<(), String> {
                with_indexed(test_input, |_input, inner, index| {
                    let len = inner.events.iter().count();
                    let mut error = None;
                    index.indexes.by_entity.for_each_list(&mut |entity, list| {
                        for &event in list {
                            let Some((_, logged)) = inner.events.iter().find(|&(i, _)| i == event)
                            else {
                                error.get_or_insert(format!(
                                    "{entity:?} names event {event:?}, but the log only has \
                                     {len} events"
                                ));
                                continue;
                            };
                            let mut found = false;
                            logged.visit_entities(&mut |named| found |= named == entity);
                            if !found {
                                error.get_or_insert(format!(
                                    "{entity:?} names event {event:?}, which does not mention it"
                                ));
                            }
                        }
                    });

                    for (event, logged) in inner.events.iter() {
                        logged.visit_entities(&mut |entity| {
                            let mut found = false;
                            index.indexes.by_entity.for_each_list(&mut |other, list| {
                                found |= other == entity && list.contains(&event);
                            });
                            if !found {
                                error.get_or_insert(format!(
                                    "event {event:?} mentions {entity:?}, which does not name it"
                                ));
                            }
                        });
                    }

                    match error {
                        Some(error) => Err(error),
                        None => Ok(()),
                    }
                })?
                .unwrap_or(Ok(()))
            })
    }

    /// The `byKind` lists partition the log, and each key is the kind of every
    /// event under it.
    #[test]
    fn by_kind_partitions_the_log() -> CheckResult<TestInput> {
        Check::new()
            .iters(1_000)
            .run(|test_input: &TestInput| -> Result<(), String> {
                with_indexed(test_input, |_input, inner, index| {
                    let mut seen = BTreeSet::new();
                    for (kind, list) in &index.indexes.by_kind {
                        for &event in list {
                            if !seen.insert(event) {
                                return Err(format!("event {event:?} is in two `byKind` lists"));
                            }
                            let logged = inner
                                .events
                                .iter()
                                .find(|&(i, _)| i == event)
                                .map(|(_, logged)| logged)
                                .ok_or_else(|| format!("no event {event:?}"))?;
                            if logged.kind() != *kind {
                                return Err(format!(
                                    "event {event:?} is a {} but is indexed under {kind}",
                                    logged.kind(),
                                ));
                            }
                        }
                    }
                    for (event, _) in inner.events.iter() {
                        if !seen.contains(&event) {
                            return Err(format!("event {event:?} is in no `byKind` list"));
                        }
                    }
                    Ok(())
                })?
                .unwrap_or(Ok(()))
            })
    }

    /// `kind` agrees with the serde tag, which is what the JavaScript sees.
    #[test]
    fn kind_agrees_with_the_serde_tag() -> CheckResult<TestInput> {
        Check::new()
            .iters(1_000)
            .run(|test_input: &TestInput| -> Result<(), String> {
                with_indexed(test_input, |_input, inner, _index| {
                    for (event, logged) in inner.events.iter() {
                        let json: serde_json::Value = serde_json::to_value(logged).unwrap();
                        let tag = json
                            .get("kind")
                            .and_then(|tag| tag.as_str())
                            .ok_or_else(|| format!("event {event:?} serialized without a tag"))?;
                        if tag != logged.kind() {
                            return Err(format!(
                                "event {event:?} serializes as {tag} but `kind` says {}",
                                logged.kind(),
                            ));
                        }
                    }
                    Ok(())
                })?
                .unwrap_or(Ok(()))
            })
    }

    /// Parents were created before their children, which also makes the parent
    /// maps acyclic.
    #[test]
    fn parents_come_before_their_children() -> CheckResult<TestInput> {
        Check::new()
            .iters(1_000)
            .run(|test_input: &TestInput| -> Result<(), String> {
                with_indexed(test_input, |_input, inner, index| {
                    for (span, parent) in index.indexes.span_parents.iter() {
                        let Some(parent) = parent else { continue };
                        if parent.parent.index() >= span.index() {
                            return Err(format!(
                                "{span:?} was split out of {:?}, which is not older",
                                parent.parent,
                            ));
                        }
                    }
                    for (bundle, parent) in index.indexes.bundle_parents.iter() {
                        let Some(parent) = parent else { continue };
                        if parent.index() >= bundle.index() {
                            return Err(format!(
                                "{bundle:?} was split out of {parent:?}, which is not older",
                            ));
                        }
                    }

                    // Nothing is silently dropped on the way into the maps.
                    for (_, event) in inner.events.iter() {
                        match event {
                            Event::SpanSplit { second, .. } => {
                                if index.indexes.span_parents[*second].is_none() {
                                    return Err(format!("{second:?} lost its parent"));
                                }
                            }
                            Event::BundleSplit { child, .. } => {
                                if index.indexes.bundle_parents[*child].is_none() {
                                    return Err(format!("{child:?} lost its parent"));
                                }
                            }
                            _ => {}
                        }
                    }

                    // Following a chain of parents terminates, at something
                    // that was constructed rather than split out.
                    let mut constructed_spans = BTreeSet::new();
                    let mut constructed_bundles = BTreeSet::new();
                    for (_, event) in inner.events.iter() {
                        match event {
                            Event::SpanConstructed { span, .. } => {
                                constructed_spans.insert(*span);
                            }
                            Event::BundleConstructed { bundle, .. } => {
                                constructed_bundles.insert(*bundle);
                            }
                            _ => {}
                        }
                    }
                    for span in inner.live_ranges.spans() {
                        let mut root = span;
                        while let Some(parent) = index.indexes.span_parents[root] {
                            root = parent.parent;
                        }
                        if !constructed_spans.contains(&root) {
                            return Err(format!(
                                "{span:?} climbs to {root:?}, which was never constructed"
                            ));
                        }
                    }
                    for bundle in inner.live_ranges.bundles() {
                        let mut root = bundle;
                        while let Some(parent) = index.indexes.bundle_parents[root] {
                            root = parent;
                        }
                        if !constructed_bundles.contains(&root) {
                            return Err(format!(
                                "{bundle:?} climbs to {root:?}, which was never constructed"
                            ));
                        }
                    }
                    Ok(())
                })?
                .unwrap_or(Ok(()))
            })
    }

    /// The statistics really do summarize the buckets, for every histogram of
    /// every allocation.
    #[test]
    fn histograms_are_consistent() -> CheckResult<TestInput> {
        Check::new()
            .iters(1_000)
            .run(|test_input: &TestInput| -> Result<(), String> {
                with_indexed(test_input, |_input, _inner, index| {
                    let mut ids = BTreeSet::new();
                    for histogram in &index.histograms {
                        check_histogram(histogram)?;
                        if !ids.insert(histogram.id) {
                            return Err(format!("duplicate histogram id {}", histogram.id));
                        }
                    }
                    Ok(())
                })?
                .unwrap_or(Ok(()))
            })
    }

    /// The invariants every histogram has, however it was built.
    fn check_histogram(histogram: &Histogram) -> Result<(), String> {
        let id = histogram.id;
        if !histogram.mean.is_finite() {
            return Err(format!("{id}'s mean is {}", histogram.mean));
        }
        let total = histogram
            .buckets
            .iter()
            .map(|bucket| bucket.count)
            .sum::<u64>();
        if total != histogram.count {
            return Err(format!(
                "{id} has {} samples but its buckets hold {total}",
                histogram.count,
            ));
        }
        if !(histogram.min <= histogram.p50
            && histogram.p50 <= histogram.p90
            && histogram.p90 <= histogram.p99
            && histogram.p99 <= histogram.max)
        {
            return Err(format!(
                "{id}'s percentiles are out of order: {histogram:?}"
            ));
        }
        if histogram.count != 0 {
            if histogram.mean < histogram.min as f64 || histogram.mean > histogram.max as f64 {
                return Err(format!("{id}'s mean is outside its range: {histogram:?}"));
            }
            let (first, last) = (
                histogram.buckets.first().unwrap(),
                histogram.buckets.last().unwrap(),
            );
            if first.lo != histogram.min || last.hi < histogram.max {
                return Err(format!(
                    "{id}'s buckets do not cover its range: {histogram:?}"
                ));
            }
            // The buckets tile the range with no gaps and no overlap, which is
            // what lets the chart draw them edge to edge.
            for pair in histogram.buckets.windows(2) {
                if pair[1].lo != pair[0].hi + 1 {
                    return Err(format!("{id}'s buckets do not tile: {histogram:?}"));
                }
            }
        }
        Ok(())
    }

    /// An input with no samples is not an error.
    #[test]
    fn an_empty_histogram_is_zeroed() {
        let histogram = Histogram::from_samples("empty", "Empty", Vec::new());
        check_histogram(&histogram).unwrap();
        assert_eq!(histogram.count, 0);
        assert_eq!(histogram.mean, 0.0);
        assert!(histogram.buckets.is_empty());
    }

    /// A hand-built distribution gets the statistics it should.
    #[test]
    fn known_samples_give_known_statistics() {
        // One sample of each value in 1..=4, so the nearest-rank percentiles
        // are the 2nd, 4th, and 4th samples.
        let histogram = Histogram::from_samples("small", "Small", vec![3, 1, 4, 2]);
        check_histogram(&histogram).unwrap();
        assert_eq!(histogram.count, 4);
        assert_eq!(histogram.min, 1);
        assert_eq!(histogram.max, 4);
        assert_eq!(histogram.mean, 2.5);
        assert_eq!((histogram.p50, histogram.p90, histogram.p99), (2, 4, 4));
        // Narrow enough for one bucket per value.
        assert_eq!(histogram.buckets.len(), 4);
        assert!(histogram.buckets.iter().all(|bucket| bucket.count == 1));

        // Wider than `NUM_BUCKETS`, so the values are grouped instead, into
        // buckets of the next power of two at least `100 / 16`.
        let histogram = Histogram::from_samples("wide", "Wide", Vec::from_iter(1..=100));
        check_histogram(&histogram).unwrap();
        assert_eq!(histogram.count, 100);
        assert_eq!(
            histogram.buckets.len(),
            usize::try_from(NUM_BUCKETS).unwrap()
        );
        assert_eq!((histogram.buckets[0].lo, histogram.buckets[0].hi), (1, 8));
        assert_eq!(histogram.buckets[0].count, 8);
        // The buckets run past the largest sample, and the ones past it are
        // kept rather than trimmed, so that the x-axis is stable.
        assert_eq!(
            (histogram.buckets[12].lo, histogram.buckets[12].hi),
            (97, 104)
        );
        assert_eq!(histogram.buckets[12].count, 4);
        assert_eq!(histogram.buckets[15].count, 0);

        // All one value: one bucket, and every percentile is it.
        let histogram = Histogram::from_samples("flat", "Flat", vec![7; 5]);
        check_histogram(&histogram).unwrap();
        assert_eq!((histogram.min, histogram.max, histogram.mean), (7, 7, 7.0));
        assert_eq!(histogram.buckets.len(), 1);
        assert_eq!(histogram.buckets[0].count, 5);
    }

    /// Registers are indexed too: the allocation an eviction moved and every
    /// register a bundle was hinted towards can be looked up.
    #[test]
    fn registers_are_indexed() -> CheckResult<TestInput> {
        Check::new()
            .iters(1_000)
            .run(|test_input: &TestInput| -> Result<(), String> {
                with_indexed(test_input, |_input, inner, index| {
                    let by_reg = &index.indexes.by_entity.reg;
                    let by_group = &index.indexes.by_entity.reg_group;
                    for (event, logged) in inner.events.iter() {
                        let regs: RegSet = match logged {
                            Event::BundleEvicted { .. } => {
                                // Every eviction is an allocation changing
                                // hands, and for a group class the allocation
                                // is a group, which is indexed as itself
                                // rather than as its members.
                                let mut regs = RegSet::new();
                                let mut groups = Vec::new();
                                logged.visit_entities(&mut |entity| match entity {
                                    EntityRef::Reg(reg) => {
                                        regs.insert(reg);
                                    }
                                    EntityRef::RegGroup(group) => groups.push(group),
                                    _ => {}
                                });
                                if regs.is_empty() && groups.is_empty() {
                                    return Err(format!(
                                        "eviction {event:?} names no register or group"
                                    ));
                                }
                                for group in groups {
                                    if !by_group[group].contains(&event) {
                                        return Err(format!(
                                            "{group:?} does not name event {event:?}, \
                                             which mentions it"
                                        ));
                                    }
                                }
                                regs
                            }
                            Event::BundleHint { hint, .. } => hint.clone(),
                            _ => continue,
                        };
                        for reg in regs.iter() {
                            if !by_reg[reg].contains(&event) {
                                return Err(format!(
                                    "{reg:?} does not name event {event:?}, which mentions it"
                                ));
                            }
                        }
                    }
                    Ok(())
                })?
                .unwrap_or(Ok(()))
            })
    }

    /// The whole index round-trips through JSON.
    #[test]
    fn the_index_round_trips_through_json() -> CheckResult<TestInput> {
        Check::new()
            .iters(100)
            .run(|test_input: &TestInput| -> Result<(), String> {
                with_indexed(test_input, |_input, _inner, index| {
                    let json = serde_json::to_string(index).unwrap();
                    let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
                    if parsed != serde_json::to_value(index).unwrap() {
                        return Err("the index does not round-trip".to_string());
                    }
                    Ok(())
                })?
                .unwrap_or(Ok(()))
            })
    }

    /// A function with nothing to spill still gets its spill histograms, empty.
    #[test]
    fn an_input_with_no_spills_still_builds() {
        let test_input = TestInput::default();
        let spills = with_indexed(&test_input, |_input, inner, index| {
            assert!(
                !inner
                    .events
                    .iter()
                    .any(|(_, event)| matches!(event, Event::SpillPlaced { .. })),
                "the default input should not spill",
            );
            let spills = index
                .histograms
                .iter()
                .filter(|histogram| histogram.id.starts_with("spills-per-"))
                .count();
            for histogram in &index.histograms {
                check_histogram(histogram).unwrap();
            }
            spills
        })
        .unwrap()
        .unwrap();
        assert_eq!(spills, 2);
    }
}
