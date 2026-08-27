//! Constructs live ranges and bundles.

use crate::RegSet;
use crate::counts::Counts;
use crate::entity::{
    Block, Entity, EntityRange, EntityRepr, Inst, PrimaryMap, Region, SecondaryMap, Val, WideInt,
};
use crate::error::IResult;
use crate::input::{
    Input, InputBlock, InputFunction, InputInst, InputValue, OperandConstraint, Position, RematCost,
};
use crate::liveness::{Liveness, block_first_inst, block_last_inst};
use crate::machine::{Machine, RegClassMembers};
use crate::output::{Allocation, OutputInner};
use crate::packed_float::PackedPositiveFloat;
use crate::timing::Timing;

define_entities! {
    /// A contiguous span `[start, end)` within which an associated value is
    /// live.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct LiveSpan = "span";

    /// A set of non-overlapping live spans that we will attempt to allocate
    /// together.
    ///
    /// Unlike `LiveSpan`, a bundle may have many associated values (e.g. due to
    /// coalescing).
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct LiveBundle = "bundle";

    /// A use or def of a value.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Use = "use";

    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct BundleSpansStorageIndex = "bundle_spans_storage_index";
}

/// A single program point at which a value is (or is not) live.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LivePoint<E>
where
    E: EntityRepr,
{
    /// +-------------------------+--------+
    /// | inst: bits(E::Wide) - 1 | pos: 1 |
    /// +-------------------------+--------+
    ///
    /// NB: The instruction is above the position, so that comparing two points'
    /// packed bits (the derived `Ord`) is the same as comparing them in program
    /// order.
    bits: E::Wide,
}

impl<E> core::fmt::Debug for LivePoint<E>
where
    E: EntityRepr,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}:{:?}", self.inst(), self.pos())
    }
}

impl<E> LivePoint<E>
where
    E: EntityRepr,
{
    /// The largest instruction index that a `LivePoint<E>` can represent.
    ///
    /// The position takes the low bit, leaving the instruction index the
    /// remaining high bits.
    pub const MAX_INST_INDEX: usize = (1usize << (<E::Wide as WideInt>::BITS - 1)) - 1;

    #[inline]
    pub fn new(inst: Inst<E>, pos: Position) -> Self {
        debug_assert!(inst.index() <= Self::MAX_INST_INDEX);
        LivePoint {
            bits: E::Wide::from_usize((inst.index() << 1) + (pos as usize)),
        }
    }

    #[inline]
    pub fn pos(self) -> Position {
        if self.bits.to_usize() & 1 == 0 {
            Position::Early
        } else {
            Position::Late
        }
    }

    #[inline]
    pub fn inst(self) -> Inst<E> {
        Inst::try_new(self.bits.to_usize() >> 1).unwrap()
    }

    /// Does the span `a_start..a_end` overlap with the span `b_start..b_end`?
    #[inline]
    pub fn spans_overlap(a_start: Self, a_end: Self, b_start: Self, b_end: Self) -> bool {
        debug_assert!(a_start <= a_end);
        debug_assert!(b_start <= b_end);
        a_start < b_end && b_start < a_end
    }

    /// The program point immediately following this one.
    ///
    /// `(I, Early)` is followed by `(I, Late)`, and `(I, Late)` by `(I + 1,
    /// Early)`. Because the position is the low bit, this operation is just
    /// incrementing the packed bits.
    ///
    /// This is what turns a use, which is inclusive, into the exclusive end of
    /// the span that reaches it.
    #[inline]
    pub fn next_point(self) -> Self {
        let bits = self.bits.to_usize() + 1;
        debug_assert!(<E::Wide as WideInt>::try_from_usize(bits).is_some());
        LivePoint {
            bits: E::Wide::from_usize(bits),
        }
    }

    /// The program point immediately preceding this one; the inverse of
    /// `Self::next_point`.
    #[inline]
    pub fn prev_point(self) -> Self {
        let bits = self.bits.to_usize();
        debug_assert!(bits > 0, "the first program point has no predecessor");
        LivePoint {
            bits: E::Wide::from_usize(bits - 1),
        }
    }
}

/// How much it would cost to spill a value, rather than keep it in a register.
///
/// Larger values mean a spill would be more expensive; smaller values mean a
/// spill would be less expensive.
///
/// A `SpillWeight` is not a cycle estimate, it has not unit and is only used to
/// weigh decisions, and is therefore only meaningful in comparison to other
/// `SpillWeight`s.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SpillWeight(PackedSpillWeight);

const SPILL_WEIGHT_BITS: u32 = 16;
type PackedSpillWeight = PackedPositiveFloat<u16, SPILL_WEIGHT_BITS>;

impl SpillWeight {
    /// Create a spill weight from `weight`, which must be positive.
    #[inline]
    pub const fn new(weight: f32) -> Self {
        SpillWeight(PackedSpillWeight::new(weight))
    }

    /// This weight's value.
    #[inline]
    pub const fn as_f32(self) -> f32 {
        self.0.as_f32()
    }

    #[inline]
    pub(crate) const fn bits(self) -> u16 {
        self.0.bits()
    }

    #[inline]
    pub(crate) const fn from_bits(bits: u16) -> Self {
        SpillWeight(PackedSpillWeight::from_bits(bits))
    }
}

/// The cost of a register-to-register move, relative to a spill or a reload.
const MOVE_COST: f32 = 0.5;

/// What fraction of its value's register class's spill cost an unconstrained
/// use pays.
///
/// An `Any` operand constraint accepts an operand in a stack slot, so spilling
/// its value does not make the program illegal, but a stack slot is still
/// slower than a register.
const STACK_ACCESS_SCALE: f32 = 0.5;

/// The `K` in `weight = total_cost / (num_insts + K)`.
///
/// For a bundle much shorter than `K`, the denominator barely moves, so the
/// weight is effectively a use *count*; for one much longer than `K`, the `K`
/// washes out and the weight becomes a use *density*.
///
/// For what it's worth: for their equivalent constants, LLVM uses `25` and
/// regalloc3 uses `200`.
const SPILL_WEIGHT_ADJUST: usize = 25;

/// Cost scale for a value that is always cheaper to rematerialize than to keep
/// in a register: spilling it costs nothing at all.
const REMAT_ALWAYS_SCALE: f32 = 0.0;

/// Cost scale for a value that is cheaper to rematerialize than to move.
const REMAT_CHEAPER_THAN_MOVE_SCALE: f32 = 0.1;

/// Cost scale for a value that is cheaper to rematerialize than to reload from
/// a spill slot.
const REMAT_CHEAPER_THAN_RELOAD_SCALE: f32 = 0.25;

/// How much worse off `val` would be if this use had to read it from a spill
/// slot instead of a register.
///
/// `unresolved` is the operand's constraint as written, and `resolved` is that
/// same constraint after a `Reuse` has been chased to the operand it is tied
/// to.
fn use_spill_cost<E>(
    input: &Input<'_, impl InputFunction>,
    val: Val<E>,
    unresolved: OperandConstraint,
    resolved: OperandConstraint,
) -> f32
where
    E: EntityRepr,
{
    let cost = match resolved {
        // The value has to be on the stack anyways, so spilling it costs
        // nothing.
        OperandConstraint::Stack => 0.0,

        // The value must be in a register here; pay the class's full price.
        OperandConstraint::Reg(class) => class.spill_cost(input.machine),

        // A spill slot is legal here, but still slower than a register.
        OperandConstraint::Any => {
            let class = input.func.value(val.with_repr32()).reg_class();
            STACK_ACCESS_SCALE * class.spill_cost(input.machine)
        }

        OperandConstraint::Reuse(_) => unreachable!("`resolved` is resolved"),
    };

    if matches!(unresolved, OperandConstraint::Reuse(_)) {
        // A reuse-tied operand needs a register-to-register move whether or not
        // its value is spilled, so subtract the move cost.
        (cost - MOVE_COST).max(0.0)
    } else {
        cost
    }
}

/// How much cheaper rematerializing a value makes spilling it.
fn remat_scale(remat_cost: Option<RematCost>) -> f32 {
    match remat_cost {
        None => 1.0,
        Some(RematCost::AlwaysRemat) => REMAT_ALWAYS_SCALE,
        Some(RematCost::CheaperThanMove) => REMAT_CHEAPER_THAN_MOVE_SCALE,
        Some(RematCost::CheaperThanReload) => REMAT_CHEAPER_THAN_RELOAD_SCALE,
    }
}

/// Like `use_spill_cost`, but scaled by rematerializability and block
/// frequency.
fn use_spill_weight<E>(
    input: &Input<'_, impl InputFunction>,
    uses: &PrimaryMap<Use<E>, UseData<E>>,
    frequency: f32,
    val: Val<E>,
    u: Use<E>,
) -> SpillWeight
where
    E: EntityRepr,
{
    let remat_scale = remat_scale(input.func.value(val.with_repr32()).remat_cost());
    let point = uses[u].point;
    let operand = usize::from(uses[u].operand);
    let input_inst = input.func.inst(point.inst().with_repr32());
    let constraint = input_inst.operand(operand).constraint();

    let cost = use_spill_cost(
        input,
        val,
        constraint,
        constraint.resolved(|j| input_inst.operand(j).constraint()),
    );
    debug_assert!(cost.is_sign_positive());

    let weight = cost * remat_scale * frequency;
    debug_assert!(weight.is_sign_positive());

    SpillWeight::new(weight)
}

/// Divide a bundle's total use cost by its length, blending a use count with a
/// use density.
pub(crate) fn normalize_spill_weight(total_use_cost: f32, sum_len_insts: usize) -> f32 {
    debug_assert!(total_use_cost >= 0.0);
    let denominator = (sum_len_insts + SPILL_WEIGHT_ADJUST) as f32;
    (total_use_cost / denominator).min(f32::MAX)
}

/// Is a bundle covering `sum_len_insts` instructions minimal?
///
/// Minimal bundles cannot be split any further.
///
/// One instruction is the floor because moves go at instruction boundaries, and
/// a one-instruction bundle has no interior boundary to put one at. On the
/// other hand, a bundle holding two one-instruction spans can still be split
/// into two bundles of one span each.
pub(crate) fn is_minimal_bundle(sum_len_insts: usize) -> bool {
    debug_assert!(
        sum_len_insts >= 1,
        "a bundle always covers at least one instruction",
    );
    sum_len_insts <= 1
}

/// Round `weight` to the precision a bundle stores it at.
#[cfg(test)]
pub(crate) fn round_bundle_spill_weight(weight: f32) -> f32 {
    PackedPositiveFloat::<u32, BUNDLE_SPILL_WEIGHT_BITS>::new(weight).as_f32()
}

pub const MAX_INST_INDEX: usize = LivePoint::<u32>::MAX_INST_INDEX;

/// The maximum number of operands that a single instruction may have.
///
/// `UseData::operand` is a `u16` index into its instruction's operand list, so
/// the largest valid index must fit in a `u16`.
pub const MAX_OPERANDS_PER_INST: usize = u16::MAX as usize + 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UseData<E>
where
    E: EntityRepr,
{
    /// The program point at which this use or def happens.
    point: LivePoint<E>,

    /// Which operand of `self.pos`'s instruction this is.
    operand: u16,

    /// How much worse off this use would be if its value were spilled.
    weight: SpillWeight,
}

impl<E> UseData<E>
where
    E: EntityRepr,
{
    /// Create a `UseData` for the `operand`th operand of `point`'s instruction.
    ///
    /// The weight is initially zero and is filled in later.
    #[inline]
    pub(crate) fn new(point: LivePoint<E>, operand: usize) -> Self {
        debug_assert!(operand < MAX_OPERANDS_PER_INST);
        UseData {
            point,
            operand: u16::try_from(operand).unwrap(),
            weight: SpillWeight::new(0.0),
        }
    }

    /// This use's position in program order: its program point, and then which
    /// operand of that point's instruction it is.
    ///
    /// Span construction pushes uses in this order, so it is what checks that
    /// the run it flushed is sorted.
    #[inline]
    pub(crate) fn order_key(&self) -> (LivePoint<E>, u16) {
        (self.point, self.operand)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LiveSpanData<E>
where
    E: EntityRepr,
{
    /// The start of this span, inclusive.
    start: LivePoint<E>,

    /// The end of this span, exclusive.
    end: LivePoint<E>,

    /// `self.val`'s uses (and, possibly, def) within this span.
    ///
    /// Sorted by position.
    uses: EntityRange<Use<E>>,

    /// The value that this span is associated with.
    val: Val<E>,

    /// Bit:     0
    ///        +------------------+
    /// Field: | has_fixed_use: 1 |
    ///        +------------------+
    flags: u8,
}

const SPAN_HAS_FIXED_USE: u8 = 1 << 0;

impl<E> LiveSpanData<E>
where
    E: EntityRepr,
{
    /// Create a span covering `[start, end)` for `val`, with the given uses.
    ///
    /// `has_fixed_use` is whether any of `uses` demands one particular register,
    /// i.e. resolves to a singleton class. The caller computes it because it is
    /// already resolving each use's constraint to decide where to split.
    #[inline]
    pub(crate) fn new(
        start: LivePoint<E>,
        end: LivePoint<E>,
        val: Val<E>,
        uses: EntityRange<Use<E>>,
        has_fixed_use: bool,
    ) -> Self {
        debug_assert!(start < end);
        LiveSpanData {
            start,
            end,
            uses,
            val,
            flags: if has_fixed_use { SPAN_HAS_FIXED_USE } else { 0 },
        }
    }
}

#[allow(dead_code, reason = "will probably need it")]
pub struct LiveBundleData<E>
where
    E: EntityRepr,
{
    /// The spans contained inside this bundle, in ascending program order.
    spans: EntityRange<BundleSpansStorageIndex<E>>,

    /// The region that this bundle is within.
    ///
    /// Bundles never span across regions.
    region: Region<E>,

    /// Where this bundle may be allocated: the merge of the resolved
    /// constraints of every use of every span within it.
    ///
    /// Always already resolved, so will never contain a `Reuse` constraint.
    constraint: OperandConstraint,

    /// The subset of `self.constraint`'s registers that this bundle would
    /// prefer to be allocated within, if any.
    ///
    /// Empty means no preference.
    preference: RegSet,

    /// Where this bundle is currently allocated.
    allocation: Option<Allocation<E>>,

    /// Packed weight and flags.
    ///
    /// Keeping the flags *above* the weight is what makes a minimal bundle sort
    /// above every ordinary one under a plain integer comparison of
    /// `weight_and_flags`, rather than under a rule that every comparison site
    /// has to remember to apply.
    ///
    /// Bit:     31           30                  29     ...     0
    ///        +------------+-------------------+------------------+
    /// Field: | minimal: 1 | has_fixed_uses: 1 | spill_weight: 30 |
    ///        +------------+-------------------+------------------+
    weight_and_flags: u32,
}

const BUNDLE_SPILL_WEIGHT_BITS: u32 = 30;
const BUNDLE_SPILL_WEIGHT_MASK: u32 = PackedPositiveFloat::<u32, BUNDLE_SPILL_WEIGHT_BITS>::MASK;
const BUNDLE_HAS_FIXED_USES: u32 = 1 << 30;
const BUNDLE_MINIMAL: u32 = 1 << 31;

impl<E> LiveBundleData<E>
where
    E: EntityRepr,
{
    /// Fold `hint` into this bundle's preference.
    fn add_hint(&mut self, hint: RegSet) {
        debug_assert!(!hint.is_empty());

        if self.preference.is_empty() {
            // Nothing has hinted this bundle yet, so take the hint whole rather
            // than intersecting it with an empty set and losing it.
            self.preference = hint;
            return;
        }

        let narrowed = self.preference.intersection(&hint);

        if narrowed.is_empty() {
            // Conflicting hints: keep the existing hint, rather than replacing it
            // with an equally arbitrary alternative.
            return;
        }

        self.preference = narrowed;
    }
}

pub struct LiveRanges<E>
where
    E: EntityRepr,
{
    /// Arena of all uses in the input function.
    uses: PrimaryMap<Use<E>, UseData<E>>,

    /// Map from a use to the span that contains it.
    use_span: SecondaryMap<Use<E>, LiveSpan<E>>,

    /// The live spans for the input function's values.
    spans: PrimaryMap<LiveSpan<E>, LiveSpanData<E>>,

    /// Each span's bundle.
    ///
    /// `None` until after coalescing has run.
    span_bundle: SecondaryMap<LiveSpan<E>, Option<LiveBundle<E>>>,

    /// The live bundles.
    bundles: PrimaryMap<LiveBundle<E>, LiveBundleData<E>>,

    /// Contiguous storage for the member spans of every bundle.
    bundle_spans_storage: PrimaryMap<BundleSpansStorageIndex<E>, LiveSpan<E>>,

    /// Map from a block to the spans within it.
    ///
    /// Only valid before any live span has been split (i.e. before region
    /// allocation), as splitting invalidates this map.
    block_spans: SecondaryMap<Block<E>, EntityRange<LiveSpan<E>>>,

    /// Map from a block to the spans that are live-in to it.
    ///
    /// Only valid before any live span has been split (i.e. before region
    /// allocation), as splitting invalidates this map.
    live_in_spans: SecondaryMap<Block<E>, EntityRange<LiveSpan<E>>>,

    /// Map from a block to the spans that are live-out of it.
    ///
    /// Only valid before any live span has been split (i.e. before region
    /// allocation), as splitting invalidates this map.
    live_out_spans: SecondaryMap<Block<E>, EntityRange<LiveSpan<E>>>,

    /// Map from a block to the uses within it.
    block_uses: SecondaryMap<Block<E>, EntityRange<Use<E>>>,

    /// Map from a region to the bundles that coalescing created for it.
    ///
    /// Does not include bundles created after coalescing, e.g. by splitting
    /// during region allocation.
    region_bundles: SecondaryMap<Region<E>, EntityRange<LiveBundle<E>>>,
}

impl<E> LiveRanges<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        LiveRanges {
            uses: PrimaryMap::new(),
            spans: PrimaryMap::new(),
            bundles: PrimaryMap::new(),
            bundle_spans_storage: PrimaryMap::new(),
            span_bundle: SecondaryMap::new(None),
            block_spans: SecondaryMap::new(EntityRange::empty()),
            live_in_spans: SecondaryMap::new(EntityRange::empty()),
            live_out_spans: SecondaryMap::new(EntityRange::empty()),
            block_uses: SecondaryMap::new(EntityRange::empty()),
            region_bundles: SecondaryMap::new(EntityRange::empty()),
            use_span: SecondaryMap::new(LiveSpan::MAX_REPRESENTABLE),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            uses,
            spans,
            bundles,
            bundle_spans_storage,
            span_bundle,
            block_spans,
            live_in_spans,
            live_out_spans,
            block_uses,
            use_span,
            region_bundles,
        } = self;
        uses.reset();
        spans.reset();
        bundles.reset();
        bundle_spans_storage.reset();
        span_bundle.reset();
        block_spans.reset();
        live_in_spans.reset();
        live_out_spans.reset();
        block_uses.reset();
        use_span.reset();
        region_bundles.reset();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            uses,
            spans,
            bundles,
            bundle_spans_storage,
            span_bundle,
            block_spans,
            live_in_spans,
            live_out_spans,
            block_uses,
            use_span,
            region_bundles,
        } = self;
        uses.is_reset()
            && spans.is_reset()
            && bundles.is_reset()
            && bundle_spans_storage.is_reset()
            && span_bundle.is_reset()
            && block_spans.is_reset()
            && live_in_spans.is_reset()
            && live_out_spans.is_reset()
            && block_uses.is_reset()
            && use_span.is_reset()
            && region_bundles.is_reset()
    }

    /// How many live spans have been constructed?
    #[allow(dead_code, reason = "will probably need it")]
    pub fn len_spans(&self) -> usize {
        self.spans.len()
    }

    /// Iterate over every live span that has been constructed.
    #[allow(dead_code, reason = "will probably need it")]
    pub fn spans(&self) -> impl Iterator<Item = LiveSpan<E>> + '_ {
        self.spans.keys()
    }

    /// How many uses have been recorded?
    #[allow(dead_code, reason = "will probably need it")]
    pub fn len_uses(&self) -> usize {
        self.uses.len()
    }

    /// How many bundles have been formed?
    pub fn len_bundles(&self) -> usize {
        self.bundles.len()
    }

    /// Iterate over every bundle.
    #[allow(dead_code, reason = "read by the tests, and by allocation soon")]
    pub fn bundles(&self) -> impl Iterator<Item = LiveBundle<E>> + '_ {
        self.bundles.keys()
    }

    /// Get the key that the next call to `push_bundle` will assign.
    pub fn next_bundle(&self, output: &mut OutputInner<E>) -> IResult<LiveBundle<E>> {
        self.bundles.next_key(output)
    }

    /// Form a new bundle out of `spans`, which must be non-empty and in
    /// ascending program order.
    pub(crate) fn push_bundle(
        &mut self,
        output: &mut OutputInner<E>,
        region: Region<E>,
        constraint: OperandConstraint,
        spans: impl Iterator<Item = LiveSpan<E>>,
    ) -> IResult<LiveBundle<E>> {
        let start = self.bundle_spans_storage.next_key(output)?;
        for span in spans {
            self.bundle_spans_storage.push(output, span)?;
        }
        let end = self.bundle_spans_storage.next_key(output)?;

        LiveBundle::new(self, output, region, constraint, EntityRange { start, end })
    }

    /// Construct the live spans for `func`'s values.
    ///
    /// This builds spans only; bundles are formed later, during partial
    /// allocation and coalescing.
    ///
    /// `liveness` is `&mut` because the per-block walk borrows its scratch
    /// space, not because this modifies the analysis results.
    pub fn construct(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        counts: &mut Counts,
        liveness: &mut Liveness<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        let _timing = Timing::new("live ranges");

        // Borrow the two maps separately so that `Liveness::block_spans` can
        // append to `uses` while we push into `spans`.
        let Self {
            uses,
            spans,
            bundles: _,
            bundle_spans_storage: _,
            span_bundle: _,
            block_spans,
            live_in_spans,
            live_out_spans,
            block_uses,
            use_span,
            region_bundles: _,
        } = self;

        // Construct a span for each value live in or across this block.
        for (block, input_block) in input.func.blocks() {
            let first_inst = output.with_repr(block_first_inst(&input_block))?;
            let last_inst = output.with_repr(block_last_inst(&input_block))?;
            let block_start = LivePoint::new(first_inst, Position::Early);
            let block_end = LivePoint::new(last_inst, Position::Late).next_point();

            let block = output.with_repr(block)?;
            let spans_start = spans.next_key(output)?;
            let uses_start = uses.next_key(output)?;
            for span in liveness.block_spans(input.func, block, uses, output)? {
                push_span_and_split_conflicts(input, uses, spans, counts, span, block_end, output)?;
            }
            let uses_end = uses.next_key(output)?;
            let spans_end = spans.next_key(output)?;

            // Sort this block's spans into buckets so that live-in and live-out
            // spans are both in a contiguous run.
            //
            // See `live_in_spans` and `live_out_spans`.
            spans.as_mut_slice()[spans_start.index()..spans_end.index()].sort_unstable_by_key(
                |data| {
                    let bucket = match (data.start == block_start, data.end == block_end) {
                        // Live-in only.
                        (true, false) => 0u8,
                        // Live-in and live-out.
                        (true, true) => 1,
                        // Live-out only.
                        (false, true) => 2,
                        // Neither: born and dead within this block.
                        (false, false) => 3,
                    };
                    (bucket, data.start, data.end)
                },
            );

            let mut live_in_end = spans_start;
            let mut live_out_start = None;
            let mut live_out_end = spans_start;
            let frequency = input_block.frequency().as_f32();

            // Attach each use to its span and calculate the use's spill weight.
            for span in (EntityRange {
                start: spans_start,
                end: spans_end,
            }) {
                let val = spans[span].val;
                for u in spans[span].uses {
                    use_span[u] = span;
                    uses[u].weight = use_spill_weight(input, uses, frequency, val, u);
                }

                let next = LiveSpan::try_new(span.index() + 1).unwrap();
                if spans[span].start == block_start {
                    live_in_end = next;
                }
                if spans[span].end == block_end {
                    live_out_start.get_or_insert(span);
                    live_out_end = next;
                }
            }

            block_spans[block] = EntityRange {
                start: spans_start,
                end: spans_end,
            };

            block_uses[block] = EntityRange {
                start: uses_start,
                end: uses_end,
            };
            debug_assert!(
                block_uses[block]
                    .into_iter()
                    .all(|u| use_span[u] != LiveSpan::default())
            );

            live_in_spans[block] = EntityRange {
                start: spans_start,
                end: live_in_end,
            };
            debug_assert!(
                live_in_spans[block]
                    .into_iter()
                    .all(|s| spans[s].start == block_start)
            );
            debug_assert_eq!(
                live_in_spans[block].into_iter().count(),
                block_spans[block]
                    .into_iter()
                    .filter(|&s| spans[s].start == block_start)
                    .count(),
            );

            live_out_spans[block] = match live_out_start {
                Some(start) => EntityRange {
                    start,
                    end: live_out_end,
                },
                None => EntityRange::empty(),
            };
            debug_assert!(
                live_out_spans[block]
                    .into_iter()
                    .all(|s| spans[s].end == block_end)
            );
            debug_assert_eq!(
                live_out_spans[block].into_iter().count(),
                block_spans[block]
                    .into_iter()
                    .filter(|&s| spans[s].end == block_end)
                    .count(),
            );
        }

        counts.live_spans += spans.len();
        counts.uses += uses.len();
        Ok(())
    }
}

impl<E> Use<E>
where
    E: EntityRepr,
{
    /// The program point at which this use or def happens.
    #[inline]
    pub(crate) fn point(self, live_ranges: &LiveRanges<E>) -> LivePoint<E> {
        live_ranges.uses[self].point
    }

    /// Which operand of this use's instruction this is.
    #[inline]
    pub(crate) fn operand(self, live_ranges: &LiveRanges<E>) -> usize {
        usize::from(live_ranges.uses[self].operand)
    }

    /// This use's spill weight.
    #[inline]
    pub(crate) fn weight(self, live_ranges: &LiveRanges<E>) -> SpillWeight {
        live_ranges.uses[self].weight
    }

    /// Get the span that contains this use.
    pub(crate) fn span(self, live_ranges: &LiveRanges<E>) -> LiveSpan<E> {
        let span = live_ranges.use_span[self];
        debug_assert_ne!(span, LiveSpan::MAX_REPRESENTABLE);
        span
    }
}

impl<E> LiveSpan<E>
where
    E: EntityRepr,
{
    /// This span's uses (and, possibly, def), in ascending program order.
    #[inline]
    pub(crate) fn uses(self, live_ranges: &LiveRanges<E>) -> EntityRange<Use<E>> {
        live_ranges.spans[self].uses
    }

    /// The start of this span, inclusive.
    #[inline]
    pub(crate) fn start(self, live_ranges: &LiveRanges<E>) -> LivePoint<E> {
        live_ranges.spans[self].start
    }

    /// The end of this span, exclusive.
    #[inline]
    pub(crate) fn end(self, live_ranges: &LiveRanges<E>) -> LivePoint<E> {
        live_ranges.spans[self].end
    }

    /// How many instructions this span covers.
    #[inline]
    pub(crate) fn len_insts(self, live_ranges: &LiveRanges<E>) -> usize {
        let first = self.start(live_ranges).inst().index();
        let last = self.end(live_ranges).prev_point().inst().index();
        debug_assert!(first <= last);
        last - first + 1
    }

    /// Do this span and `other` overlap (intersect)?
    #[inline]
    pub(crate) fn overlaps(self, live_ranges: &LiveRanges<E>, other: LiveSpan<E>) -> bool {
        LivePoint::<E>::spans_overlap(
            self.start(live_ranges),
            self.end(live_ranges),
            other.start(live_ranges),
            other.end(live_ranges),
        )
    }

    /// The value that this span is associated with.
    #[inline]
    pub(crate) fn val(self, live_ranges: &LiveRanges<E>) -> Val<E> {
        live_ranges.spans[self].val
    }

    /// Does this span contain a use with a fixed register constraint?
    #[inline]
    pub(crate) fn has_fixed_use(self, live_ranges: &LiveRanges<E>) -> bool {
        live_ranges.spans[self].flags & SPAN_HAS_FIXED_USE != 0
    }

    /// Get the bundle that this span is associated with, if any.
    ///
    /// Always returns `Some` after coalescing completes.
    pub(crate) fn bundle(self, live_ranges: &LiveRanges<E>) -> Option<LiveBundle<E>> {
        live_ranges.span_bundle[self]
    }

    /// Where this span may be allocated: the merge of the resolved constraints
    /// of every one of its uses.
    pub(crate) fn constraint(
        self,
        live_ranges: &LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
    ) -> OperandConstraint {
        let mut constraint = OperandConstraint::Any;
        for u in self.uses(live_ranges) {
            let input_inst = input.func.inst(u.point(live_ranges).inst().with_repr32());
            let sibling = |j| input_inst.operand(j).constraint();
            let use_constraint = input_inst
                .operand(u.operand(live_ranges))
                .constraint()
                .resolved(sibling);
            constraint = constraint
                .merge(
                    &use_constraint,
                    input.machine,
                    |_| unreachable!("the accumulated constraint is always resolved"),
                    |_| unreachable!("the use's constraint is already resolved"),
                )
                .expect("uses within the same span never conflict");
        }
        constraint
    }
}

impl<E> LiveBundle<E>
where
    E: EntityRepr,
{
    /// Create a new bundle.
    ///
    /// The spans must be non-empty, in ascending program order, and not already
    /// associated with another bundle.
    ///
    /// `constraint` must already be resolved (i.e. not `Reuse`).
    fn new(
        live_ranges: &mut LiveRanges<E>,
        output: &mut OutputInner<E>,
        region: Region<E>,
        constraint: OperandConstraint,
        spans: EntityRange<BundleSpansStorageIndex<E>>,
    ) -> IResult<Self> {
        debug_assert!(!spans.is_empty());
        debug_assert!(!matches!(constraint, OperandConstraint::Reuse(_)));

        let bundle = live_ranges.bundles.next_key(output)?;

        for index in spans {
            let span = live_ranges.bundle_spans_storage[index];
            debug_assert!(live_ranges.span_bundle[span].is_none());
            live_ranges.span_bundle[span] = Some(bundle);
        }

        let pushed = live_ranges.bundles.push(
            output,
            LiveBundleData {
                spans,
                region,
                constraint,
                preference: RegSet::new(),
                allocation: None,
                weight_and_flags: 0,
            },
        )?;
        debug_assert_eq!(pushed, bundle);

        bundle.recompute_weight_and_flags(live_ranges);
        Ok(bundle)
    }

    /// Recompute the cached `has_fixed_uses`, `is_minimal` and spill weight
    /// from the spans this bundle currently holds.
    fn recompute_weight_and_flags(self, live_ranges: &mut LiveRanges<E>) {
        let mut has_fixed_uses = false;
        let mut total_use_cost = 0.0;
        let mut sum_len_insts = 0;

        for span in self.spans(live_ranges) {
            has_fixed_uses |= span.has_fixed_use(live_ranges);
            total_use_cost += span
                .uses(live_ranges)
                .into_iter()
                .map(|u| u.weight(live_ranges).as_f32())
                .sum::<f32>();
            sum_len_insts += span.len_insts(live_ranges);
        }

        let mut weight_and_flags = PackedPositiveFloat::<u32, BUNDLE_SPILL_WEIGHT_BITS>::new(
            normalize_spill_weight(total_use_cost, sum_len_insts),
        )
        .bits();
        debug_assert_eq!(weight_and_flags & !BUNDLE_SPILL_WEIGHT_MASK, 0);
        if is_minimal_bundle(sum_len_insts) {
            weight_and_flags |= BUNDLE_MINIMAL;
        }
        if has_fixed_uses {
            weight_and_flags |= BUNDLE_HAS_FIXED_USES;
        }

        live_ranges.bundles[self].weight_and_flags = weight_and_flags;
    }

    /// Get the spans within this bundle, in ascending program order.
    pub(crate) fn spans(
        self,
        live_ranges: &LiveRanges<E>,
    ) -> impl ExactSizeIterator<Item = LiveSpan<E>> + Clone + '_ {
        live_ranges.bundles[self]
            .spans
            .into_iter()
            .map(move |i| live_ranges.bundle_spans_storage[i])
    }

    #[inline]
    #[cfg(test)]
    pub(crate) fn spans_storage(
        self,
        live_ranges: &LiveRanges<E>,
    ) -> EntityRange<BundleSpansStorageIndex<E>> {
        live_ranges.bundles[self].spans
    }

    /// Split this bundle in two between spans.
    ///
    /// This `LiveBundle` will retain `spans[..i]` and the return value is a new
    /// `LiveBundle` that contains `spans[i..]`.
    ///
    /// ```text
    ///                  bundle1
    /// +----------------------------------------+
    /// | span1      span2        span3          |
    /// | [==========)            [============) |
    /// |            [======)                    |
    /// +----------------------------------------+
    ///
    ///                      |
    ///                      |
    ///                      |
    ///                split_at_span(3)
    ///                      |
    ///                      |
    ///                      V
    ///
    ///         bundle1                 bundle2
    /// +---------------------+    +----------------+
    /// | span1      span2    |    | span3          |
    /// | [==========)        |    | [============) |
    /// |            [======) |    |                |
    /// +---------------------+    +----------------+
    /// ```
    ///
    /// It must be the case that `1 <= i < spans.len()`, so that neither half is
    /// left without any span.
    pub(crate) fn split_at_span(
        self,
        live_ranges: &mut LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
        output: &mut OutputInner<E>,
        i: usize,
    ) -> IResult<LiveBundle<E>> {
        let data = &live_ranges.bundles[self];
        let (region, spans) = (data.region, data.spans);
        debug_assert!(data.allocation.is_none());

        let indices = spans.indices();
        debug_assert!(1 <= i && i < indices.len());
        let mid = BundleSpansStorageIndex::try_new(indices.start + i).unwrap();

        let prefix = EntityRange {
            start: spans.start,
            end: mid,
        };
        let suffix = EntityRange {
            start: mid,
            end: spans.end,
        };

        live_ranges.bundles[self].spans = prefix;
        self.recompute_weight_and_flags(live_ranges);
        self.recompute_constraint(live_ranges, input);

        for index in suffix {
            let span = live_ranges.bundle_spans_storage[index];
            debug_assert_eq!(live_ranges.span_bundle[span], Some(self));
            live_ranges.span_bundle[span] = None;
        }
        let new = LiveBundle::new(live_ranges, output, region, OperandConstraint::Any, suffix)?;
        new.recompute_constraint(live_ranges, input);
        Ok(new)
    }

    /// The region that this bundle is within.
    ///
    /// Bundles never span across regions.
    #[inline]
    pub(crate) fn region(self, live_ranges: &LiveRanges<E>) -> Region<E> {
        live_ranges.bundles[self].region
    }

    /// Where this bundle may be allocated: the merge of the resolved
    /// constraints of every use of every span within it.
    #[inline]
    pub(crate) fn constraint(self, live_ranges: &LiveRanges<E>) -> OperandConstraint {
        live_ranges.bundles[self].constraint
    }

    /// The subset of this bundle's constraint's registers that it would prefer
    /// to be allocated within, if any.
    ///
    /// Empty means no preference.
    #[inline]
    pub(crate) fn preference(self, live_ranges: &LiveRanges<E>) -> &RegSet {
        &live_ranges.bundles[self].preference
    }

    /// Where this bundle is currently allocated.
    #[inline]
    #[allow(dead_code, reason = "will probably need it")]
    pub(crate) fn allocation(self, live_ranges: &LiveRanges<E>) -> Option<Allocation<E>> {
        live_ranges.bundles[self].allocation
    }

    /// Is this bundle minimal, i.e. too small to be split any further?
    #[inline]
    #[allow(dead_code, reason = "will probably need it")]
    pub(crate) fn is_minimal(self, live_ranges: &LiveRanges<E>) -> bool {
        live_ranges.bundles[self].weight_and_flags & BUNDLE_MINIMAL != 0
    }

    /// Does this bundle contain a use with a fixed register constraint?
    #[inline]
    #[allow(dead_code, reason = "will probably need it")]
    pub(crate) fn has_fixed_uses(self, live_ranges: &LiveRanges<E>) -> bool {
        live_ranges.bundles[self].weight_and_flags & BUNDLE_HAS_FIXED_USES != 0
    }

    /// How expensive it would be to spill this bundle.
    #[inline]
    pub(crate) fn spill_weight(self, live_ranges: &LiveRanges<E>) -> f32 {
        PackedPositiveFloat::<u32, BUNDLE_SPILL_WEIGHT_BITS>::from_bits(
            live_ranges.bundles[self].weight_and_flags & BUNDLE_SPILL_WEIGHT_MASK,
        )
        .as_f32()
    }

    /// Bias this bundle towards the registers that `constraint` names.
    pub(crate) fn hint(
        self,
        live_ranges: &mut LiveRanges<E>,
        machine: &Machine,
        constraint: OperandConstraint,
    ) {
        match constraint {
            // Fallthrough.
            OperandConstraint::Reg(_) => {}

            // If everything is acceptable there is nothing to hint.
            OperandConstraint::Any => return,

            // Things that belong on the stack have no register(s) to hint.
            OperandConstraint::Stack => return,

            OperandConstraint::Reuse(_) => unreachable!("constraints should already be resolved"),
        }

        let data = &mut live_ranges.bundles[self];

        let already_resolved = |_| unreachable!("constraints should already be resolved");
        let class =
            match data
                .constraint
                .merge(&constraint, machine, &already_resolved, &already_resolved)
            {
                Some(OperandConstraint::Reg(intersection)) => intersection,
                Some(OperandConstraint::Any) | Some(OperandConstraint::Stack) | None => return,
                Some(OperandConstraint::Reuse(_)) => {
                    unreachable!("constraints should already be resolved")
                }
            };

        // We only hint for registers (the common case) and not register groups.
        let RegClassMembers::Regs(_) = class.members(machine) else {
            return;
        };

        debug_assert!(!class.member_set(machine).is_empty());
        data.add_hint(class.member_set(machine).clone());
    }

    /// Bias this bundle towards `regs`.
    pub(crate) fn add_hint(self, live_ranges: &mut LiveRanges<E>, regs: &RegSet) {
        if regs.is_empty() {
            return;
        }
        live_ranges.bundles[self].add_hint(regs.clone());
    }

    /// Recompute this bundle's constraint from the spans it currently holds.
    fn recompute_constraint(
        self,
        live_ranges: &mut LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
    ) {
        let mut constraint = OperandConstraint::Any;
        for span in self.spans(live_ranges) {
            let span_constraint = span.constraint(live_ranges, input);
            constraint = constraint
                .merge(
                    &span_constraint,
                    input.machine,
                    |_| unreachable!("the accumulated constraint is always resolved"),
                    |_| unreachable!("a span's constraint is already resolved"),
                )
                .expect("the spans of a bundle never conflict, so neither do any subset of them");
        }
        live_ranges.bundles[self].constraint = constraint;
    }
}

impl<E> Block<E>
where
    E: EntityRepr,
{
    /// Get the spans within this block.
    ///
    /// Only valid before any live span has been split (i.e. before region
    /// allocation), as splitting invalidates this map.
    pub(crate) fn spans(self, live_ranges: &LiveRanges<E>) -> EntityRange<LiveSpan<E>> {
        live_ranges.block_spans[self]
    }

    /// Get the spans that are live-in to this block.
    ///
    /// Only valid before any live span has been split (i.e. before region
    /// allocation), as splitting invalidates this map.
    pub(crate) fn live_in_spans(self, live_ranges: &LiveRanges<E>) -> EntityRange<LiveSpan<E>> {
        live_ranges.live_in_spans[self]
    }

    /// Get the spans that are live-out of this block.
    ///
    /// Only valid before any live span has been split (i.e. before region
    /// allocation), as splitting invalidates this map.
    pub(crate) fn live_out_spans(self, live_ranges: &LiveRanges<E>) -> EntityRange<LiveSpan<E>> {
        live_ranges.live_out_spans[self]
    }

    /// Get the range of uses that construction recorded for this block.
    fn uses(self, live_ranges: &LiveRanges<E>) -> EntityRange<Use<E>> {
        live_ranges.block_uses[self]
    }
}

impl<E> Region<E>
where
    E: EntityRepr,
{
    /// Get the bundles that coalescing created for this region.
    ///
    /// Only valid before any live span has been split (i.e. before region
    /// allocation), as splitting adds bundles outside this range.
    pub(crate) fn bundles(self, live_ranges: &LiveRanges<E>) -> EntityRange<LiveBundle<E>> {
        live_ranges.region_bundles[self]
    }

    /// Record the bundles that were created for this region.
    pub(crate) fn set_bundles(
        self,
        live_ranges: &mut LiveRanges<E>,
        bundles: EntityRange<LiveBundle<E>>,
    ) {
        debug_assert!(live_ranges.region_bundles[self].is_empty());
        live_ranges.region_bundles[self] = bundles;
    }
}

impl<E> Inst<E>
where
    E: EntityRepr,
{
    /// Find the span that records this instruction's `operand`th operand as one
    /// of its uses, where this instruction is in `block`.
    pub(crate) fn operand_span(
        self,
        live_ranges: &LiveRanges<E>,
        block: Block<E>,
        operand: usize,
    ) -> Option<LiveSpan<E>> {
        block
            .uses(live_ranges)
            .into_iter()
            .find(|&u| u.point(live_ranges).inst() == self && u.operand(live_ranges) == operand)
            .map(|u| u.span(live_ranges))
    }
}

/// Push the given span, eagerly splitting at every point where its uses'
/// constraints conflict.
fn push_span_and_split_conflicts<E>(
    input: &Input<'_, impl InputFunction>,
    uses: &PrimaryMap<Use<E>, UseData<E>>,
    spans: &mut PrimaryMap<LiveSpan<E>, LiveSpanData<E>>,
    counts: &mut Counts,
    (start, end, val, span_uses): (LivePoint<E>, LivePoint<E>, Val<E>, EntityRange<Use<E>>),
    block_end: LivePoint<E>,
    output: &mut OutputInner<E>,
) -> IResult<()>
where
    E: EntityRepr,
{
    // The piece we are accumulating: where it starts, where its uses start, the
    // merged constraint of everything folded into it so far, and whether any of
    // that demands one particular register.
    let mut piece_start = start;
    let mut piece_uses_start = span_uses.start;
    let mut piece_constraint = OperandConstraint::Any;
    let mut piece_has_fixed_use = false;

    let mut last_point = start;
    for use_ in span_uses {
        let use_data = &uses[use_];
        let point = use_data.point;

        let input_inst = input.func.inst(point.inst().with_repr32());
        let sibling = |j| input_inst.operand(j).constraint();
        let use_constraint = input_inst
            .operand(usize::from(use_data.operand))
            .constraint();

        let resolved = use_constraint.resolved(&sibling);
        let is_fixed = match resolved {
            OperandConstraint::Reg(class) => class.is_singleton(input.machine),
            _ => false,
        };

        match piece_constraint.merge(
            &use_constraint,
            input.machine,
            |_| unreachable!("the accumulated constraint is always resolved"),
            &sibling,
        ) {
            // No conflict: we can fold `use_` into this piece.
            Some(merged) => {
                piece_constraint = merged.resolved(&sibling);
                piece_has_fixed_use |= is_fixed;
                last_point = point;
            }

            // Conflict: `use_` cannot fold into this piece, so split the span.
            None => {
                spans.push(
                    output,
                    LiveSpanData::new(
                        piece_start,
                        core::cmp::max(point, last_point.next_point()),
                        val,
                        EntityRange {
                            start: piece_uses_start,
                            end: use_,
                        },
                        piece_has_fixed_use,
                    ),
                )?;
                counts.eager_splits.inc();

                piece_start = point;
                piece_uses_start = use_;
                piece_constraint = resolved;
                piece_has_fixed_use = is_fixed;
                last_point = point;
            }
        }
    }

    // The final piece runs to the end.
    //
    // This piece either has uses or spans to the end of the block (because the
    // associated value is live-out of the block).
    debug_assert!(piece_uses_start != span_uses.end || end == block_end);
    spans.push(
        output,
        LiveSpanData::new(
            piece_start,
            end,
            val,
            EntityRange {
                start: piece_uses_start,
                end: span_uses.end,
            },
            piece_has_fixed_use,
        ),
    )?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::DefUse;
    use crate::Reg;
    use crate::RegClass;
    use crate::dfs::Dfs;
    use crate::entity::Block;
    use crate::input::BlockFrequency;
    use crate::region_tree::RegionTree;
    use crate::test::{TestFunction, TestInput};
    use mutatis::check::{Check, CheckResult};
    use std::{
        collections::{BTreeSet as Set, HashMap},
        format,
        string::{String, ToString},
        vec,
        vec::Vec,
    };

    fn inst<E>(index: usize) -> Inst<E>
    where
        E: EntityRepr,
    {
        Inst::try_new(index).unwrap()
    }

    #[test]
    fn live_point_round_trips() {
        // The largest index each representation can hold, so that we exercise
        // the top of the packed field as well as the bottom.
        let u8_max = Inst::<u8>::MAX_REPRESENTABLE.index();
        let u16_max = Inst::<u16>::MAX_REPRESENTABLE.index();

        for index in [0, 1, 2, 100, u8_max] {
            let early = LivePoint::<u8>::new(inst(index), Position::Early);
            let late = LivePoint::<u8>::new(inst(index), Position::Late);
            assert_eq!(early.inst().index(), index);
            assert_eq!(late.inst().index(), index);
            assert_eq!(early.pos() as u8, Position::Early as u8);
            assert_eq!(late.pos() as u8, Position::Late as u8);
            assert!(early.bits < late.bits);
        }

        for index in [0, 1, 2, 100, u16_max] {
            let early = LivePoint::<u16>::new(inst(index), Position::Early);
            let late = LivePoint::<u16>::new(inst(index), Position::Late);
            assert_eq!(early.inst().index(), index);
            assert_eq!(late.inst().index(), index);
            assert_eq!(early.pos() as u8, Position::Early as u8);
            assert_eq!(late.pos() as u8, Position::Late as u8);
            assert!(early.bits < late.bits);
        }
    }

    /// The property that justifies packing a point into one integer at all: the
    /// integer order of the packed bits is program order.
    #[test]
    fn live_points_compare_in_program_order() {
        let mut previous = None;
        for index in 0..8 {
            for point in [
                LivePoint::<u32>::new(inst(index), Position::Early),
                LivePoint::<u32>::new(inst(index), Position::Late),
            ] {
                if let Some(previous) = previous {
                    assert!(previous < point.bits);
                }
                previous = Some(point.bits);
            }
        }
    }

    /// The very top of the packed field, which is also the ceiling that
    /// validation enforces.
    #[test]
    fn live_point_at_the_largest_representable_inst() {
        let index = MAX_INST_INDEX;
        let point = LivePoint::<u32>::new(inst(index), Position::Late);
        assert_eq!(point.inst().index(), index);
        assert_eq!(point.bits, u32::MAX);
    }

    /// The ceilings that `run` uses to skip entity representations, and that
    /// validation uses to reject a function outright.
    #[test]
    fn max_inst_index_per_repr() {
        assert_eq!(LivePoint::<u8>::MAX_INST_INDEX, (1 << 15) - 1);
        assert_eq!(LivePoint::<u16>::MAX_INST_INDEX, (1 << 31) - 1);
        assert_eq!(LivePoint::<u32>::MAX_INST_INDEX, (1 << 31) - 1);

        // `u32` is the widest representation, so it sets the global ceiling.
        assert_eq!(MAX_INST_INDEX, LivePoint::<u32>::MAX_INST_INDEX);

        // For the narrow representations the `Inst<E>` entity runs out well
        // before the packing does, so it is the entity that binds there and the
        // packing that binds for `u32`.
        assert!(Inst::<u8>::MAX_REPRESENTABLE.index() < LivePoint::<u8>::MAX_INST_INDEX);
        assert!(Inst::<u16>::MAX_REPRESENTABLE.index() < LivePoint::<u16>::MAX_INST_INDEX);
        assert!(Inst::<u32>::MAX_REPRESENTABLE.index() > LivePoint::<u32>::MAX_INST_INDEX);

        // Whichever of the two binds, one index is reserved above the largest
        // index any real instruction may take, because live span construction
        // ends a span that reaches a block's exit at the one-past-the-end point
        // `(last_inst + 1, Early)`. That point must be constructible: both the
        // `Inst<E>` entity and the `LivePoint<E>` packing have to hold it.
        fn one_past_the_end_is_representable<E>()
        where
            E: EntityRepr,
        {
            let reserved = crate::max_representable_inst_index::<E>();
            let one_past_the_end = Inst::<E>::try_new(reserved).unwrap();
            assert!(one_past_the_end.index() <= LivePoint::<E>::MAX_INST_INDEX);
            let point = LivePoint::<E>::new(one_past_the_end, Position::Early);
            assert_eq!(point.inst(), one_past_the_end);
            assert!(matches!(point.pos(), Position::Early));
        }

        one_past_the_end_is_representable::<u8>();
        one_past_the_end_is_representable::<u16>();
        one_past_the_end_is_representable::<u32>();
    }

    /// There is one `UseData` per operand in the whole function, so its size is
    /// worth pinning down: a `LivePoint` and an operand index and a weight, with
    /// no padding at any entity representation.
    #[test]
    fn a_use_is_no_bigger_than_its_fields() {
        assert_eq!(size_of::<SpillWeight>(), 2);
        assert_eq!(
            size_of::<UseData<u32>>(),
            size_of::<LivePoint<u32>>() + size_of::<u16>() + size_of::<SpillWeight>(),
        );
        assert_eq!(size_of::<UseData<u32>>(), 8);
        assert_eq!(size_of::<UseData<u16>>(), 8);
        assert_eq!(size_of::<UseData<u8>>(), 6);
    }

    fn span(flags: u8) -> LiveSpanData<u32> {
        LiveSpanData {
            start: LivePoint::new(inst(0), Position::Early),
            end: LivePoint::new(inst(0), Position::Late),
            uses: EntityRange::empty(),
            val: Val::try_new(0).unwrap(),
            flags,
        }
    }

    fn has_fixed_use(span: &LiveSpanData<u32>) -> bool {
        span.flags & SPAN_HAS_FIXED_USE != 0
    }

    #[test]
    fn span_has_fixed_use_flag_round_trips() {
        assert!(!has_fixed_use(&span(0)));
        assert!(has_fixed_use(&span(SPAN_HAS_FIXED_USE)));
    }

    fn bundle(weight_and_flags: u32) -> LiveBundleData<u32> {
        LiveBundleData {
            spans: EntityRange::empty(),
            region: Region::try_new(0).unwrap(),
            constraint: OperandConstraint::Any,
            preference: RegSet::new(),
            allocation: None,
            weight_and_flags,
        }
    }

    fn is_minimal(bundle: &LiveBundleData<u32>) -> bool {
        bundle.weight_and_flags & BUNDLE_MINIMAL != 0
    }

    fn has_fixed_uses(bundle: &LiveBundleData<u32>) -> bool {
        bundle.weight_and_flags & BUNDLE_HAS_FIXED_USES != 0
    }

    fn spill_weight(bundle: &LiveBundleData<u32>) -> f32 {
        PackedPositiveFloat::<u32, BUNDLE_SPILL_WEIGHT_BITS>::from_bits(
            bundle.weight_and_flags & BUNDLE_SPILL_WEIGHT_MASK,
        )
        .as_f32()
    }

    #[test]
    fn bundle_flags_do_not_disturb_the_weight() {
        let weight = PackedPositiveFloat::<u32, BUNDLE_SPILL_WEIGHT_BITS>::new(3.25).bits();

        let plain = bundle(weight);
        assert!(!is_minimal(&plain));
        assert!(!has_fixed_uses(&plain));
        assert_eq!(spill_weight(&plain), 3.25);

        let all = bundle(weight | BUNDLE_MINIMAL | BUNDLE_HAS_FIXED_USES);
        assert!(is_minimal(&all));
        assert!(has_fixed_uses(&all));
        assert_eq!(spill_weight(&all), 3.25);
    }

    /// The reason the flags sit above the weight: a minimal bundle outranks
    /// every ordinary one under a plain integer comparison, with no rule for a
    /// comparison site to remember.
    #[test]
    fn minimal_bundles_outrank_every_ordinary_weight() {
        let heaviest_ordinary = bundle(BUNDLE_SPILL_WEIGHT_MASK);
        let lightest_minimal = bundle(BUNDLE_MINIMAL);
        assert!(!is_minimal(&heaviest_ordinary));
        assert!(is_minimal(&lightest_minimal));
        assert!(lightest_minimal.weight_and_flags > heaviest_ordinary.weight_and_flags);
    }

    /// The flag bits and the weight field must exactly tile a `u32`.
    #[test]
    fn bundle_weight_and_flags_tile_a_u32() {
        assert_eq!(
            BUNDLE_SPILL_WEIGHT_MASK | BUNDLE_HAS_FIXED_USES | BUNDLE_MINIMAL,
            u32::MAX
        );
        for flag in [BUNDLE_HAS_FIXED_USES, BUNDLE_MINIMAL] {
            assert_eq!(flag & BUNDLE_SPILL_WEIGHT_MASK, 0);
        }
    }

    /// The set holding exactly the registers with these indices.
    fn regs(indices: &[usize]) -> RegSet {
        let mut set = RegSet::new();
        for &index in indices {
            set.insert(Reg::try_new(index).unwrap());
        }
        set
    }

    /// A bundle takes its first hint whole: a fresh bundle's empty preference
    /// means that nothing has hinted it yet, so there is nothing to narrow the
    /// hint against.
    #[test]
    fn the_first_hint_is_adopted_whole() {
        let mut bundle = bundle(0);
        assert!(bundle.preference.is_empty());

        bundle.add_hint(regs(&[0, 2]));
        assert_eq!(bundle.preference, regs(&[0, 2]));
    }

    /// A second hint narrows the preference to the registers both hints want.
    #[test]
    fn a_later_hint_narrows_the_preference() {
        let mut bundle = bundle(0);
        bundle.add_hint(regs(&[0, 2]));

        bundle.add_hint(regs(&[2, 3]));
        assert_eq!(bundle.preference, regs(&[2]));

        // And narrowing again keeps narrowing, rather than starting over from
        // the newest hint.
        bundle.add_hint(regs(&[1, 2]));
        assert_eq!(bundle.preference, regs(&[2]));
    }

    /// ... but a hint that wants none of the registers the preference does is
    /// dropped, rather than replacing one arbitrary choice with another.
    #[test]
    fn a_conflicting_hint_leaves_the_preference_alone() {
        let mut bundle = bundle(0);
        bundle.add_hint(regs(&[0, 2]));

        bundle.add_hint(regs(&[1, 3]));
        assert_eq!(bundle.preference, regs(&[0, 2]));
    }

    /// Compute the liveness and live spans of `test_input`'s function.
    fn analyze_spans(test_input: &TestInput) -> Result<(Liveness<u32>, LiveRanges<u32>), String> {
        let mut counts = Counts::new();
        let mut dfs = Dfs::<u32>::new();
        let mut region_tree = RegionTree::<u32>::new();
        let mut liveness = Liveness::<u32>::new();
        let mut live_ranges = LiveRanges::<u32>::new();
        let mut output = OutputInner::<u32>::new();

        assert!(live_ranges.is_reset());

        let result = test_input.with_input(|input| {
            let func = input.func;
            region_tree
                .construct(func, &mut counts, &mut dfs, &mut output)
                .and_then(|()| liveness.construct(func, &mut counts, &mut dfs, &mut output))
                .and_then(|()| {
                    live_ranges.construct(input, &mut counts, &mut liveness, &mut output)
                })
        });
        if result.is_err() {
            return Err(format!("construction failed: {:?}", output.take_error()));
        }

        Ok((liveness, live_ranges))
    }

    /// The half-open program point bounds of `block`: `[start, end)`.
    ///
    /// This reads the block's instructions directly rather than going through
    /// anything `Liveness` computes, so that it can stand as an oracle for the
    /// span endpoints that construction is supposed to produce.
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

    /// Every operand in `func`, as `(block, point, operand index, kind, value)`.
    fn all_operands(func: &TestFunction) -> Vec<(Block, LivePoint<u32>, usize, DefUse, Val)> {
        let mut operands = Vec::new();
        for (block, input_block) in func.blocks() {
            for (inst, input_inst) in input_block.insts() {
                for (i, operand) in input_inst.operands().enumerate() {
                    operands.push((
                        block,
                        LivePoint::new(inst, operand.pos()),
                        i,
                        operand.kind(),
                        operand.val(),
                    ));
                }
            }
        }
        operands
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

    /// The point of eager splitting, stated directly: a value whose uses want
    /// disjoint register classes gets one span per class, cut just before the
    /// use that conflicts.
    ///
    /// The property test above says that no span is left unsatisfiable; this
    /// says where the split lands, which no invariant pins down.
    #[test]
    fn split_a_span_whose_uses_conflict() {
        let rc = |i| OperandConstraint::Reg(RegClass::try_new(i).unwrap());

        let test_input = TestInput::with_use_constraints(&[rc(0), rc(1)]);
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();

        let spans: Vec<LiveSpan> = live_ranges.spans().collect();
        assert_eq!(spans.len(), 2, "{spans:#?}");

        // The def, and then the two uses that cannot share a location.
        let def = LivePoint::new(inst(0), Position::Late);
        let first_use = LivePoint::new(inst(1), Position::Early);
        let second_use = LivePoint::new(inst(2), Position::Early);

        let (first, second) = (spans[0], spans[1]);
        assert_eq!(first.val(&live_ranges), second.val(&live_ranges));
        assert_eq!(first.start(&live_ranges), def);
        assert_eq!(
            first.end(&live_ranges),
            second_use,
            "the cut is just before the conflict"
        );
        assert_eq!(second.start(&live_ranges), second_use);
        assert!(second.end(&live_ranges) > second_use);

        // Each use is recorded by the piece that can satisfy it, and the def by
        // the piece it starts.
        let points = |span: LiveSpan| -> Vec<LivePoint<u32>> {
            span.uses(&live_ranges)
                .into_iter()
                .map(|u| u.point(&live_ranges))
                .collect()
        };
        assert_eq!(points(spans[0]), vec![def, first_use]);
        assert_eq!(points(spans[1]), vec![second_use]);

        // The control: `rc2` holds both registers, so it can be satisfied
        // alongside `rc0` and there is nothing to split.
        let test_input = TestInput::with_use_constraints(&[rc(0), rc(2)]);
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();
        assert_eq!(live_ranges.spans().count(), 1);
    }

    /// Splitting a bundle rearranges who owns which slots of the shared span
    /// storage without disturbing the tiling of it.
    ///
    /// Nothing else covers the arena side of splitting: the `splitting.rs`
    /// kernel never sees a `LiveRanges`, and `coalescing_properties` stops
    /// before region allocation ever runs. So this walks every admissible cut
    /// of one multi-span bundle and checks that the halves partition the
    /// parent exactly — no gap, no overlap, no orphaned slot — that both come
    /// out with the summaries `push_bundle` would have given them, and that
    /// both have had their constraints recomputed from the spans they kept.
    #[test]
    fn split_bundle_keeps_storage_tiled() {
        let rc = |i| OperandConstraint::Reg(RegClass::try_new(i).unwrap());

        // Alternating conflicting classes, so that span construction cuts the
        // one value into a span per use and there are several cuts to try.
        let test_input = TestInput::with_use_constraints(&[rc(0), rc(1), rc(0), rc(1), rc(0)]);
        let region = Region::try_new(0).unwrap();

        let build = || -> (LiveRanges<u32>, Vec<LiveSpan>) {
            let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();
            let spans = live_ranges.spans().collect::<Vec<_>>();
            (live_ranges, spans)
        };

        // A bundle's spans must never conflict with one another, and here every
        // span conflicts with its neighbours, so the bundle we split takes every
        // *other* span: one class throughout, with a hole between each pair.
        // That is the shape `split_between_spans` is handed in practice anyway.
        // The rest go into a second bundle, both so that every slot of the
        // storage is owned and so that the tiling comes out *unsorted* after the
        // split: the suffix half is the newest bundle in the arena, but its run
        // sits before that second bundle's.
        let evens = |spans: &[LiveSpan]| spans.iter().copied().step_by(2).collect::<Vec<_>>();
        let odds =
            |spans: &[LiveSpan]| spans.iter().copied().skip(1).step_by(2).collect::<Vec<_>>();

        let (_, all_spans) = build();
        let num_cut_spans = evens(&all_spans).len();
        assert!(
            num_cut_spans >= 3 && !odds(&all_spans).is_empty(),
            "want several cuts to try and a bundle after them, got {num_cut_spans} of \
             {} spans",
            all_spans.len(),
        );

        for prefix_end in 1..num_cut_spans {
            let (mut live_ranges, spans) = build();
            let mut output = OutputInner::<u32>::new();
            let (cut, rest) = (evens(&spans), odds(&spans));

            let prefix = live_ranges
                .push_bundle(
                    &mut output,
                    region,
                    OperandConstraint::Any,
                    cut.iter().copied(),
                )
                .unwrap();
            let tail = live_ranges
                .push_bundle(
                    &mut output,
                    region,
                    OperandConstraint::Any,
                    rest.iter().copied(),
                )
                .unwrap();
            let parent_run = prefix.spans_storage(&live_ranges);

            let suffix = test_input
                .with_input(|input| {
                    prefix.split_at_span(&mut live_ranges, input, &mut output, prefix_end)
                })
                .unwrap();

            // The two runs are adjacent, and together they are exactly what the
            // parent held.
            let prefix_run = prefix.spans_storage(&live_ranges);
            let suffix_run = suffix.spans_storage(&live_ranges);
            assert_eq!(prefix_run.start, parent_run.start);
            assert_eq!(prefix_run.end, suffix_run.start, "no gap and no overlap");
            assert_eq!(suffix_run.end, parent_run.end);
            assert_eq!(prefix_run.indices().len(), prefix_end);
            assert_eq!(suffix_run.indices().len(), num_cut_spans - prefix_end);

            // Each half holds the spans it should, in order, and each span
            // names the half that holds it.
            assert_eq!(
                prefix.spans(&live_ranges).collect::<Vec<_>>(),
                cut[..prefix_end]
            );
            assert_eq!(
                suffix.spans(&live_ranges).collect::<Vec<_>>(),
                cut[prefix_end..]
            );
            for (i, &span) in cut.iter().enumerate() {
                let expected = if i < prefix_end { prefix } else { suffix };
                assert_eq!(span.bundle(&live_ranges), Some(expected), "cut span {i}");
            }
            for (i, &span) in rest.iter().enumerate() {
                assert_eq!(span.bundle(&live_ranges), Some(tail), "tail span {i}");
            }

            // Both halves' cached summaries are what `push_bundle` would have
            // computed for the same span lists, and their constraints are what a
            // from-scratch recompute over those same spans gives — both built
            // from scratch elsewhere.
            let (mut reference, ref_spans) = build();
            let mut ref_output = OutputInner::<u32>::new();
            let ref_cut = evens(&ref_spans);
            let want_prefix = reference
                .push_bundle(
                    &mut ref_output,
                    region,
                    OperandConstraint::Any,
                    ref_cut[..prefix_end].iter().copied(),
                )
                .unwrap();
            let want_suffix = reference
                .push_bundle(
                    &mut ref_output,
                    region,
                    OperandConstraint::Any,
                    ref_cut[prefix_end..].iter().copied(),
                )
                .unwrap();
            test_input.with_input(|input| {
                want_prefix.recompute_constraint(&mut reference, input);
                want_suffix.recompute_constraint(&mut reference, input);
            });

            for (half, want) in [(prefix, want_prefix), (suffix, want_suffix)] {
                assert_eq!(
                    half.constraint(&live_ranges),
                    want.constraint(&reference),
                    "constraint of {half:?} after splitting at {prefix_end}",
                );
                assert_eq!(
                    half.has_fixed_uses(&live_ranges),
                    want.has_fixed_uses(&reference),
                    "has_fixed_uses of {half:?} after splitting at {prefix_end}",
                );
                assert_eq!(
                    half.spill_weight(&live_ranges),
                    want.spill_weight(&reference),
                    "spill_weight of {half:?} after splitting at {prefix_end}",
                );
                assert_eq!(
                    half.is_minimal(&live_ranges),
                    want.is_minimal(&reference),
                    "is_minimal of {half:?} after splitting at {prefix_end}",
                );
            }

            // And `coalescing.rs`'s invariant 5 still holds over the arena as a
            // whole: the runs tile it, though no longer in bundle-index order,
            // since the suffix is the newest bundle but sits in the middle.
            check_bundle_runs_tile_storage(&live_ranges);
            assert!(
                suffix > tail && suffix_run.start < tail.spans_storage(&live_ranges).start,
                "the suffix is the newest bundle but sits before the tail in storage, which is \
                 the case the sorted walk exists for",
            );
        }
    }

    /// The bundles' span lists tile their shared storage, in storage order.
    ///
    /// This is `coalescing.rs`'s invariant 5, repeated here because the test
    /// above is the only thing that runs it against a *split* arena.
    fn check_bundle_runs_tile_storage(live_ranges: &LiveRanges<u32>) {
        let mut runs = live_ranges
            .bundles()
            .map(|bundle| {
                let spans = bundle.spans_storage(live_ranges);
                assert!(!spans.is_empty(), "{bundle:?} holds no spans");
                (spans.start.index(), spans.end.index(), bundle)
            })
            .collect::<Vec<_>>();
        runs.sort_unstable();

        let mut next = 0;
        for (start, end, bundle) in runs {
            assert_eq!(start, next, "{bundle:?}'s run leaves a gap or overlaps");
            next = end;
        }
        assert_eq!(
            next,
            live_ranges.len_spans(),
            "some span belongs to nothing"
        );
    }

    /// Every use in `test_input`, in program order, as `(point, operand,
    /// weight)`.
    fn use_weights(test_input: &TestInput) -> Vec<(LivePoint<u32>, usize, f32)> {
        let (_liveness, live_ranges) = analyze_spans(test_input).unwrap();
        let mut weights: Vec<_> = live_ranges
            .spans()
            .flat_map(|span| span.uses(&live_ranges).into_iter())
            .map(|u| {
                (
                    u.point(&live_ranges),
                    u.operand(&live_ranges),
                    u.weight(&live_ranges).as_f32(),
                )
            })
            .collect();
        weights.sort_by_key(|&(point, operand, _)| (point, operand));
        weights
    }

    /// `weight` as it survives being packed into a [`SpillWeight`].
    ///
    /// A weight keeps only the top bits of its mantissa, so an expectation
    /// computed in full `f32` precision has to be put through the same rounding
    /// before it can be compared for equality.
    fn packed(weight: f32) -> f32 {
        SpillWeight::new(weight).as_f32()
    }

    /// Every class of [`TestMachine::two_registers`] costs this much to spill,
    /// and all of its values belong to `rc2`, so every weight the tests below
    /// expect is a multiple of this one number.
    const CLASS_COST: f32 = 1.0;

    /// What a use is worth in a register comes from its own constraint: nothing
    /// when it has to be on the stack anyway, a fraction when the stack is
    /// merely allowed, and full price when only a register will do.
    #[test]
    fn a_use_weighs_what_a_register_saves_it() {
        let rc2 = OperandConstraint::Reg(RegClass::try_new(2).unwrap());

        // Index 1 is the use; index 0 is the `Any` def that `with_use_constraints`
        // puts in front of it.
        let weight_of =
            |constraint| use_weights(&TestInput::with_use_constraints(&[constraint]))[1].2;

        assert_eq!(weight_of(rc2), packed(CLASS_COST));
        assert_eq!(
            weight_of(OperandConstraint::Any),
            packed(STACK_ACCESS_SCALE * CLASS_COST),
        );
        assert_eq!(
            weight_of(OperandConstraint::Stack),
            0.0,
            "a use that demands the stack loses nothing by being spilled there",
        );

        // The `Any` def in front of every one of those is itself weighed the
        // same way, so a def is not a special case.
        assert_eq!(
            use_weights(&TestInput::with_use_constraints(&[rc2]))[0].2,
            packed(STACK_ACCESS_SCALE * CLASS_COST),
        );
    }

    /// A tied operand needs a move whether or not its value is spilled, so a
    /// register only saves it the difference.
    #[test]
    fn a_tied_operand_only_saves_the_difference() {
        let rc2 = OperandConstraint::Reg(RegClass::try_new(2).unwrap());

        let weight_of = |test_input: &TestInput, operand: usize| {
            use_weights(test_input)
                .into_iter()
                .find(|&(point, j, _)| point.inst() == inst(1) && j == operand)
                .expect("the tied instruction's operands are both recorded")
                .2
        };

        // Operand 1 is the def tied to operand 0, so it resolves to operand 0's
        // constraint -- but pays a move's worth less for it.
        let tied = TestInput::with_reuse_def(rc2);
        assert_eq!(weight_of(&tied, 1), packed(CLASS_COST - MOVE_COST));
        assert_eq!(
            weight_of(&tied, 0),
            packed(CLASS_COST),
            "the untied operand it is tied *to* still pays full price",
        );

        // When a register would not have saved more than a move costs, the
        // difference floors at zero rather than going negative.
        let tied = TestInput::with_reuse_def(OperandConstraint::Any);
        assert!(STACK_ACCESS_SCALE * CLASS_COST <= MOVE_COST);
        assert_eq!(weight_of(&tied, 1), 0.0);
    }

    /// The same use is worth more in a block that runs more often.
    #[test]
    fn block_frequency_scales_every_weight() {
        let rc2 = OperandConstraint::Reg(RegClass::try_new(2).unwrap());

        let weight_at = |frequency| {
            let mut test_input = TestInput::with_use_constraints(&[rc2]);
            test_input.set_block_frequencies(frequency);
            use_weights(&test_input)[1].2
        };

        assert_eq!(weight_at(BlockFrequency::NORMAL), packed(CLASS_COST),);
        assert_eq!(
            weight_at(BlockFrequency::HOT),
            packed(BlockFrequency::HOT.as_f32() * CLASS_COST),
        );

        // A cold block does not zero a use out -- `COLD` is the smallest
        // positive frequency, not no frequency -- it just puts it below
        // everything that runs at all.
        let cold = weight_at(BlockFrequency::COLD);
        assert!(cold > 0.0, "{cold}");
        assert!(cold < weight_at(BlockFrequency::NORMAL));
    }

    /// A value that can be recomputed on demand is worth less in a register,
    /// and the cheaper it is to recompute the less it is worth.
    #[test]
    fn rematerializable_values_are_cheaper_to_spill() {
        let rc2 = OperandConstraint::Reg(RegClass::try_new(2).unwrap());

        let weight_with = |remat| {
            let mut test_input = TestInput::with_use_constraints(&[rc2]);
            test_input.set_remat_costs(remat);
            use_weights(&test_input)[1].2
        };

        assert_eq!(weight_with(None), packed(CLASS_COST));
        assert_eq!(
            weight_with(Some(RematCost::CheaperThanReload)),
            packed(REMAT_CHEAPER_THAN_RELOAD_SCALE * CLASS_COST),
        );
        assert_eq!(
            weight_with(Some(RematCost::CheaperThanMove)),
            packed(REMAT_CHEAPER_THAN_MOVE_SCALE * CLASS_COST),
        );
        assert_eq!(
            weight_with(Some(RematCost::AlwaysRemat)),
            0.0,
            "a value that is always cheaper to recompute is free to spill",
        );

        assert!(
            weight_with(Some(RematCost::AlwaysRemat))
                < weight_with(Some(RematCost::CheaperThanMove))
        );
        assert!(
            weight_with(Some(RematCost::CheaperThanMove))
                < weight_with(Some(RematCost::CheaperThanReload))
        );
        assert!(weight_with(Some(RematCost::CheaperThanReload)) < weight_with(None));
    }

    /// A use that names a class holding one register has no allocation choice
    /// left, and the span that covers it says so.
    #[test]
    fn a_use_that_names_one_register_is_a_fixed_use() {
        let rc = |i| OperandConstraint::Reg(RegClass::try_new(i).unwrap());

        let flags = |test_input: &TestInput| -> Vec<bool> {
            let (_liveness, live_ranges) = analyze_spans(test_input).unwrap();
            live_ranges
                .spans()
                .map(|s| s.has_fixed_use(&live_ranges))
                .collect()
        };

        // `rc0` holds exactly one of `two_registers`' two registers...
        assert_eq!(
            flags(&TestInput::with_use_constraints(&[rc(0)])),
            vec![true]
        );

        // ...while `rc2` holds both, so a use of it still has a choice.
        assert_eq!(
            flags(&TestInput::with_use_constraints(&[rc(2)])),
            vec![false]
        );

        // The flag is per span, not per value: a value whose stack use and
        // fixed register use force a split only flags the piece that actually
        // has the fixed one.
        assert_eq!(
            flags(&TestInput::with_use_constraints(&[
                OperandConstraint::Stack,
                rc(0),
            ])),
            vec![false, true],
        );
    }

    /// A span's length is what its weight gets divided by, so it counts
    /// instructions -- inclusively, and never fewer than one.
    #[test]
    fn a_spans_length_counts_its_instructions_inclusively() {
        let rc2 = OperandConstraint::Reg(RegClass::try_new(2).unwrap());

        // A def at instruction 0 and uses at 1 and 2 span three instructions,
        // even though the span ends part-way through the third.
        let test_input = TestInput::with_use_constraints(&[rc2, rc2]);
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();
        let spans: Vec<LiveSpan> = live_ranges.spans().collect();
        assert_eq!(spans.len(), 1, "{spans:#?}");
        assert_eq!(
            spans[0].start(&live_ranges),
            LivePoint::new(inst(0), Position::Late)
        );
        assert_eq!(
            spans[0].end(&live_ranges),
            LivePoint::new(inst(2), Position::Late)
        );
        assert_eq!(spans[0].len_insts(&live_ranges), 3);

        // A def whose value dies within its own instruction still covers that
        // one instruction, so no bundle can ever have a zero-length span to
        // divide by.
        for span in live_ranges.spans() {
            assert!(span.len_insts(&live_ranges) >= 1);
        }
    }

    /// The constant added to a bundle's length is what makes the weight a use
    /// *count* for short bundles and a use *density* for long ones.
    #[test]
    fn the_normalizer_blends_a_use_count_with_a_use_density() {
        // Same total cost, different lengths: the shorter bundle wins, because
        // it packs the same work into fewer instructions.
        assert!(normalize_spill_weight(4.0, 1) > normalize_spill_weight(4.0, 100));

        // Well below `SPILL_WEIGHT_ADJUST` the denominator barely moves, so
        // doubling a bundle's length costs it only a few percent...
        let short = normalize_spill_weight(1.0, 1);
        let twice = normalize_spill_weight(1.0, 2);
        assert!(twice > 0.9 * short, "{twice} vs {short}");

        // ...while well above it the constant washes out and doubling the
        // length nearly halves the weight.
        let long = normalize_spill_weight(1.0, 1_000);
        let twice = normalize_spill_weight(1.0, 2_000);
        assert!(twice < 0.6 * long, "{twice} vs {long}");

        // A bundle whose uses are all free to spill weighs nothing, however
        // long it is.
        assert_eq!(normalize_spill_weight(0.0, 1_000), 0.0);
    }

    /// The floor is one instruction, and it is a floor rather than a step: a
    /// bundle that somehow came out smaller is still minimal.
    #[test]
    fn the_minimal_floor_is_one_instruction() {
        assert!(is_minimal_bundle(1));
        assert!(!is_minimal_bundle(2));
        assert!(!is_minimal_bundle(usize::MAX));
    }

    #[test]
    fn live_span_properties() -> CheckResult<TestInput> {
        Check::new()
            .iters(10_000)
            .run(|test_input: &TestInput| -> Result<(), String> {
                let func = &test_input.func;
                let (mut liveness, live_ranges) = analyze_spans(test_input)?;

                let num_values = func.len_values();
                let operands = all_operands(func);
                let inst_block = inst_blocks(func);
                let bounds: HashMap<Block, (LivePoint<u32>, LivePoint<u32>)> = func
                    .blocks()
                    .map(|(b, _)| (b, block_points(func, b)))
                    .collect();

                // Index the spans by the block they live in and by their value.
                // A span's block is the one that owns the instruction its start
                // points at; property 1 below checks that the whole span fits
                // inside that block.
                let mut spans_of: HashMap<(Val, Block), Vec<LiveSpan>> = HashMap::new();
                let mut spans_in: HashMap<Block, Vec<LiveSpan>> =
                    func.blocks().map(|(b, _)| (b, Vec::new())).collect();

                // 1. Every span is well formed and stays inside a single block.
                for span in live_ranges.spans() {
                    if span.start(&live_ranges) >= span.end(&live_ranges) {
                        return Err(format!(
                            "{span:?} covers {:?}..{:?}, which is empty or backwards",
                            span.start(&live_ranges),
                            span.end(&live_ranges),
                        ));
                    }
                    if span.val(&live_ranges).index() >= num_values {
                        return Err(format!(
                            "{span:?} is for {:?}, but the function only defines {num_values} \
                             values",
                            span.val(&live_ranges),
                        ));
                    }
                    let Some(&block) = inst_block.get(&span.start(&live_ranges).inst()) else {
                        return Err(format!(
                            "{span:?} starts at {:?}, which is in no block",
                            span.start(&live_ranges),
                        ));
                    };
                    let (block_start, block_end) = bounds[&block];
                    if span.start(&live_ranges) < block_start || span.end(&live_ranges) > block_end
                    {
                        return Err(format!(
                            "{span:?} covers {:?}..{:?}, which escapes {block:?}'s bounds \
                             {block_start:?}..{block_end:?}",
                            span.start(&live_ranges),
                            span.end(&live_ranges),
                        ));
                    }
                    spans_of
                        .entry((span.val(&live_ranges), block))
                        .or_default()
                        .push(span);
                    spans_in.get_mut(&block).unwrap().push(span);
                }

                // Construction groups a block's spans by whether they are
                // live-in and/or live-out, rather than by program order, so put
                // each value's pieces back into program order before checking
                // the properties that talk about "the first" and "the last"
                // piece.
                for spans in spans_of.values_mut() {
                    spans.sort_unstable_by_key(|&s| (s.start(&live_ranges), s.end(&live_ranges)));
                }

                // 1b. Each span's uses are inside it, are strictly ascending in
                // `(point, operand)`, and name real operands of that span's
                // value.
                for span in live_ranges.spans() {
                    let mut previous = None;
                    for use_data in span.uses(&live_ranges) {
                        let key = (use_data.point(&live_ranges), use_data.operand(&live_ranges));
                        if use_data.point(&live_ranges) < span.start(&live_ranges)
                            || use_data.point(&live_ranges) >= span.end(&live_ranges)
                        {
                            return Err(format!(
                                "{span:?} covers {:?}..{:?} but has a use at {:?}",
                                span.start(&live_ranges),
                                span.end(&live_ranges),
                                use_data.point(&live_ranges),
                            ));
                        }
                        if previous.is_some_and(|previous| previous >= key) {
                            return Err(format!(
                                "{span:?}'s uses are not in ascending program order: \
                                 {previous:?} is followed by {key:?}",
                            ));
                        }
                        previous = Some(key);
                        let is_real = operands.iter().any(|&(_b, point, i, _kind, val)| {
                            point == use_data.point(&live_ranges)
                                && i == use_data.operand(&live_ranges)
                                && val == span.val(&live_ranges)
                        });
                        if !is_real {
                            return Err(format!(
                                "{span:?} records a use of {:?} at {:?}, operand {}, but no such \
                                 operand exists",
                                span.val(&live_ranges),
                                use_data.point(&live_ranges),
                                use_data.operand(&live_ranges),
                            ));
                        }
                    }
                }

                // 1c. The spans' use ranges tile the uses map exactly: every
                // recorded use belongs to exactly one span.
                let mut ranges: Vec<(usize, usize)> = live_ranges
                    .spans()
                    .map(|span| span.uses(&live_ranges))
                    .filter(|range| !range.is_empty())
                    .map(|range| (range.start.index(), range.end.index()))
                    .collect();
                ranges.sort();
                let mut next = 0;
                for &(start, end) in &ranges {
                    if start != next {
                        return Err(format!(
                            "the spans' use ranges do not tile the uses map: expected the next \
                             range to start at {next}, but it starts at {start}",
                        ));
                    }
                    next = end;
                }
                if next != live_ranges.len_uses() {
                    return Err(format!(
                        "the spans' use ranges cover {next} of the {} recorded uses",
                        live_ranges.len_uses(),
                    ));
                }

                // 1d. One span is one allocation, so all of a span's uses have
                // to be satisfiable by a single location. Fold their
                // constraints the way construction does; folding is exact,
                // because the machine's class list is closed under
                // intersection, so a fold that succeeds really does describe a
                // location that every use accepts. This is the property that
                // eager splitting buys.
                test_input.with_input(|input| -> Result<(), String> {
                    for span in live_ranges.spans() {
                        let mut constraint = OperandConstraint::Any;
                        for use_data in span.uses(&live_ranges) {
                            // Fold the way construction folds, down to
                            // resolving each answer against the instruction it
                            // came from, so that this is a check on where the
                            // spans were cut and not on a second reading of the
                            // same operands.
                            let input_inst = input.func.inst(use_data.point(&live_ranges).inst());
                            let sibling = |j| input_inst.operand(j).constraint();
                            let this = input_inst
                                .operand(use_data.operand(&live_ranges))
                                .constraint();
                            match constraint.merge(
                                &this,
                                input.machine,
                                |_| unreachable!("the folded constraint is always resolved"),
                                &sibling,
                            ) {
                                Some(merged) => constraint = merged.resolved(&sibling),
                                None => {
                                    return Err(format!(
                                        "{span:?} has a use at {:?} constrained to {this:?}, \
                                         which cannot be satisfied along with {constraint:?}, \
                                         the constraints of the uses before it",
                                        use_data.point(&live_ranges),
                                    ));
                                }
                            }
                        }
                    }
                    Ok(())
                })?;

                // 2. A value has at most one span per block, and its spans are
                // pairwise disjoint.
                //
                // Splitting a conflict is what makes it "at most one" rather
                // than "exactly one": a value's pieces within a block are
                // ascending and leave no gap between them, and any two pieces
                // are disjoint except for the single program point that a
                // conflict between two uses of one instruction leaves them
                // sharing, at which both of them record a use. Nothing else may
                // overlap, because a value in two places at once needs a move
                // between them, and there is nowhere to put a move except
                // between two instructions.
                for ((val, block), spans) in &spans_of {
                    for pair in spans.windows(2) {
                        let (previous, next) = (pair[0], pair[1]);
                        if next.start(&live_ranges) < previous.start(&live_ranges)
                            || next.start(&live_ranges) > previous.end(&live_ranges)
                        {
                            return Err(format!(
                                "{val:?}'s spans in {block:?} are out of order or leave a gap: \
                                 {:?}..{:?} is followed by {:?}..{:?}",
                                previous.start(&live_ranges),
                                previous.end(&live_ranges),
                                next.start(&live_ranges),
                                next.end(&live_ranges),
                            ));
                        }
                    }
                }
                for span_a in live_ranges.spans() {
                    for span_b in live_ranges.spans() {
                        if span_a >= span_b || span_a.val(&live_ranges) != span_b.val(&live_ranges)
                        {
                            continue;
                        }
                        let (a_start, a_end) =
                            (span_a.start(&live_ranges), span_a.end(&live_ranges));
                        let (b_start, b_end) =
                            (span_b.start(&live_ranges), span_b.end(&live_ranges));
                        if a_start >= b_end || b_start >= a_end {
                            continue;
                        }

                        // Order the two by `(start, end)` rather than by start
                        // alone, so that two pieces that begin at the same point
                        // -- what a third conflicting use at that point leaves
                        // behind -- are still compared earlier-first.
                        let (first, second) = if (a_start, a_end) <= (b_start, b_end) {
                            (span_a, span_b)
                        } else {
                            (span_b, span_a)
                        };
                        let point = second.start(&live_ranges);
                        let both_use_it = [first, second].into_iter().all(|span| {
                            span.uses(&live_ranges)
                                .into_iter()
                                .any(|u| u.point(&live_ranges) == point)
                        });
                        if first.end(&live_ranges) != point.next_point() || !both_use_it {
                            return Err(format!(
                                "{span_a:?} ({a_start:?}..{a_end:?}) and {span_b:?} \
                                 ({b_start:?}..{b_end:?}) are both for {:?} and overlap by more \
                                 than the one program point at which both of them record a use",
                                span_a.val(&live_ranges),
                            ));
                        }
                    }
                }

                for (block, input_block) in func.blocks() {
                    let (block_start, block_end) = bounds[&block];
                    let last_inst = input_block.insts().next_back().unwrap().0;

                    // 3. A span starts at the block's entry exactly when its
                    // value is live-in there, or is defined by the very first
                    // program point in the block.
                    let starting_at_entry: Set<Val> = spans_in[&block]
                        .iter()
                        .filter(|&&span| span.start(&live_ranges) == block_start)
                        .map(|&span| span.val(&live_ranges))
                        .collect();
                    let mut expected: Set<Val> = block.live_in(&liveness).collect();
                    for &(b, point, _i, kind, val) in &operands {
                        if b == block && point == block_start && matches!(kind, DefUse::Def) {
                            expected.insert(val);
                        }
                    }
                    if starting_at_entry != expected {
                        return Err(format!(
                            "the values whose spans start at {block:?}'s entry are \
                             {starting_at_entry:?}, but should be {expected:?} (its live-in set \
                             plus whatever it defines at {block_start:?})",
                        ));
                    }

                    // 4. Spans that end at the block's exit are exactly those
                    // whose last event is the last thing that happens in the
                    // block. Three ways to be one, and the block's exit is the
                    // exclusive end point in all three:
                    //
                    // * The value is live-out, so its span reaches the exit by
                    //   definition.
                    //
                    // * The value is defined somewhere in the last instruction.
                    //   A def that nothing reads still spans past its own
                    //   instruction, and a def that something reads can only be
                    //   read at the late slot of that same instruction.
                    //
                    // * The value is used at the last instruction's late slot,
                    //   the block's final program point, so the span that
                    //   reaches that use ends just after it.
                    let ending_at_exit: Set<Val> = spans_in[&block]
                        .iter()
                        .filter(|&&span| span.end(&live_ranges) == block_end)
                        .map(|&span| span.val(&live_ranges))
                        .collect();
                    let mut expected: Set<Val> = block.live_out(&liveness).collect();
                    for &(b, point, _i, kind, val) in &operands {
                        if b != block || point.inst() != last_inst {
                            continue;
                        }
                        if matches!(kind, DefUse::Def) || point.pos() == Position::Late {
                            expected.insert(val);
                        }
                    }
                    if ending_at_exit != expected {
                        return Err(format!(
                            "the values whose spans end at {block:?}'s exit are \
                             {ending_at_exit:?}, but should be {expected:?}",
                        ));
                    }

                    // 5. A dead block parameter gets no span at all, while a
                    // live one gets a span starting at the block's entry. This
                    // is the one place we deliberately differ from regalloc2,
                    // which gives a dead parameter a trivial range.
                    for param in input_block.params() {
                        let spans = spans_of.get(&(param, block));
                        if block.is_live_in(&liveness, param) {
                            match spans.map(|s| s.as_slice()) {
                                // A parameter is live-in, so its range starts
                                // at the entry however many pieces the range is
                                // later split into.
                                Some([first, ..]) => {
                                    if first.start(&live_ranges) != block_start {
                                        return Err(format!(
                                            "{param:?} is live-in at {block:?}, but its first \
                                             span starts at {:?} rather than the block's entry \
                                             {block_start:?}",
                                            first.start(&live_ranges),
                                        ));
                                    }
                                }
                                _ => {
                                    return Err(format!(
                                        "{param:?} is live-in at {block:?}, but has {} spans \
                                         there",
                                        spans.map_or(0, |s| s.len()),
                                    ));
                                }
                            }
                        } else if spans.is_some_and(|s| !s.is_empty()) {
                            return Err(format!(
                                "nothing reads {block:?}'s parameter {param:?}, so it is only \
                                 the destination of a move that is never made and needs no \
                                 register, but it still got a span",
                            ));
                        }
                    }

                    // 6. A value with a span in a block is live at that block's
                    // entry or exit, or the block mentions it.
                    for &span in &spans_in[&block] {
                        let val = span.val(&live_ranges);
                        let mentioned = operands
                            .iter()
                            .any(|&(b, _p, _i, _k, v)| b == block && v == val);
                        if !mentioned
                            && !block.is_live_in(&liveness, val)
                            && !block.is_live_out(&liveness, val)
                        {
                            return Err(format!(
                                "{span:?} gives {val:?} a span in {block:?}, which neither \
                                 mentions it nor has it live at either end",
                            ));
                        }
                    }

                    // 7. A value that flows straight through a block has a span
                    // that tiles the whole block, with no gap at either end.
                    for val_index in 0..num_values {
                        let val = Val::try_new(val_index).unwrap();
                        if !block.is_live_in(&liveness, val) || !block.is_live_out(&liveness, val) {
                            continue;
                        }
                        let Some(spans) = spans_of.get(&(val, block)).filter(|s| !s.is_empty())
                        else {
                            return Err(format!(
                                "{val:?} is live across all of {block:?}, but does not have any \
                                 span there",
                            ));
                        };
                        // Property 2 has already established that the pieces
                        // are ascending and leave no gap, so tiling the block is
                        // the first one starting at its entry and the last one
                        // ending at its exit.
                        let first = *spans.first().unwrap();
                        let last = *spans.last().unwrap();
                        if first.start(&live_ranges) != block_start
                            || last.end(&live_ranges) != block_end
                        {
                            return Err(format!(
                                "{val:?} is live across all of {block:?}, but its spans cover \
                                 only {:?}..{:?} of {block_start:?}..{block_end:?}",
                                first.start(&live_ranges),
                                last.end(&live_ranges),
                            ));
                        }
                    }
                }

                // 8. Every operand is accounted for: a def starts its value's
                // span exactly at its own program point, a use is strictly
                // inside one, and either way the span records it.
                for &(block, point, i, kind, val) in &operands {
                    let Some(spans) = spans_of.get(&(val, block)).filter(|s| !s.is_empty()) else {
                        return Err(format!(
                            "{block:?} has an operand at {point:?} naming {val:?}, but {val:?} \
                             does not have any span in {block:?}",
                        ));
                    };
                    match kind {
                        // A def is where the value's range in the block begins,
                        // so it is the first piece that starts at its point.
                        DefUse::Def => {
                            let first = *spans.first().unwrap();
                            if first.start(&live_ranges) != point {
                                return Err(format!(
                                    "{val:?} is defined at {point:?} in {block:?}, but its first \
                                     span there starts at {:?}",
                                    first.start(&live_ranges),
                                ));
                            }
                        }
                        // A use only has to fall inside one of the pieces.
                        DefUse::Use => {
                            let covered = spans.iter().any(|&span| {
                                point >= span.start(&live_ranges) && point < span.end(&live_ranges)
                            });
                            if !covered {
                                return Err(format!(
                                    "{val:?} is used at {point:?} in {block:?}, but none of its \
                                     spans there cover that point",
                                ));
                            }
                        }
                    }
                    let recorded = spans.iter().any(|&span| {
                        span.uses(&live_ranges)
                            .into_iter()
                            .any(|u| u.point(&live_ranges) == point && u.operand(&live_ranges) == i)
                    });
                    if !recorded {
                        return Err(format!(
                            "operand {i} of {point:?} names {val:?}, but no span of {val:?} in \
                             {block:?} records it as one of its uses",
                        ));
                    }
                }

                // 9. Each use's weight is the cost model applied to that
                // use's own operand, in that use's own block, and a span flags
                // a fixed use exactly when one of its uses names a class that
                // holds a single register.
                test_input.with_input(|input| -> Result<(), String> {
                    for span in live_ranges.spans() {
                        let val = span.val(&live_ranges);
                        let remat = remat_scale(input.func.value(val).remat_cost());
                        let mut any_fixed = false;

                        for u in span.uses(&live_ranges) {
                            let point = u.point(&live_ranges);
                            let operand = u.operand(&live_ranges);
                            let block = inst_block[&point.inst()];
                            let frequency = func.block(block).frequency().as_f32();

                            let input_inst = input.func.inst(point.inst());
                            let sibling = |j| input_inst.operand(j).constraint();
                            let raw = input_inst.operand(operand).constraint();
                            let resolved = raw.resolved(&sibling);

                            let expected = SpillWeight::new(
                                (use_spill_cost(input, val, raw, resolved) * remat * frequency)
                                    .max(0.0),
                            );
                            let actual = u.weight(&live_ranges);
                            if actual != expected {
                                return Err(format!(
                                    "{u:?} (operand {operand} of {point:?}, in {block:?}) weighs \
                                     {}, but the cost model says {}",
                                    actual.as_f32(),
                                    expected.as_f32(),
                                ));
                            }
                            if !actual.as_f32().is_finite() || actual.as_f32() < 0.0 {
                                return Err(format!(
                                    "{u:?} weighs {}, which is not a weight",
                                    actual.as_f32(),
                                ));
                            }

                            any_fixed |= match resolved {
                                OperandConstraint::Reg(class) => class.is_singleton(input.machine),
                                _ => false,
                            };
                        }

                        if span.has_fixed_use(&live_ranges) != any_fixed {
                            return Err(format!(
                                "{span:?} reports has_fixed_use = {}, but {} of its uses names a \
                                 class holding a single register",
                                span.has_fixed_use(&live_ranges),
                                if any_fixed { "one" } else { "none" },
                            ));
                        }
                    }
                    Ok(())
                })?;

                // 10. Constructing twice gives exactly the same spans and uses.
                let (_, again) = analyze_spans(test_input)?;
                let first: Vec<_> = live_ranges.spans.as_slice().to_vec();
                let second: Vec<_> = again.spans.as_slice().to_vec();
                if first != second {
                    return Err("constructing twice gave different spans".to_string());
                }
                if live_ranges.len_uses() != again.len_uses() {
                    return Err("constructing twice gave different uses".to_string());
                }
                for index in 0..live_ranges.len_uses() {
                    let u = Use::try_new(index).unwrap();
                    if live_ranges.uses[u] != again.uses[u] {
                        return Err(format!("constructing twice gave {u:?} different data"));
                    }
                }

                // 11. Both halves reset cleanly, including the scratch that
                // span construction borrows from `Liveness`.
                let mut live_ranges = live_ranges;
                live_ranges.reset();
                if !live_ranges.is_reset() {
                    return Err("`LiveRanges::is_reset` is false after `reset`".to_string());
                }
                liveness.reset();
                if !liveness.is_reset() {
                    return Err("`Liveness::is_reset` is false after `reset`".to_string());
                }

                Ok(())
            })
    }
}
