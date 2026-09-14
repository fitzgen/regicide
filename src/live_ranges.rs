//! Constructs live ranges and bundles.

use crate::counts::Counts;
use crate::entity::{
    Block, Entity, EntityRange, EntityRepr, Inst, PrimaryMap, Region, SecondaryMap, Val, WideInt,
};
use crate::error::IResult;
use crate::events::EventsLog;
use crate::input::{
    DefUse, Input, InputBlock, InputFunction, InputInst, InputValue, OperandConstraint, Position,
    RematCost,
};
use crate::liveness::{Liveness, block_first_inst, block_last_inst};
use crate::machine::{Machine, RegClassMembers};
use crate::output::{OutputInner, RegAllocation};
use crate::packed_float::PackedPositiveFloat;
use crate::timing::Timing;
use crate::{RegClass, RegSet};

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

/// A point serializes as the instruction and half it names, never as the packed
/// bits.
#[cfg(feature = "serialize")]
impl<E> serde::Serialize for LivePoint<E>
where
    E: EntityRepr,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeStruct;
        let mut s = serializer.serialize_struct("LivePoint", 2)?;
        s.serialize_field("inst", &self.inst())?;
        s.serialize_field("pos", &self.pos())?;
        s.end()
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

    /// This point's packed representation, for packing it inside a larger key.
    ///
    /// Always fits in 32 bits, as `E::Wide` is at most a `u32`.
    #[inline]
    pub fn to_bits(self) -> usize {
        self.bits.to_usize()
    }

    /// Reconstruct a point from `Self::to_bits`.
    #[inline]
    pub fn from_bits(bits: usize) -> Self {
        debug_assert!(<E::Wide as WideInt>::try_from_usize(bits).is_some());
        LivePoint {
            bits: E::Wide::from_usize(bits),
        }
    }

    /// The last instruction boundary at or before this point: `(I, Early)`,
    /// where `I` is this point's instruction.
    #[inline]
    pub fn inst_boundary_at_or_before(self) -> Self {
        match self.pos() {
            Position::Early => self,
            Position::Late => self.prev_point(),
        }
    }

    /// The first instruction boundary strictly after this point: `(I + 1,
    /// Early)`, where `I` is this point's instruction.
    #[inline]
    pub fn inst_boundary_after(self) -> Self {
        let next = self.next_point();
        match next.pos() {
            Position::Early => next,
            Position::Late => next.next_point(),
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

#[cfg(feature = "serialize")]
impl serde::Serialize for SpillWeight {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let weight = self.as_f32();
        serializer.serialize_f32(if weight.is_finite() { weight } else { 0.0 })
    }
}

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

/// Do the spans `[.., end)` and `[start, ..)` touch in the middle of an
/// instruction?
#[inline]
pub(crate) fn touch_mid_inst<E>(end: LivePoint<E>, start: LivePoint<E>) -> bool
where
    E: EntityRepr,
{
    debug_assert!(end <= start);
    end.pos() == Position::Late && start.inst() == end.inst()
}

/// Is the described bundle minimal?
///
/// `len_cuttable_gaps` is the number of places that it could be cut.
///
/// `len_uses` is the number of uses inside the bundle.
///
/// `len_insts` is the number of distinct instructions the bundle covers.
///
/// A minimal bundle is one that cannot be meaningfully split any smaller:
///
/// * A bundle with a cuttable gap between two of its spans in is not minimal:
///   we could split out a bundle for each span.
///
///   (Note that not all gaps between spans are cuttable: two spans may be tied
///   together via, e.g., `Reuse` constraints. See `LiveSpan::is_tied_to` for
///   details.)
///
/// * Bundles with zero uses are minimal as soon as they have no cuttable gap
///   between spans.
///
///   (We could *technically* keep shaving off single-instruction spans off of
///   it, but this is useless. A span is always within one basic block, so if we
///   have so much interference that we will spill any of them to the stack, we
///   might as well just spill the whole span to the stack, since zero uses
///   means we aren't using the value in this block anyways. Even worse, it
///   would also open the door to repeatedly spilling and reloading a value in a
///   basic block where it isn't even used, adding more cost than if we just
///   spilled the whole zero-use span from the start!)
///
/// * Bundles with uses are minimal once they cover exactly one instruction: we
///   can't make them any smaller while still covering their uses and allowing
///   for moves to be inserted before or after them (which can only happen
///   between instructions, not in the middle of one).
///
///   (Note that a bundle need not cover that one instruction with a single
///   span: for example, two spans that are reuse-tied together can both cover
///   the same instruction, and the bundle could still be minimal.)
pub(crate) fn is_minimal_bundle(
    len_cuttable_gaps: usize,
    len_uses: usize,
    len_insts: usize,
) -> bool {
    debug_assert!(
        len_insts >= 1,
        "a bundle always covers at least one instruction",
    );
    len_cuttable_gaps == 0 && (len_uses == 0 || len_insts == 1)
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

    /// The registers this bundle is currently allocated to.
    reg_allocation: Option<RegAllocation<E>>,

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
        input: &Input<'_, impl InputFunction>,
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

        LiveBundle::new(
            self,
            input,
            output,
            region,
            constraint,
            EntityRange { start, end },
        )
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
        events: &mut EventsLog<E>,
        liveness: &mut Liveness<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        let _timing = Timing::new("live ranges");

        // Borrow the two maps separately so that `Liveness::block_spans` can
        // append to `uses` while we push into `spans`.
        let Self {
            uses,
            spans,
            block_spans,
            live_in_spans,
            live_out_spans,
            block_uses,
            use_span,
            ..
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

            #[cfg(feature = "visualizer")]
            let events_start = events.len();

            for span in liveness.block_spans(input.func, block, uses, output)? {
                push_span_and_split_conflicts(
                    input, uses, spans, counts, events, span, block, block_end, output,
                )?;
            }
            let uses_end = uses.next_key(output)?;
            let spans_end = spans.next_key(output)?;

            // Sort this block's spans into buckets so that live-in and live-out
            // spans are both in a contiguous run.
            //
            // See `live_in_spans` and `live_out_spans`.
            let sort_key = |data: &LiveSpanData<E>| {
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
                (bucket, data.start, data.end, data.val, data.uses.start)
            };

            let block_span_range = spans_start.index()..spans_end.index();

            // The events above name span keys that the sort is about to
            // invalidate, so remember the order they were pushed in.
            #[cfg(feature = "visualizer")]
            let keys_before = alloc::vec::Vec::from_iter(
                spans.as_slice()[block_span_range.clone()]
                    .iter()
                    .map(sort_key),
            );

            spans.as_mut_slice()[block_span_range.clone()].sort_unstable_by_key(sort_key);

            #[cfg(feature = "visualizer")]
            remap_block_span_events(
                events,
                events_start,
                spans_start,
                &keys_before,
                &alloc::vec::Vec::from_iter(
                    spans.as_slice()[block_span_range].iter().map(sort_key),
                ),
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

    /// Does this use demand one particular register?
    ///
    /// Resolving the operand's constraint needs its siblings, which is why
    /// this takes `input` rather than reading anything cached.
    pub(crate) fn is_fixed(
        self,
        live_ranges: &LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
    ) -> bool {
        let input_inst = input
            .func
            .inst(self.point(live_ranges).inst().with_repr32());
        let sibling = |j| input_inst.operand(j).constraint();
        input_inst
            .operand(self.operand(live_ranges))
            .constraint()
            .resolved(&sibling)
            .is_fixed(input.machine)
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

    /// The subrange of this span's uses that sit at `point`.
    #[inline]
    pub(crate) fn uses_at(
        self,
        live_ranges: &LiveRanges<E>,
        point: LivePoint<E>,
    ) -> EntityRange<Use<E>> {
        let uses = self.uses(live_ranges);
        if uses.is_empty() {
            return EntityRange::empty();
        }

        let indices = uses.indices();
        let sorted = &live_ranges.uses.as_slice()[indices.clone()];
        let first = sorted.partition_point(|u| u.point < point);
        let last = sorted.partition_point(|u| u.point <= point);

        EntityRange {
            start: Use::try_new(indices.start + first).unwrap(),
            end: Use::try_new(indices.start + last).unwrap(),
        }
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

    /// The block this span lies within; spans never cross a block boundary.
    pub(crate) fn block(self, func: &impl InputFunction, live_ranges: &LiveRanges<E>) -> Block<E> {
        func.inst(self.start(live_ranges).inst().with_repr32())
            .block()
            .with_repr::<E>()
            .expect("every block index already fit in `E` in the earlier passes")
    }

    /// Does this span contain a use with a fixed register constraint?
    #[inline]
    pub(crate) fn has_fixed_use(self, live_ranges: &LiveRanges<E>) -> bool {
        live_ranges.spans[self].flags & SPAN_HAS_FIXED_USE != 0
    }

    /// Must this span stay in the same bundle as `prev`, the span immediately
    /// before it in some bundle?
    ///
    /// The spans must stay together when they touch in the middle of an
    /// instruction (so there is no place to put a move instruction between
    /// them, if necessary) and either:
    ///
    /// * the spans are associated with the same value, or
    ///
    /// * one span has a use with a `Reuse(_)` constraint naming a use in the
    ///   other span.
    ///
    /// Any other scenario either has an instruction boundary between the two
    /// spans where we can place any moves between them, if necessary, or else
    /// there is nothing that could demand a move between the two spans.
    pub(crate) fn is_tied_to(
        self,
        live_ranges: &LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
        prev: LiveSpan<E>,
    ) -> bool {
        let at = self.start(live_ranges);
        debug_assert!(prev.end(live_ranges) <= at);
        if !touch_mid_inst(prev.end(live_ranges), at) {
            return false;
        }

        // Two pieces of one value need the value moved from one to the other.
        if self.val(live_ranges) == prev.val(live_ranges) {
            return true;
        }

        // A span only ever begins at a def or a block's first instruction, and
        // a block begins at an `Early` point, so a span starting in the middle
        // of an instruction (a `Late` point) must begin with its def.
        debug_assert_eq!(at.pos(), Position::Late);

        let early = at.inst_boundary_at_or_before();
        debug_assert_eq!(early.inst(), at.inst());

        let input_inst = input.func.inst(at.inst().with_repr32());
        let reuses = |operand: usize, target: usize| {
            matches!(
                input_inst.operand(operand).constraint(),
                OperandConstraint::Reuse(i) if i == target
            )
        };

        let late_uses = self.uses_at(live_ranges, at);
        let early_uses = prev.uses_at(live_ranges, early);

        late_uses.into_iter().any(|late| {
            let late = late.operand(live_ranges);
            early_uses.into_iter().any(|early| {
                let early = early.operand(live_ranges);
                // Validation rules out reuse chains, so at most one of these
                // two can hold; checking both saves us from depending on which
                // side of the instruction the reusing operand sits on.
                reuses(late, early) || reuses(early, late)
            })
        })
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
            let use_constraint = reuse_aware_constraint(
                input,
                u.point(live_ranges).inst().with_repr32(),
                u.operand(live_ranges),
            );
            constraint = constraint
                .merge_resolved(&use_constraint, input.machine)
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
        input: &Input<'_, impl InputFunction>,
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
                reg_allocation: None,
                weight_and_flags: 0,
            },
        )?;
        debug_assert_eq!(pushed, bundle);

        bundle.recompute_weight_and_flags(live_ranges, input);
        Ok(bundle)
    }

    /// Recompute the cached `has_fixed_uses`, `is_minimal` and spill weight
    /// from the spans this bundle currently holds.
    fn recompute_weight_and_flags(
        self,
        live_ranges: &mut LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
    ) {
        let mut has_fixed_uses = false;
        let mut total_use_cost = 0.0;
        let mut sum_len_insts = 0;
        let mut len_uses = 0;

        // How many of the gaps between this bundle's spans a cut could go in,
        // and how many instructions two of its spans both touch. Both come out
        // of walking each adjacent pair, and together they are what decides
        // minimality.
        let mut len_cuttable_gaps = 0;
        let mut shared_insts = 0;
        let mut prev: Option<LiveSpan<E>> = None;

        for span in self.spans(live_ranges) {
            has_fixed_uses |= span.has_fixed_use(live_ranges);
            let uses = span.uses(live_ranges);
            len_uses += uses.len();
            total_use_cost += uses
                .into_iter()
                .map(|u| u.weight(live_ranges).as_f32())
                .sum::<f32>();
            sum_len_insts += span.len_insts(live_ranges);

            if let Some(prev) = prev {
                if touch_mid_inst(prev.end(live_ranges), span.start(live_ranges)) {
                    // The two spans meet in the middle of an instruction, so
                    // they both cover it, and a cut between them is only legal
                    // if it demands no move.
                    shared_insts += 1;
                    if !span.is_tied_to(live_ranges, input, prev) {
                        len_cuttable_gaps += 1;
                    }
                } else {
                    len_cuttable_gaps += 1;
                }
            }
            prev = Some(span);
        }

        // The spill weight blends a use count with a use *density*, so it wants
        // the summed lengths; minimality wants the instructions actually
        // covered, counting a shared one once.
        let len_insts = sum_len_insts - shared_insts;

        let mut weight_and_flags = PackedPositiveFloat::<u32, BUNDLE_SPILL_WEIGHT_BITS>::new(
            normalize_spill_weight(total_use_cost, sum_len_insts),
        )
        .bits();
        debug_assert_eq!(weight_and_flags & !BUNDLE_SPILL_WEIGHT_MASK, 0);
        if is_minimal_bundle(len_cuttable_gaps, len_uses, len_insts) {
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

    pub(crate) fn num_vals(self, live_ranges: &LiveRanges<E>) -> usize {
        assert!(
            cfg!(any(feature = "trace-log", feature = "visualizer")),
            "this method is inefficient and only exists for diagnostics",
        );
        let mut vals = alloc::collections::BTreeSet::new();
        for span in self.spans(live_ranges) {
            vals.insert(span.val(live_ranges));
        }
        vals.len()
    }

    /// Split this bundle in two between spans.
    ///
    /// This `LiveBundle` will retain `spans[..i]` and the return value is a new
    /// `LiveBundle` that contains `spans[i..]`.
    ///
    /// ```text
    ///                  bundle1
    /// +----------------------------------------+
    /// | span0      span1        span2          |
    /// | [==========)            [============) |
    /// |            [======)                    |
    /// +----------------------------------------+
    ///
    ///                      |
    ///                      |
    ///                      |
    ///                split_at_span(2)
    ///                      |
    ///                      |
    ///                      V
    ///
    ///         bundle1                 bundle2
    /// +---------------------+    +----------------+
    /// | span0      span1    |    | span2          |
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
        events: &mut EventsLog<E>,
        output: &mut OutputInner<E>,
        i: usize,
    ) -> IResult<LiveBundle<E>> {
        let data = &live_ranges.bundles[self];
        let (region, spans) = (data.region, data.spans);
        debug_assert!(data.reg_allocation.is_none());

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
        self.recompute_weight_and_flags(live_ranges, input);
        self.recompute_constraint(live_ranges, input);

        for index in suffix {
            let span = live_ranges.bundle_spans_storage[index];
            debug_assert_eq!(live_ranges.span_bundle[span], Some(self));
            live_ranges.span_bundle[span] = None;
        }

        // When the two halves touch in the middle of an instruction, the new
        // bundle would begin at a `Late` point, where no move can be inserted,
        // so move the new bundle's start up to the instruction boundary.
        let first = live_ranges.bundle_spans_storage[mid];
        let start = live_ranges.spans[first].start;
        if start.pos() == Position::Late {
            live_ranges.spans[first].start = start.inst_boundary_at_or_before();
        }

        let new = LiveBundle::new(
            live_ranges,
            input,
            output,
            region,
            OperandConstraint::Any,
            suffix,
        )?;
        new.recompute_constraint(live_ranges, input);
        event!(
            events,
            BundleSplit {
                parent: self,
                child: new,
                region,
            }
        );
        Ok(new)
    }

    /// Split this bundle in two within one of its spans.
    ///
    /// `spans[i]` is divided at `at` into `[start, at)` and `[at, end)`. This
    /// `LiveBundle` retains `spans[..i]` plus `[start, at)`; the returned
    /// `LiveBundle` holds `[at, end)` plus `spans[i + 1..]`.
    ///
    /// ```text
    ///                     bundle1
    ///   +-----------------------------------------+
    ///   | span0      span1     span2              |
    ///   | [==========)         [===U==V=========) |
    ///   |            [======)                     |
    ///   +-----------------------------------------+
    ///
    ///                          |
    ///                          |
    ///                 split_at_point(2, V)
    ///                          |
    ///                          V
    ///
    ///           bundle1                        bundle2
    /// +-------------------------------+    +--------------+
    /// | span0      span1     span2    |    | span3        |
    /// | [==========)         [===U==) |    | [V=========) |
    /// |            [======)           |    |              |
    /// +-------------------------------+    +--------------+
    /// ```
    ///
    /// `at` must be at `Position::Early`, because a move cannot be inserted in
    /// the middle of an instruction, and additionally must fall within
    /// `spans[i]` such that neither piece is empty.
    pub(crate) fn split_at_point(
        self,
        live_ranges: &mut LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
        events: &mut EventsLog<E>,
        output: &mut OutputInner<E>,
        i: usize,
        at: LivePoint<E>,
    ) -> IResult<LiveBundle<E>> {
        let data = &live_ranges.bundles[self];
        let (region, spans) = (data.region, data.spans);
        debug_assert!(data.reg_allocation.is_none());
        debug_assert_eq!(at.pos(), Position::Early);

        let indices = spans.indices();
        let n = indices.len();
        debug_assert!(i < n);

        #[cfg(debug_assertions)]
        let orig_len_spans = self.spans(live_ranges).len();

        #[cfg(debug_assertions)]
        let orig_len_uses = self
            .spans(live_ranges)
            .map(|s| s.uses(live_ranges).len())
            .sum::<usize>();

        let slot = |j: usize| BundleSpansStorageIndex::try_new(indices.start + j).unwrap();

        let old = live_ranges.bundle_spans_storage[slot(i)];
        let LiveSpanData {
            start,
            end,
            uses,
            val,
            flags: _,
        } = live_ranges.spans[old];
        debug_assert!(start < at);
        debug_assert!(at < end);

        // Divide the span's uses.
        let mid = if uses.is_empty() {
            uses.end
        } else {
            let indices = uses.indices();
            let sorted = &live_ranges.uses.as_slice()[indices.clone()];
            let offset = sorted.partition_point(|u| u.point < at);
            Use::try_new(indices.start + offset).unwrap()
        };
        let lo_uses = EntityRange {
            start: uses.start,
            end: mid,
        };
        let hi_uses = EntityRange {
            start: mid,
            end: uses.end,
        };

        let is_fixed = |live_ranges: &LiveRanges<E>, range: EntityRange<Use<E>>| {
            range.into_iter().any(|u| u.is_fixed(live_ranges, input))
        };
        let lo_is_fixed = is_fixed(live_ranges, lo_uses);
        let hi_is_fixed = is_fixed(live_ranges, hi_uses);

        // Rewrite the divided span in place as the first piece; because we are
        // rewriting this span in place, its uses are already associated with it
        // and its `span_bundle` entry remains valid.
        live_ranges.spans[old] = LiveSpanData::new(start, at, val, lo_uses, lo_is_fixed);

        // The new span takes second piece.
        let new_span = live_ranges.spans.push(
            output,
            LiveSpanData::new(at, end, val, hi_uses, hi_is_fixed),
        )?;

        // And the new span's uses need to be reassociated with it.
        for u in hi_uses {
            live_ranges.use_span[u] = new_span;
        }

        event!(
            events,
            SpanSplit {
                parent: old,
                first: old,
                second: new_span,
                at,
                val,
            }
        );

        let prefix_len_spans = i + 1;
        let suffix_len_spans = n - i;

        #[cfg(debug_assertions)]
        {
            assert!(prefix_len_spans <= orig_len_spans);
            assert!(suffix_len_spans <= orig_len_spans);
        }

        // Now we need to fix the range of spans that each new bundle
        // covers. Bundles reference their spans indirectly by naming a
        // contiguous range of `bundle_spans_storage`. Unlike when splitting
        // between spans, we cannot reuse the same range of
        // `bundle_spans_storage` elements for both bundles, giving a disjoint
        // subrange to each of them, because splitting a span in two means we
        // now have `n + 1` spans but only `n` elements inside
        // `bundle_spans_storage`. But *one* of the two halves can reuse the old
        // `bundle_spans_storage` elements. We let the half with more spans
        // reuse the storage, so that we minimize copying and
        // `bundle_spans_storage` growth.
        let (prefix_spans, suffix_spans) = if prefix_len_spans <= suffix_len_spans {
            // Prefix is shorter: copy its spans to the end of
            // `bundle_spans_storage`. Its last span is the first half of the
            // split span, which was modified in place, so we don't need to do
            // anything for the prefix beyond copying its subslice.
            let start = live_ranges.bundle_spans_storage.next_key(output)?;
            for j in 0..prefix_len_spans {
                let span = live_ranges.bundle_spans_storage[slot(j)];
                live_ranges.bundle_spans_storage.push(output, span)?;
            }
            let end = live_ranges.bundle_spans_storage.next_key(output)?;
            // However, the suffix's first span needs to point at the new span
            // (the second half of the split span).
            live_ranges.bundle_spans_storage[slot(i)] = new_span;
            (
                EntityRange { start, end },
                EntityRange {
                    start: slot(i),
                    end: spans.end,
                },
            )
        } else {
            // Suffix is shorter, so push its first span (the new span, i.e. the
            // second half of the split span) to `bundle_spans_storage` and then
            // copy over its tail of spans afterwards.
            let start = live_ranges.bundle_spans_storage.next_key(output)?;
            live_ranges.bundle_spans_storage.push(output, new_span)?;
            for j in prefix_len_spans..n {
                let span = live_ranges.bundle_spans_storage[slot(j)];
                live_ranges.bundle_spans_storage.push(output, span)?;
            }
            let end = live_ranges.bundle_spans_storage.next_key(output)?;
            (
                EntityRange {
                    start: spans.start,
                    end: slot(prefix_len_spans),
                },
                EntityRange { start, end },
            )
        };
        debug_assert_eq!(prefix_spans.indices().len(), prefix_len_spans);
        debug_assert_eq!(suffix_spans.indices().len(), suffix_len_spans);

        live_ranges.bundles[self].spans = prefix_spans;
        self.recompute_weight_and_flags(live_ranges, input);
        self.recompute_constraint(live_ranges, input);

        // Clear out the old span-to-bundle associations.
        for index in suffix_spans {
            let span = live_ranges.bundle_spans_storage[index];
            debug_assert!(span == new_span || live_ranges.span_bundle[span] == Some(self));
            live_ranges.span_bundle[span] = None;
        }
        let new = LiveBundle::new(
            live_ranges,
            input,
            output,
            region,
            OperandConstraint::Any,
            suffix_spans,
        )?;
        new.recompute_constraint(live_ranges, input);

        #[cfg(debug_assertions)]
        {
            // Splitting moves uses between the two bundles but never creates or
            // destroys one.
            let self_len_uses = self
                .spans(live_ranges)
                .map(|s| s.uses(live_ranges).len())
                .sum::<usize>();
            let new_len_uses = new
                .spans(live_ranges)
                .map(|s| s.uses(live_ranges).len())
                .sum::<usize>();
            debug_assert_eq!(self_len_uses + new_len_uses, orig_len_uses);
        }

        event!(
            events,
            BundleSplit {
                parent: self,
                child: new,
                region,
            }
        );

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

    /// The register class that this bundle's values naturally belong within.
    ///
    /// This is where the bundle may live absent any constraint from its uses.
    pub(crate) fn value_reg_class(
        self,
        live_ranges: &LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
    ) -> RegClass {
        let class_of = |span: LiveSpan<E>| {
            let val = span.val(live_ranges).with_repr32();
            input.func.value(val).reg_class()
        };

        let mut spans = self.spans(live_ranges);
        let first = spans
            .next()
            .expect("a bundle always holds at least one span");
        let rc = class_of(first);

        debug_assert!(
            spans.all(|span| class_of(span) == rc),
            "the values in one bundle always share a register class",
        );

        rc
    }

    /// The subset of this bundle's constraint's registers that it would prefer
    /// to be allocated within, if any.
    ///
    /// Empty means no preference.
    #[inline]
    pub(crate) fn preference(self, live_ranges: &LiveRanges<E>) -> &RegSet {
        &live_ranges.bundles[self].preference
    }

    /// The registers this bundle is currently allocated to.
    ///
    /// `None` until region allocation gives it a register, and forever for a
    /// bundle that lives in memory: a bundle can hold several coalesced values
    /// while stack homes are per-value, so see `Val::stack_home` for those.
    #[inline]
    pub(crate) fn reg_allocation(self, live_ranges: &LiveRanges<E>) -> Option<RegAllocation<E>> {
        live_ranges.bundles[self].reg_allocation
    }

    /// Record where region allocation decided to put this bundle.
    #[inline]
    pub(crate) fn set_reg_allocation(
        self,
        live_ranges: &mut LiveRanges<E>,
        alloc: RegAllocation<E>,
    ) {
        live_ranges.bundles[self].reg_allocation = Some(alloc);
    }

    /// Forget where this bundle was allocated, because it was just evicted from
    /// there.
    #[inline]
    pub(crate) fn clear_reg_allocation(self, live_ranges: &mut LiveRanges<E>) {
        live_ranges.bundles[self].reg_allocation = None;
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

    /// Bias this bundle towards the registers that `constraint` names, on
    /// behalf of `from`.
    pub(crate) fn hint(
        self,
        live_ranges: &mut LiveRanges<E>,
        events: &mut EventsLog<E>,
        machine: &Machine,
        constraint: OperandConstraint,
        from: Option<LiveBundle<E>>,
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

        let class = match self
            .constraint(live_ranges)
            .merge_resolved(&constraint, machine)
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

        // Via `add_hint`, so that every hint is logged in one place.
        self.add_hint(live_ranges, events, class.member_set(machine), from);
    }

    /// Bias this bundle towards `regs`, on behalf of `from`.
    pub(crate) fn add_hint(
        self,
        live_ranges: &mut LiveRanges<E>,
        events: &mut EventsLog<E>,
        regs: &RegSet,
        from: Option<LiveBundle<E>>,
    ) {
        if regs.is_empty() {
            return;
        }
        live_ranges.bundles[self].add_hint(regs.clone());
        event!(
            events,
            BundleHint {
                bundle: self,
                hint: regs.clone(),
                from,
            }
        );
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
                .merge_resolved(&span_constraint, input.machine)
                .expect("the spans of a bundle never conflict, so neither do any subset of them");
        }
        live_ranges.bundles[self].constraint = constraint;
    }
}

impl<E> Block<E>
where
    E: EntityRepr,
{
    /// The program point at which this block begins.
    pub(crate) fn start_point(self, input: &Input<'_, impl InputFunction>) -> LivePoint<E> {
        let input_block = input.func.block(self.with_repr32());
        let first_inst = block_first_inst(&input_block)
            .with_repr::<E>()
            .expect("every instruction index already fit in `E` in the earlier passes");
        LivePoint::new(first_inst, Position::Early)
    }

    /// The program point just past the end of this block.
    pub(crate) fn end_point(self, input: &Input<'_, impl InputFunction>) -> LivePoint<E> {
        let input_block = input.func.block(self.with_repr32());
        let last = block_last_inst(&input_block)
            .with_repr::<E>()
            .expect("every instruction index already fit in `E` in the earlier passes");
        LivePoint::new(last, Position::Late).next_point()
    }

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
    pub(crate) fn uses(self, live_ranges: &LiveRanges<E>) -> EntityRange<Use<E>> {
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

/// Get the constraint that an instruction's `operand` places on its span.
///
/// Resolves a `Reuse` to its target's constraint, narrows both halves of a tie
/// by the same sibling reads, and then strengthens both to demand a register:
/// a stack home belongs to one value alone and so cannot be reused for two
/// different values.
fn reuse_aware_constraint(
    input: &Input<'_, impl InputFunction>,
    inst: Inst,
    operand: usize,
) -> OperandConstraint {
    let input_inst = input.func.inst(inst);
    let constraint = input_inst.operand(operand).constraint();
    let mut resolved = constraint.resolved(|j| input_inst.operand(j).constraint());

    // The operand whose reads decide where the tie lives: the target for a
    // `Reuse`, and the operand itself when some `Reuse` names it.
    let tie_target = match constraint {
        OperandConstraint::Reuse(target) => Some(target),
        _ if is_reuse_target(&input_inst, operand) => Some(operand),
        _ => None,
    };

    // A `Reuse` is defined in the register its target is read from, so a
    // sibling reading that value in a register at that point under a narrower
    // class than the target's own operand does constrains the definition too.
    // Both halves fold those siblings in identically: narrowing only the
    // definition would leave the target free to fold into an earlier piece the
    // definition cannot share, and the tie would be quietly broken.
    if let Some(target) = tie_target {
        let target = input_inst.operand(target);
        for other in input_inst.operands() {
            if other.kind() != DefUse::Use
                || other.val() != target.val()
                || other.pos() != target.pos()
            {
                continue;
            }
            let OperandConstraint::Reg(other) = other
                .constraint()
                .resolved(|j| input_inst.operand(j).constraint())
            else {
                continue;
            };
            resolved = match resolved {
                OperandConstraint::Any => OperandConstraint::Reg(other),
                OperandConstraint::Reg(rc) => rc
                    .intersect(input.machine, other)
                    .map_or(resolved, OperandConstraint::Reg),
                resolved => resolved,
            };
        }
    }

    let is_tied = tie_target.is_some();
    match resolved {
        OperandConstraint::Any if is_tied => {
            let val = input_inst.operand(operand).val().unwrap();
            OperandConstraint::Reg(input.func.value(val).reg_class())
        }
        resolved => resolved,
    }
}

/// Rewrite the provisional span keys in the events a block's span construction
/// logged, after the sort has moved those spans.
#[cfg(feature = "visualizer")]
fn remap_block_span_events<E, K>(
    events: &mut EventsLog<E>,
    events_start: usize,
    spans_start: LiveSpan<E>,
    keys_before: &[K],
    keys_after: &[K],
) where
    E: EntityRepr,
    K: Ord,
{
    let remap = |span: LiveSpan<E>| -> LiveSpan<E> {
        let old = span.index() - spans_start.index();
        let new = keys_after.binary_search(&keys_before[old]).unwrap();
        LiveSpan::try_new(spans_start.index() + new).unwrap()
    };

    for event in events.iter_mut_from(events_start) {
        match event {
            crate::events::Event::SpanConstructed { span, .. } => *span = remap(*span),
            crate::events::Event::EagerSplit { before, .. } => *before = remap(*before),
            crate::events::Event::ReuseSplit { before, copy, .. } => {
                *before = before.map(remap);
                *copy = remap(*copy);
            }
            _ => unreachable!("only span construction has run; unexpected event: {event:?}"),
        }
    }
}

/// Push a span covering `start..end` of `val`, holding the uses in
/// `uses_start..uses_end`.
fn push_span<E>(
    spans: &mut PrimaryMap<LiveSpan<E>, LiveSpanData<E>>,
    output: &mut OutputInner<E>,
    events: &mut EventsLog<E>,
    val: Val<E>,
    (start, end): (LivePoint<E>, LivePoint<E>),
    (uses_start, uses_end): (Use<E>, Use<E>),
    constraint: OperandConstraint,
    has_fixed_use: bool,
    block: Block<E>,
) -> IResult<LiveSpan<E>>
where
    E: EntityRepr,
{
    let uses = EntityRange {
        start: uses_start,
        end: uses_end,
    };
    let span = spans.push(
        output,
        LiveSpanData::new(start, end, val, uses, has_fixed_use),
    )?;
    event!(
        events,
        SpanConstructed {
            span,
            val,
            start,
            end,
            block,
            num_uses: uses.len(),
            constraint,
            has_fixed_use,
        }
    );
    Ok(span)
}

/// One use of a value, with its constraint resolved.
struct ResolvedUse<E>
where
    E: EntityRepr,
{
    /// The use itself.
    use_: Use<E>,

    /// Its program point.
    point: LivePoint<E>,

    /// Which operand of `point`'s instruction it is.
    operand: usize,

    /// Its resolved constraint.
    constraint: OperandConstraint,

    /// And whether the constraint is a single, fixed register.
    is_fixed: bool,

    /// Whether this use reads the value, as opposed to defining it.
    is_read: bool,
}

impl<E> ResolvedUse<E>
where
    E: EntityRepr,
{
    /// Look `use_` up and resolve its constraint.
    fn new(
        input: &Input<'_, impl InputFunction>,
        uses: &PrimaryMap<Use<E>, UseData<E>>,
        use_: Use<E>,
    ) -> Self {
        let use_data = &uses[use_];
        let point = use_data.point;
        let operand = usize::from(use_data.operand);
        let constraint = reuse_aware_constraint(input, point.inst().with_repr32(), operand);
        let is_fixed = constraint.is_fixed(input.machine);
        let is_read = input
            .func
            .inst(point.inst().with_repr32())
            .operand(operand)
            .kind()
            == DefUse::Use;
        ResolvedUse {
            use_,
            point,
            operand,
            constraint,
            is_fixed,
            is_read,
        }
    }

    /// Does a definition at this use's instruction reuse this operand's place
    /// and does this use's value outlive this instruction? If so, this use
    /// needs its own span.
    fn needs_a_span_of_its_own(
        &self,
        input: &Input<'_, impl InputFunction>,
        end: LivePoint<E>,
    ) -> bool {
        let input_inst = input.func.inst(self.point.inst().with_repr32());
        self.is_read
            && is_reuse_target(&input_inst, self.operand)
            && (end > self.point.next_point() || another_tie_follows(&input_inst, self.operand))
    }
}

/// A piece of a span being accumulated, and the run of uses at its end.
///
/// A run is the group of uses at one program point. When a definition ties
/// itself to the last of several reads at one point, the whole run must move
/// into the reuse's span together, since a span's uses are contiguous.
struct Piece<E>
where
    E: EntityRepr,
{
    /// Where the piece starts.
    start: LivePoint<E>,

    /// Where its uses start.
    uses_start: Use<E>,

    /// The merged constraint of everything folded in so far.
    constraint: OperandConstraint,

    /// Whether the merged constraint demands one particular register.
    has_fixed_use: bool,

    /// The piece's last point, thus far.
    point: LivePoint<E>,

    /// The point of the earliest read folded in, if the piece holds any.
    first_read: Option<LivePoint<E>>,

    /// Where its run on uses starts.
    run_start: Use<E>,

    /// The merged constraint of just the run of uses.
    run_constraint: OperandConstraint,

    /// Whether the run's merged constraint demands one particular register.
    run_has_fixed_use: bool,

    /// Whether the piece demanded a fixed register before this run began.
    before_run_has_fixed_use: bool,
}

impl<E> Piece<E>
where
    E: EntityRepr,
{
    /// A piece beginning at `start` with nothing folded into it yet.
    fn empty(start: LivePoint<E>, uses_start: Use<E>) -> Self {
        Piece {
            start,
            uses_start,
            constraint: OperandConstraint::Any,
            has_fixed_use: false,
            point: start,
            first_read: None,
            run_start: uses_start,
            run_constraint: OperandConstraint::Any,
            run_has_fixed_use: false,
            before_run_has_fixed_use: false,
        }
    }

    /// A piece beginning at `start` that holds `u`, and nothing before it.
    fn restarting_at(start: LivePoint<E>, u: &ResolvedUse<E>) -> Self {
        Piece {
            start,
            uses_start: u.use_,
            constraint: u.constraint,
            has_fixed_use: u.is_fixed,
            point: u.point,
            first_read: u.is_read.then_some(u.point),
            run_start: u.use_,
            run_constraint: u.constraint,
            run_has_fixed_use: u.is_fixed,
            before_run_has_fixed_use: false,
        }
    }

    /// Fold the given use into this piece.
    ///
    /// `merged` is the merge of `u`'s constraint with the piece's.
    fn fold(&mut self, u: &ResolvedUse<E>, merged: OperandConstraint, machine: &Machine) {
        if u.point != self.point {
            // A new run begins: remember the fixedness predating it.
            self.before_run_has_fixed_use = self.has_fixed_use;
            self.run_start = u.use_;
            self.run_constraint = u.constraint;
            self.run_has_fixed_use = u.is_fixed;
        } else {
            // The run accumulates only its own uses, not the piece's: whether
            // it can join a tie is only about the uses that would move into the
            // tie's span; the rest of the piece would stay behind.
            self.run_constraint = self
                .run_constraint
                .merge_resolved(&u.constraint, machine)
                .expect("the run admits everything the piece does, which merged with `u`");
            self.run_has_fixed_use |= u.is_fixed;
        }
        self.constraint = merged;
        self.has_fixed_use |= u.is_fixed;
        if self.first_read.is_none() && u.is_read {
            self.first_read = Some(u.point);
        }
        self.point = u.point;
    }

    /// Would folding `u` in pin a read to the stack that need not be there?
    ///
    /// `Any` merged with `Stack` is `Stack`, so one stack operand silently
    /// drags the rest of the piece onto the stack, where it never competes for
    /// a register at all. Cutting costs a move, though, so it is only worth it
    /// where the side keeping its register holds a read at some other point.
    fn a_read_would_land_on_the_stack(&self, u: &ResolvedUse<E>) -> bool {
        match (self.constraint, u.constraint) {
            // The piece would be dragged onto the stack: cut if it holds a read
            // that would rather stay in a register.
            (OperandConstraint::Any, OperandConstraint::Stack) => {
                self.first_read.is_some_and(|read| read < u.point)
            }

            // `u` would be dragged onto the stack by the piece: cut if `u` is
            // itself a read, at a point the piece does not already reach.
            (OperandConstraint::Stack, OperandConstraint::Any) => u.is_read && self.point < u.point,

            // Everything else either merges without moving either side onto or
            // off of the stack, or does not merge at all, in which case
            // `merge_resolved` has already said so.
            _ => false,
        }
    }

    /// Cut the span just before `u`, which cannot join this piece.
    ///
    /// The piece so far becomes its own span, reaching far enough to cover its
    /// own last point, and `u` begins a fresh piece that the caller goes on
    /// accumulating into.
    ///
    /// The new piece starts at the last instruction boundary, not at `u`
    /// itself, because the move between the two pieces cannot happen in the
    /// middle of an instruction.
    fn split_before(
        &self,
        spans: &mut PrimaryMap<LiveSpan<E>, LiveSpanData<E>>,
        output: &mut OutputInner<E>,
        events: &mut EventsLog<E>,
        val: Val<E>,
        block: Block<E>,
        u: &ResolvedUse<E>,
    ) -> IResult<Self> {
        let before = push_span(
            spans,
            output,
            events,
            val,
            (self.start, core::cmp::max(u.point, self.point.next_point())),
            (self.uses_start, u.use_),
            self.constraint,
            self.has_fixed_use,
            block,
        )?;
        event!(
            events,
            EagerSplit {
                val,
                at: u.point,
                before,
                constraint: self.constraint,
                conflicting: u.constraint,
            }
        );
        Ok(Piece::restarting_at(
            u.point.inst_boundary_at_or_before(),
            u,
        ))
    }

    /// Split this piece around the reuse-tie at `u`.
    ///
    /// A `Reuse` is a definition, so it overwrites the location it shares with its
    /// target. A target that outlives the instruction needs a second copy for its
    /// later uses, so it is split like this:
    ///
    /// ```ignore
    ///        def               reuse                     use
    /// span1: [d================)
    /// span2:                   [r==)
    /// span3:                   [==========================u)
    /// ```
    ///
    /// `span2` holds only the tied use, and coalescing bundles it with the span
    /// containing the other tied half. `span3` starts at the same point rather than
    /// after it, since it exists to keep the value alive across the reuse
    /// instruction for subsequent uses. Coalescing will also try bundling `span1`
    /// with `span3`, when possible.
    ///
    /// This method pushes `span1` and `span2`, and returns `span3` so more uses
    /// can be accumulated into it.
    fn split_at_reuse(
        &self,
        spans: &mut PrimaryMap<LiveSpan<E>, LiveSpanData<E>>,
        output: &mut OutputInner<E>,
        events: &mut EventsLog<E>,
        machine: &Machine,
        val: Val<E>,
        block: Block<E>,
        u: &ResolvedUse<E>,
    ) -> IResult<Self> {
        // Earlier uses at this same point belong to the reuse's span rather
        // than the piece, if they can share a location with the tie.
        let run_at_this_point = self.point == u.point && self.run_start != u.use_;
        let run_joins_the_tie = run_at_this_point
            && self
                .run_constraint
                .merge_resolved(&u.constraint, machine)
                .is_some();

        // Where the piece ends, where its uses end, and whose fixedness.
        let (end, uses_end, has_fixed_use) = if run_joins_the_tie {
            // The run belongs to the tie: the piece stops short of it.
            (u.point, self.run_start, self.before_run_has_fixed_use)
        } else if run_at_this_point {
            // The run conflicts with the tie, so it stays in the piece, which
            // must reach past the early half to contain it.
            (u.point.next_point(), u.use_, self.has_fixed_use)
        } else {
            // Nothing here is in the piece, so it ends where the instruction
            // begins.
            (u.point, u.use_, self.has_fixed_use)
        };

        // The piece so far, `span1`. May be empty, and then not pushed at all.
        let before = if self.start < end || self.uses_start != uses_end {
            Some(push_span(
                spans,
                output,
                events,
                val,
                (self.start, end),
                (self.uses_start, uses_end),
                self.constraint,
                has_fixed_use,
                block,
            )?)
        } else {
            None
        };

        // `span2`: the reads at this point and the early half of their
        // instruction, existing only to be overwritten by the reuse def.
        let after = output.entity::<Use<E>>(u.use_.index() + 1)?;
        let copy = push_span(
            spans,
            output,
            events,
            val,
            (u.point, u.point.next_point()),
            (uses_end, after),
            u.constraint,
            u.is_fixed || (run_joins_the_tie && self.run_has_fixed_use),
            block,
        )?;
        event!(
            events,
            ReuseSplit {
                val,
                at: u.point,
                target_use: u.use_,
                before,
                copy,
            }
        );

        // The surviving tail, `span3`.
        Ok(Piece::empty(u.point, after))
    }
}

/// Push the given span, eagerly splitting it whenever:
///
/// * nothing can satisfy all of the uses constraints simultaneously,
///
/// * a value is named as a `Reuse` target and outlives its instruction, or
///
/// * a use that could be in a register would unnecessarily be constrained to
///   the stack.
fn push_span_and_split_conflicts<E>(
    input: &Input<'_, impl InputFunction>,
    uses: &PrimaryMap<Use<E>, UseData<E>>,
    spans: &mut PrimaryMap<LiveSpan<E>, LiveSpanData<E>>,
    counts: &mut Counts,
    events: &mut EventsLog<E>,
    (start, end, val, span_uses): (LivePoint<E>, LivePoint<E>, Val<E>, EntityRange<Use<E>>),
    block: Block<E>,
    block_end: LivePoint<E>,
    output: &mut OutputInner<E>,
) -> IResult<()>
where
    E: EntityRepr,
{
    let mut piece = Piece::empty(start, span_uses.start);
    for use_ in span_uses {
        let u = ResolvedUse::new(input, uses, use_);

        if u.needs_a_span_of_its_own(input, end) {
            debug_assert_eq!(u.point.pos(), Position::Early);
            piece = piece.split_at_reuse(spans, output, events, input.machine, val, block, &u)?;
            counts.reuse_splits.inc();
            continue;
        }

        match piece
            .constraint
            .merge_resolved(&u.constraint, input.machine)
        {
            // The constraints merge, and merging them costs no read its
            // register: we can fold `use_` into this piece.
            Some(merged) if !piece.a_read_would_land_on_the_stack(&u) => {
                piece.fold(&u, merged, input.machine)
            }

            // Either nothing at all satisfies both constraints, or the only
            // thing that does is a stack slot that a read on one side would
            // rather not be pinned to. Split the span, either way.
            _ => {
                piece = piece.split_before(spans, output, events, val, block, &u)?;
                counts.eager_splits.inc();
            }
        }
    }

    // The final piece runs to the end.
    //
    // This piece either has uses or spans to the end of the block (because the
    // associated value is live-out of the block).
    debug_assert!(piece.uses_start != span_uses.end || end == block_end);
    push_span(
        spans,
        output,
        events,
        val,
        (piece.start, end),
        (piece.uses_start, span_uses.end),
        piece.constraint,
        piece.has_fixed_use,
        block,
    )?;
    Ok(())
}

/// Does a later operand tie a definition to another read of `index`'s value?
///
/// Two definitions cannot share a register, so neither can the reads they
/// overwrite, even when the value dies at this instruction.
fn another_tie_follows<'a>(input_inst: &impl InputInst<'a>, index: usize) -> bool {
    let val = input_inst.operand(index).val();
    input_inst
        .operands()
        .enumerate()
        .skip(index + 1)
        .any(|(j, op)| {
            op.kind() == DefUse::Use && op.val() == val && is_reuse_target(input_inst, j)
        })
}

/// Does some definition of this instruction tie itself to its `index`th
/// operand?
fn is_reuse_target<'a>(input_inst: &impl InputInst<'a>, index: usize) -> bool {
    input_inst
        .operands()
        .any(|op| op.constraint() == OperandConstraint::Reuse(index))
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
    use crate::rpo::Rpo;
    use crate::test::{TestFunction, TestInput};
    use core::sync::atomic::{AtomicUsize, Ordering};
    use mutatis::{
        check::{Check, CheckResult},
        mutators as m,
    };
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
            reg_allocation: None,
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
        analyze_spans_and_events(test_input)
            .map(|(liveness, live_ranges, _)| (liveness, live_ranges))
    }

    /// Like `analyze_spans`, but also hands back the events that construction
    /// logged.
    fn analyze_spans_and_events(
        test_input: &TestInput,
    ) -> Result<(Liveness<u32>, LiveRanges<u32>, EventsLog<u32>), String> {
        let mut counts = Counts::new();
        let mut events = EventsLog::<u32>::new();
        let mut dfs = Dfs::<u32>::new();
        let mut rpo = Rpo::<u32>::new();
        let mut region_tree = RegionTree::<u32>::new();
        let mut liveness = Liveness::<u32>::new();
        let mut live_ranges = LiveRanges::<u32>::new();
        let mut output = OutputInner::<u32>::new();

        assert!(live_ranges.is_reset());

        let result = test_input.with_input(|input| {
            let func = input.func;
            rpo.construct(func, &mut dfs, &mut output)
                .and_then(|()| region_tree.construct(func, &mut counts, &mut dfs, &mut output))
                .and_then(|()| liveness.construct(func, &mut counts, &rpo, &mut output))
                .and_then(|()| {
                    live_ranges.construct(
                        input,
                        &mut counts,
                        &mut events,
                        &mut liveness,
                        &mut output,
                    )
                })
        });
        if result.is_err() {
            return Err(format!("construction failed: {:?}", output.take_error()));
        }

        Ok((liveness, live_ranges, events))
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

    /// Every operand in `func` that names a value, as `(block, point, operand
    /// index, kind, value)`.
    ///
    /// An operand naming no value names a register the allocator does not own,
    /// which no span covers, so there is nothing here to compare it against.
    fn all_operands(func: &TestFunction) -> Vec<(Block, LivePoint<u32>, usize, DefUse, Val)> {
        let mut operands = Vec::new();
        for (block, input_block) in func.blocks() {
            for (inst, input_inst) in input_block.insts() {
                for (i, operand) in input_inst.operands().enumerate() {
                    let Some(val) = operand.val() else {
                        continue;
                    };
                    operands.push((
                        block,
                        LivePoint::new(inst, operand.pos()),
                        i,
                        operand.kind(),
                        val,
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

    /// The inputs `live_span_properties` starts its random walk from.
    fn seeds() -> Vec<TestInput> {
        vec![
            TestInput::default(),
            TestInput::with_reuse_of_a_surviving_value(),
            TestInput::with_two_reads_and_a_reuse_of_a_surviving_value(),
            TestInput::with_a_fixed_read_beside_a_reuse_of_a_surviving_value(),
            TestInput::with_a_pinned_read_before_a_reuse_that_reads_twice(),
            TestInput::with_a_reuse_of_a_live_in_value(),
            TestInput::with_two_reuses_at_one_point(),
            TestInput::with_two_reuses_of_a_dying_value(),
            TestInput::with_a_critical_edge(),
            TestInput::with_two_entry_params(),
            TestInput::with_an_entry_param_read_two_ways(),
            TestInput::with_entry_params_in_two_banks(),
            TestInput::with_values_in_two_banks_spilled_and_reloaded(),
            TestInput::with_use_constraints(&[
                OperandConstraint::Any,
                OperandConstraint::Stack,
                OperandConstraint::Any,
                OperandConstraint::Any,
            ]),
        ]
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

    /// A stack operand does not drag the reads around it onto the stack. The
    /// span is cut on both sides of it, so the reads before it keep their
    /// register and the reads after it get one back.
    #[test]
    fn split_a_span_whose_any_uses_straddle_a_stack_use() {
        let (any, stack) = (OperandConstraint::Any, OperandConstraint::Stack);

        let test_input = TestInput::with_use_constraints(&[any, stack, any, any]);
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();

        let spans: Vec<LiveSpan> = live_ranges.spans().collect();
        assert_eq!(spans.len(), 3, "{spans:#?}");

        let def = LivePoint::new(inst(0), Position::Late);
        let first_use = LivePoint::new(inst(1), Position::Early);
        let stack_use = LivePoint::new(inst(2), Position::Early);
        let third_use = LivePoint::new(inst(3), Position::Early);
        let last_use = LivePoint::new(inst(4), Position::Early);

        // The three pieces abut exactly, and the middle one covers the stack
        // operand's instruction and nothing more.
        assert_eq!(spans[0].start(&live_ranges), def);
        assert_eq!(spans[0].end(&live_ranges), stack_use);
        assert_eq!(spans[1].start(&live_ranges), stack_use);
        assert_eq!(spans[1].end(&live_ranges), third_use);
        assert_eq!(spans[2].start(&live_ranges), third_use);
        assert!(spans[2].end(&live_ranges) > last_use);

        // Each use is recorded by the piece that covers it.
        let points = |span: LiveSpan| -> Vec<LivePoint<u32>> {
            span.uses(&live_ranges)
                .into_iter()
                .map(|u| u.point(&live_ranges))
                .collect()
        };
        assert_eq!(points(spans[0]), vec![def, first_use]);
        assert_eq!(points(spans[1]), vec![stack_use]);
        assert_eq!(points(spans[2]), vec![third_use, last_use]);

        // And only the middle piece is pinned to the stack.
        let constraints: Vec<OperandConstraint> = test_input.with_input(|input| {
            spans
                .iter()
                .map(|s| s.constraint(&live_ranges, input))
                .collect()
        });
        assert_eq!(constraints, vec![any, stack, any]);
    }

    /// A definition is not split off from the stack read that follows it: the
    /// value has to reach the slot either way, so cutting here would only turn
    /// "define into the slot" into "define into a register, then store it".
    #[test]
    fn a_stack_use_does_not_split_a_definition_off_by_itself() {
        let test_input = TestInput::with_use_constraints(&[OperandConstraint::Stack]);
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();

        let spans: Vec<LiveSpan> = live_ranges.spans().collect();
        assert_eq!(spans.len(), 1, "{spans:#?}");
        assert_eq!(
            spans[0].start(&live_ranges),
            LivePoint::new(inst(0), Position::Late),
            "the definition writes straight into the slot"
        );

        let constraint = test_input.with_input(|input| spans[0].constraint(&live_ranges, input));
        assert_eq!(constraint, OperandConstraint::Stack);
    }

    /// Every span construction is logged, and so is the eager split that made
    /// two of them.
    #[test]
    #[cfg(feature = "visualizer")]
    fn span_construction_and_eager_splits_are_logged() {
        use crate::events::Event;

        let rc = |i| OperandConstraint::Reg(RegClass::try_new(i).unwrap());
        let test_input = TestInput::with_use_constraints(&[rc(0), rc(1)]);
        let (_liveness, live_ranges, events) = analyze_spans_and_events(&test_input).unwrap();

        let spans: Vec<LiveSpan> = live_ranges.spans().collect();
        assert_eq!(spans.len(), 2, "{spans:#?}");

        let constructed: Vec<_> = events
            .iter()
            .filter_map(|(_, e)| match e {
                Event::SpanConstructed {
                    span,
                    val,
                    start,
                    end,
                    ..
                } => Some((*span, *val, *start, *end)),
                _ => None,
            })
            .collect();
        assert_eq!(constructed.len(), 2, "{constructed:#?}");
        for (span, val, start, end) in constructed {
            assert_eq!(val, span.val(&live_ranges));
            assert_eq!(start, span.start(&live_ranges));
            assert_eq!(end, span.end(&live_ranges));
        }

        let splits: Vec<_> = events
            .iter()
            .filter_map(|(_, e)| match e {
                Event::EagerSplit {
                    val,
                    at,
                    before,
                    constraint,
                    conflicting,
                } => Some((*val, *at, *before, *constraint, *conflicting)),
                _ => None,
            })
            .collect();
        assert_eq!(splits.len(), 1, "{splits:#?}");
        let (val, at, before, constraint, conflicting) = splits[0];
        assert_eq!(before, spans[0]);
        assert_eq!(val, spans[0].val(&live_ranges));
        assert_eq!(at, LivePoint::new(inst(2), Position::Early));
        assert_eq!(constraint, rc(0));
        assert_eq!(conflicting, rc(1));
    }

    /// Both directions of a stack cut are logged, each naming the constraint
    /// the piece would have been forced to take on.
    #[test]
    #[cfg(feature = "visualizer")]
    fn splits_off_of_and_back_onto_the_stack_are_logged() {
        use crate::events::Event;

        let (any, stack) = (OperandConstraint::Any, OperandConstraint::Stack);
        let test_input = TestInput::with_use_constraints(&[any, stack, any, any]);
        let (_liveness, live_ranges, events) = analyze_spans_and_events(&test_input).unwrap();

        let val = live_ranges.spans().next().unwrap().val(&live_ranges);
        let splits: Vec<_> = events
            .iter()
            .filter_map(|(_, e)| match e {
                Event::EagerSplit {
                    val,
                    at,
                    constraint,
                    conflicting,
                    ..
                } => Some((*val, *at, *constraint, *conflicting)),
                _ => None,
            })
            .collect();
        assert_eq!(
            splits,
            vec![
                (val, LivePoint::new(inst(2), Position::Early), any, stack),
                (val, LivePoint::new(inst(3), Position::Early), stack, any),
            ],
            "{splits:#?}"
        );
    }

    /// A reuse split names the use it was made for and the one-point span the
    /// definition overwrites.
    #[test]
    #[cfg(feature = "visualizer")]
    fn reuse_splits_are_logged() {
        use crate::events::Event;

        let test_input = TestInput::with_reuse_of_a_surviving_value();
        let (_liveness, live_ranges, events) = analyze_spans_and_events(&test_input).unwrap();

        let splits: Vec<_> = events
            .iter()
            .filter_map(|(_, e)| match e {
                Event::ReuseSplit {
                    val,
                    at,
                    target_use,
                    before,
                    copy,
                } => Some((*val, *at, *target_use, *before, *copy)),
                _ => None,
            })
            .collect();
        assert_eq!(splits.len(), 1, "{splits:#?}");
        let (val, at, target_use, before, copy) = splits[0];

        assert_eq!(val, copy.val(&live_ranges));
        assert_eq!(at, target_use.point(&live_ranges));
        assert_eq!(copy.start(&live_ranges), at);
        assert_eq!(copy.end(&live_ranges), at.next_point());
        let before = before.expect("the value is live before the tie");
        assert_eq!(before.end(&live_ranges), at);

        // The pieces were logged as they were pushed, before the split that
        // explains them.
        let kinds: Vec<_> = events
            .iter()
            .map(|(_, e)| match e {
                Event::SpanConstructed { .. } => "span",
                Event::ReuseSplit { .. } => "reuse",
                _ => "other",
            })
            .collect();
        let reuse = kinds.iter().position(|k| *k == "reuse").unwrap();
        assert_eq!(kinds[reuse - 1], "span");
    }

    /// A `Reuse` whose target outlives the instruction gets the three-piece
    /// shape `split_at_reuse` draws. The properties above say only that the
    /// pieces tile the value's range; this says where the cuts land and who
    /// owns the tied use.
    #[test]
    fn split_a_span_around_a_reuse_of_a_surviving_value() {
        let test_input = TestInput::with_reuse_of_a_surviving_value();
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();

        // The reuse names operand 0 of `inst1`, the value that outlives it.
        let survivor =
            test_input.with_input(|input| input.func.inst(inst(1)).operand(0).val().unwrap());
        let spans: Vec<LiveSpan> = live_ranges
            .spans()
            .filter(|span| span.val(&live_ranges) == survivor)
            .collect();
        assert_eq!(spans.len(), 3, "{spans:#?}");

        let def = LivePoint::new(inst(0), Position::Late);
        let tie = LivePoint::new(inst(1), Position::Early);
        let overwritten = LivePoint::new(inst(1), Position::Late);
        let later_use = LivePoint::new(inst(2), Position::Early);

        // The run up to the tie ...
        assert_eq!(spans[0].start(&live_ranges), def);
        assert_eq!(
            spans[0].end(&live_ranges),
            tie,
            "the first piece stops at the instruction that overwrites its place",
        );

        // ... the copy the definition overwrites, the instruction's early half ...
        assert_eq!(spans[1].start(&live_ranges), tie);
        assert_eq!(
            spans[1].end(&live_ranges),
            overwritten,
            "the doomed piece covers just the tied instruction",
        );

        // ... and the survivor, starting alongside it so both share a source.
        assert_eq!(spans[2].start(&live_ranges), tie);
        assert_eq!(spans[2].end(&live_ranges), later_use.next_point());

        // The tied use belongs to the overwritten piece, which is therefore
        // what `Inst::operand_span` resolves to for coalescing.
        let points = |span: LiveSpan| -> Vec<LivePoint<u32>> {
            span.uses(&live_ranges)
                .into_iter()
                .map(|u| u.point(&live_ranges))
                .collect()
        };
        assert_eq!(points(spans[0]), vec![def]);
        assert_eq!(points(spans[1]), vec![tie]);
        assert_eq!(points(spans[2]), vec![later_use]);

        // The control: with no later read the value dies at the tie.
        let test_input = TestInput::with_reuse_def(OperandConstraint::Any);
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();
        let survivor =
            test_input.with_input(|input| input.func.inst(inst(1)).operand(0).val().unwrap());
        assert_eq!(
            live_ranges
                .spans()
                .filter(|span| span.val(&live_ranges) == survivor)
                .count(),
            1,
        );
    }

    /// Reading one value twice under a tie still cuts it into three pieces.
    ///
    /// Both reads are at one point, so the piece before the tie ends there and
    /// hands *both* to the overwritten piece; ending it later would leave three
    /// pieces live across that point.
    #[test]
    fn split_a_span_around_a_reuse_that_reads_its_value_twice() {
        let test_input = TestInput::with_two_reads_and_a_reuse_of_a_surviving_value();
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();

        // The reuse names operand 1 of `inst1`; operand 0 reads it too.
        let survivor =
            test_input.with_input(|input| input.func.inst(inst(1)).operand(1).val().unwrap());
        assert_eq!(
            survivor,
            test_input.with_input(|input| input.func.inst(inst(1)).operand(0).val().unwrap()),
            "the fixture reads one value twice",
        );

        let spans: Vec<LiveSpan> = live_ranges
            .spans()
            .filter(|span| span.val(&live_ranges) == survivor)
            .collect();
        assert_eq!(spans.len(), 3, "{spans:#?}");

        let def = LivePoint::new(inst(0), Position::Late);
        let tie = LivePoint::new(inst(1), Position::Early);
        let overwritten = LivePoint::new(inst(1), Position::Late);
        let later_use = LivePoint::new(inst(2), Position::Early);

        assert_eq!(spans[0].start(&live_ranges), def);
        assert_eq!(
            spans[0].end(&live_ranges),
            tie,
            "the first piece stops at the tie even though it just read the value there",
        );

        assert_eq!(spans[1].start(&live_ranges), tie);
        assert_eq!(spans[1].end(&live_ranges), overwritten);

        assert_eq!(spans[2].start(&live_ranges), tie);
        assert_eq!(spans[2].end(&live_ranges), later_use.next_point());

        // Both reads belong to the overwritten piece: they read one place, and
        // a span's uses are contiguous.
        let points = |span: LiveSpan| -> Vec<LivePoint<u32>> {
            span.uses(&live_ranges)
                .into_iter()
                .map(|u| u.point(&live_ranges))
                .collect()
        };
        assert_eq!(points(spans[0]), vec![def]);
        assert_eq!(points(spans[1]), vec![tie, tie]);
        assert_eq!(points(spans[2]), vec![later_use]);
    }

    /// The same three pieces, but with the plain read pinned to `r0` while the
    /// tie's own operand demands nothing.
    #[test]
    fn a_fixed_read_beside_a_reuse_fixes_the_overwritten_piece() {
        let test_input = TestInput::with_a_fixed_read_beside_a_reuse_of_a_surviving_value();
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();

        let survivor =
            test_input.with_input(|input| input.func.inst(inst(1)).operand(1).val().unwrap());
        let spans: Vec<LiveSpan> = live_ranges
            .spans()
            .filter(|span| span.val(&live_ranges) == survivor)
            .collect();
        assert_eq!(spans.len(), 3, "{spans:#?}");

        let def = LivePoint::new(inst(0), Position::Late);
        let tie = LivePoint::new(inst(1), Position::Early);
        let overwritten = LivePoint::new(inst(1), Position::Late);
        let later_use = LivePoint::new(inst(2), Position::Early);

        assert_eq!(spans[0].start(&live_ranges), def);
        assert_eq!(spans[0].end(&live_ranges), tie);
        assert_eq!(spans[1].start(&live_ranges), tie);
        assert_eq!(spans[1].end(&live_ranges), overwritten);
        assert_eq!(spans[2].start(&live_ranges), tie);
        assert_eq!(spans[2].end(&live_ranges), later_use.next_point());

        // Both halves of the tie resolve to the pinned read's class: the
        // target (operand 1) because the sibling narrows it, and the
        // definition (operand 2) because it is narrowed by the very same
        // sibling. Agreeing is what keeps them in one bundle.
        test_input.with_input(|input| {
            let pinned = reuse_aware_constraint(input, inst(1), 0);
            let target = reuse_aware_constraint(input, inst(1), 1);
            let def = reuse_aware_constraint(input, inst(1), 2);
            assert_eq!(
                target, pinned,
                "the tie's target is narrowed to the pinned read beside it",
            );
            assert_eq!(def, target, "both halves of the tie must agree");
            assert!(
                target.is_fixed(input.machine),
                "and that class is a single register: {target:?}",
            );
        });
        assert!(
            spans[1].has_fixed_use(&live_ranges),
            "the overwritten piece holds a read pinned to one register: {:#?}",
            spans[1],
        );
    }

    /// A read pinned elsewhere, at an *earlier* point, does not keep the run at
    /// the tie's point out of the overwritten piece.
    ///
    /// The run is what moves into that piece, so only the run's own constraint
    /// decides whether it can join the tie. Folding the rest of the piece in
    /// too --- the pinned read here --- makes the merge fail, and the value
    /// then needs two registers across the tie's instruction instead of one.
    #[test]
    fn a_pinned_read_does_not_veto_a_later_run_joining_a_tie() {
        let test_input = TestInput::with_a_pinned_read_before_a_reuse_that_reads_twice();
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();

        // The reuse names operand 2 of `inst2`; operands 0 and 1 read it too,
        // at the same point, and `inst1` reads it at an earlier one.
        let survivor =
            test_input.with_input(|input| input.func.inst(inst(2)).operand(2).val().unwrap());
        test_input.with_input(|input| {
            let inst2 = input.func.inst(inst(2));
            for i in [0, 1] {
                assert_eq!(
                    inst2.operand(i).val(),
                    Some(survivor),
                    "operand {i} reads it too"
                );
            }
            assert_eq!(input.func.inst(inst(1)).operand(0).val(), Some(survivor));

            // The pinned read and the tie want disjoint classes, so the piece
            // before the tie cannot satisfy both --- which is the whole point.
            let pinned = reuse_aware_constraint(input, inst(1), 0);
            let tie = reuse_aware_constraint(input, inst(2), 2);
            assert!(
                pinned.merge_resolved(&tie, input.machine).is_none(),
                "{pinned:?} and {tie:?} should conflict",
            );
        });

        let spans: Vec<LiveSpan> = live_ranges
            .spans()
            .filter(|span| span.val(&live_ranges) == survivor)
            .collect();
        assert_eq!(spans.len(), 3, "{spans:#?}");

        let def = LivePoint::new(inst(0), Position::Late);
        let pinned_read = LivePoint::new(inst(1), Position::Early);
        let tie = LivePoint::new(inst(2), Position::Early);
        let overwritten = LivePoint::new(inst(2), Position::Late);
        let later_use = LivePoint::new(inst(3), Position::Early);

        assert_eq!(spans[0].start(&live_ranges), def);
        assert_eq!(
            spans[0].end(&live_ranges),
            tie,
            "the piece holding the pinned read stops at the tie, rather than \
             reaching past the early half to keep the run it has no claim on",
        );

        assert_eq!(spans[1].start(&live_ranges), tie);
        assert_eq!(spans[1].end(&live_ranges), overwritten);

        assert_eq!(spans[2].start(&live_ranges), tie);
        assert_eq!(spans[2].end(&live_ranges), later_use.next_point());

        // All three reads at the tie's point belong to the overwritten piece.
        let points = |span: LiveSpan| -> Vec<LivePoint<u32>> {
            span.uses(&live_ranges)
                .into_iter()
                .map(|u| u.point(&live_ranges))
                .collect()
        };
        assert_eq!(points(spans[0]), vec![def, pinned_read]);
        assert_eq!(points(spans[1]), vec![tie, tie, tie]);
        assert_eq!(points(spans[2]), vec![later_use]);
    }

    /// A tie's target joins the sibling that pins its run, rather than folding
    /// into an earlier piece pinned somewhere else.
    #[test]
    fn a_reuse_target_joins_the_sibling_that_pins_its_run() {
        let test_input = TestInput::with_a_pinned_read_before_a_reuse_of_an_unpinned_read();
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();

        // The reuse at `inst2` names operand 0; operand 1 reads the same value
        // at the same point, and `inst1` read it at an earlier one.
        let survivor =
            test_input.with_input(|input| input.func.inst(inst(2)).operand(0).val().unwrap());
        let spans: Vec<LiveSpan> = live_ranges
            .spans()
            .filter(|span| span.val(&live_ranges) == survivor)
            .collect();
        assert_eq!(spans.len(), 2, "{spans:#?}");

        let def = LivePoint::new(inst(0), Position::Late);
        let pinned_read = LivePoint::new(inst(1), Position::Early);
        let tie = LivePoint::new(inst(2), Position::Early);
        let overwritten = LivePoint::new(inst(2), Position::Late);

        // The earlier pinned read's piece stops at the tie ...
        assert_eq!(spans[0].start(&live_ranges), def);
        assert_eq!(spans[0].end(&live_ranges), tie);
        // ... and the doomed copy the definition overwrites holds *both* reads
        // at the tie's point: the target and the sibling that pins it.
        assert_eq!(spans[1].start(&live_ranges), tie);
        assert_eq!(spans[1].end(&live_ranges), overwritten);

        let uses = |span: LiveSpan| -> Vec<(usize, LivePoint<u32>)> {
            span.uses(&live_ranges)
                .into_iter()
                .map(|u| (u.operand(&live_ranges), u.point(&live_ranges)))
                .collect()
        };
        assert_eq!(uses(spans[0]), vec![(0, def), (0, pinned_read)]);
        assert_eq!(
            uses(spans[1]),
            vec![(0, tie), (1, tie)],
            "the tie's target did not stay behind in the pinned read's piece",
        );

        // And so the definition's span can share a bundle with its target's:
        // the two constraints merge, which is what coalescing needs.
        let tied =
            test_input.with_input(|input| input.func.inst(inst(2)).operand(2).val().unwrap());
        let def_span = live_ranges
            .spans()
            .find(|span| span.val(&live_ranges) == tied)
            .unwrap();
        test_input.with_input(|input| {
            let target = spans[1].constraint(&live_ranges, input);
            let definition = def_span.constraint(&live_ranges, input);
            assert!(
                target.merge_resolved(&definition, input.machine).is_some(),
                "the tie's halves must be coalescable: {target:?} and {definition:?}",
            );
        });
    }

    /// A tie at a block's first instruction, on a live-in value, splits it in
    /// two, not three: the piece up to the tie is empty --- arrival and tie
    /// share the start point --- so it is never pushed, and pushed anyway it
    /// would hold a register across the early half with no uses at all.
    #[test]
    fn split_a_span_around_a_reuse_of_a_live_in_value() {
        let test_input = TestInput::with_a_reuse_of_a_live_in_value();
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();

        // The reuse names operand 0 of `inst2`, the block's first instruction.
        let survivor =
            test_input.with_input(|input| input.func.inst(inst(2)).operand(0).val().unwrap());
        let spans: Vec<LiveSpan> = live_ranges
            .spans()
            .filter(|span| span.val(&live_ranges) == survivor)
            .collect();
        assert_eq!(spans.len(), 3, "{spans:#?}");

        let def = LivePoint::new(inst(0), Position::Late);
        let tie = LivePoint::new(inst(2), Position::Early);
        let overwritten = LivePoint::new(inst(2), Position::Late);
        let later_use = LivePoint::new(inst(3), Position::Early);

        // The whole of `block0`, which the value flows out of ...
        assert_eq!(spans[0].start(&live_ranges), def);
        assert_eq!(
            spans[0].end(&live_ranges),
            tie,
            "the defining block's piece ends where the tied block begins",
        );

        // ... then `block1`'s two pieces: the doomed copy and the survivor.
        assert_eq!(spans[1].start(&live_ranges), tie);
        assert_eq!(spans[1].end(&live_ranges), overwritten);
        assert_eq!(spans[2].start(&live_ranges), tie);
        assert_eq!(spans[2].end(&live_ranges), later_use.next_point());

        let points = |span: LiveSpan| -> Vec<LivePoint<u32>> {
            span.uses(&live_ranges)
                .into_iter()
                .map(|u| u.point(&live_ranges))
                .collect()
        };
        assert_eq!(points(spans[0]), vec![def]);
        assert_eq!(points(spans[1]), vec![tie]);
        assert_eq!(points(spans[2]), vec![later_use]);
    }

    /// Two ties at one point cut their value into one doomed piece each plus
    /// one survivor: the first tie takes everything up to the instruction, so
    /// the piece before the *second* is empty and never pushed.
    #[test]
    fn split_a_span_around_two_reuses_at_one_point() {
        let test_input = TestInput::with_two_reuses_at_one_point();
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();

        // Both ties name reads of the same value, at the same point.
        let survivor =
            test_input.with_input(|input| input.func.inst(inst(1)).operand(0).val().unwrap());
        assert_eq!(
            survivor,
            test_input.with_input(|input| input.func.inst(inst(1)).operand(1).val().unwrap()),
        );

        let spans: Vec<LiveSpan> = live_ranges
            .spans()
            .filter(|span| span.val(&live_ranges) == survivor)
            .collect();
        assert_eq!(spans.len(), 4, "{spans:#?}");

        let def = LivePoint::new(inst(0), Position::Late);
        let tie = LivePoint::new(inst(1), Position::Early);
        let overwritten = LivePoint::new(inst(1), Position::Late);
        let later_use = LivePoint::new(inst(2), Position::Early);

        // The run up to the first tie, a doomed piece per tie, and the survivor.
        assert_eq!(spans[0].start(&live_ranges), def);
        assert_eq!(spans[0].end(&live_ranges), tie);
        for span in &spans[1..3] {
            assert_eq!(span.start(&live_ranges), tie);
            assert_eq!(span.end(&live_ranges), overwritten);
        }
        assert_eq!(spans[3].start(&live_ranges), tie);
        assert_eq!(spans[3].end(&live_ranges), later_use.next_point());

        let points = |span: LiveSpan| -> Vec<LivePoint<u32>> {
            span.uses(&live_ranges)
                .into_iter()
                .map(|u| u.point(&live_ranges))
                .collect()
        };
        assert_eq!(points(spans[0]), vec![def]);
        assert_eq!(points(spans[1]), vec![tie]);
        assert_eq!(points(spans[2]), vec![tie]);
        assert_eq!(points(spans[3]), vec![later_use]);
    }

    /// Two ties at one point on a dying value still cut it into one piece per
    /// tie: one location would carry both reads, but the definitions that
    /// overwrite them cannot share a register, so neither can the reads. The
    /// last tie keeps the tail, there being nothing after it to carry.
    #[test]
    fn split_a_span_around_two_reuses_of_a_dying_value() {
        let test_input = TestInput::with_two_reuses_of_a_dying_value();
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();

        let survivor =
            test_input.with_input(|input| input.func.inst(inst(1)).operand(0).val().unwrap());
        let spans: Vec<LiveSpan> = live_ranges
            .spans()
            .filter(|span| span.val(&live_ranges) == survivor)
            .collect();
        assert_eq!(spans.len(), 3, "{spans:#?}");

        let def = LivePoint::new(inst(0), Position::Late);
        let tie = LivePoint::new(inst(1), Position::Early);
        let overwritten = LivePoint::new(inst(1), Position::Late);

        assert_eq!(spans[0].start(&live_ranges), def);
        assert_eq!(spans[0].end(&live_ranges), tie);
        for span in &spans[1..] {
            assert_eq!(span.start(&live_ranges), tie);
            assert_eq!(span.end(&live_ranges), overwritten);
        }

        let points = |span: LiveSpan| -> Vec<LivePoint<u32>> {
            span.uses(&live_ranges)
                .into_iter()
                .map(|u| u.point(&live_ranges))
                .collect()
        };
        assert_eq!(points(spans[0]), vec![def]);
        assert_eq!(points(spans[1]), vec![tie]);
        assert_eq!(points(spans[2]), vec![tie]);
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
            let mut events = EventsLog::<u32>::new();
            let mut output = OutputInner::<u32>::new();
            let (cut, rest) = (evens(&spans), odds(&spans));

            let (prefix, tail) = test_input.with_input(|input| {
                let prefix = live_ranges
                    .push_bundle(
                        input,
                        &mut output,
                        region,
                        OperandConstraint::Any,
                        cut.iter().copied(),
                    )
                    .unwrap();
                let tail = live_ranges
                    .push_bundle(
                        input,
                        &mut output,
                        region,
                        OperandConstraint::Any,
                        rest.iter().copied(),
                    )
                    .unwrap();
                (prefix, tail)
            });
            let parent_run = prefix.spans_storage(&live_ranges);

            let suffix = test_input
                .with_input(|input| {
                    prefix.split_at_span(
                        &mut live_ranges,
                        input,
                        &mut events,
                        &mut output,
                        prefix_end,
                    )
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
            let (want_prefix, want_suffix) = test_input.with_input(|input| {
                let want_prefix = reference
                    .push_bundle(
                        input,
                        &mut ref_output,
                        region,
                        OperandConstraint::Any,
                        ref_cut[..prefix_end].iter().copied(),
                    )
                    .unwrap();
                let want_suffix = reference
                    .push_bundle(
                        input,
                        &mut ref_output,
                        region,
                        OperandConstraint::Any,
                        ref_cut[prefix_end..].iter().copied(),
                    )
                    .unwrap();
                (want_prefix, want_suffix)
            });
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

    /// Cutting a bundle inside one of its spans.
    ///
    /// Runs over every legal cut of every span, in two arena layouts: one where
    /// the bundle owns the whole arena, so a hole is left behind, and one where
    /// another bundle's run follows it, so relocation has to leave that run
    /// alone.
    #[test]
    fn split_bundle_within_span() {
        let rc = |i| OperandConstraint::Reg(RegClass::try_new(i).unwrap());
        let any = OperandConstraint::Any;

        // Two conflicting classes, each held for three instructions at a time,
        // so that span construction cuts the value into spans that cover
        // several instructions and hold several uses. That gives every span an
        // interior instruction boundary to cut at, with uses on both sides.
        let constraints: Vec<_> = (0..5).flat_map(|k| [rc(k % 2), any, any]).collect();
        let test_input = TestInput::with_use_constraints(&constraints);
        let region = Region::try_new(0).unwrap();

        // Neighbouring spans conflict, so as in `split_bundle_keeps_storage_tiled`
        // the bundle being cut takes every *other* span and the rest go into a
        // bundle of their own, sitting after it in the shared storage.
        let evens = |spans: &[LiveSpan]| spans.iter().copied().step_by(2).collect::<Vec<_>>();
        let odds =
            |spans: &[LiveSpan]| spans.iter().copied().skip(1).step_by(2).collect::<Vec<_>>();

        let build = || -> (LiveRanges<u32>, Vec<LiveSpan>) {
            let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();
            let spans = evens(&live_ranges.spans().collect::<Vec<_>>());
            (live_ranges, spans)
        };

        let (probe, all_spans) = build();
        assert_eq!(
            all_spans.len(),
            3,
            "want three compatible multi-instruction spans to cut inside of, got {all_spans:?}",
        );

        // Every instruction boundary strictly inside a span is a legal cut.
        let cut_points = |live_ranges: &LiveRanges<u32>, span: LiveSpan| {
            let mut points = Vec::new();
            let mut at = span.start(live_ranges).next_point();
            while at < span.end(live_ranges) {
                if at.pos() == Position::Early {
                    points.push(at);
                }
                at = at.next_point();
            }
            points
        };
        for &span in &all_spans {
            assert!(
                !cut_points(&probe, span).is_empty(),
                "{span:?} has no interior boundary to cut at",
            );
        }
        drop(probe);

        // Either the bundle owns every span, so relocating a half leaves a hole
        // in the middle of the arena, or it owns all but the last, so another
        // bundle's run sits after the hole.
        for num_owned in [all_spans.len() - 1, all_spans.len()] {
            for i in 0..num_owned {
                let (probe, spans) = build();
                for at in cut_points(&probe, spans[i]) {
                    let (mut live_ranges, spans) = build();
                    let mut events = EventsLog::<u32>::new();
                    let mut output = OutputInner::<u32>::new();
                    let leftovers = odds(&live_ranges.spans().collect::<Vec<_>>());

                    let (bundle, followers) = test_input.with_input(|input| {
                        let bundle = live_ranges
                            .push_bundle(
                                input,
                                &mut output,
                                region,
                                OperandConstraint::Any,
                                spans[..num_owned].iter().copied(),
                            )
                            .unwrap();

                        // Whatever the bundle did not take goes into bundles of
                        // its own, so that every slot of the storage starts out
                        // owned and there is a run after the one being cut.
                        let mut followers = Vec::new();
                        for rest in [&spans[num_owned..], &leftovers[..]] {
                            if rest.is_empty() {
                                continue;
                            }
                            let follower = live_ranges
                                .push_bundle(
                                    input,
                                    &mut output,
                                    region,
                                    OperandConstraint::Any,
                                    rest.iter().copied(),
                                )
                                .unwrap();
                            followers.push((follower, follower.spans_storage(&live_ranges)));
                        }
                        (bundle, followers)
                    });

                    let parent_run = bundle.spans_storage(&live_ranges);
                    let divided = spans[i];
                    let (start, end) = (divided.start(&live_ranges), divided.end(&live_ranges));
                    let uses = divided.uses(&live_ranges).into_iter().collect::<Vec<_>>();
                    let had_fixed_use = divided.has_fixed_use(&live_ranges);
                    let len_insts = |live_ranges: &LiveRanges<u32>, b: LiveBundle| {
                        b.spans(live_ranges)
                            .map(|s| s.len_insts(live_ranges))
                            .sum::<usize>()
                    };
                    let parent_len_insts = len_insts(&live_ranges, bundle);
                    let unchanged = spans
                        .iter()
                        .filter(|&&s| s != divided)
                        .map(|&s| (s, s.start(&live_ranges), s.end(&live_ranges)))
                        .collect::<Vec<_>>();

                    let context = format!("cutting {divided:?} at {at:?}, of {num_owned} spans");

                    let suffix = test_input
                        .with_input(|input| {
                            bundle.split_at_point(
                                &mut live_ranges,
                                input,
                                &mut events,
                                &mut output,
                                i,
                                at,
                            )
                        })
                        .unwrap();

                    // The divided span was rewritten in place as the first
                    // piece and the second piece is the newest span; together
                    // they cover exactly what it covered.
                    let new_span = live_ranges.spans().last().unwrap();
                    assert_ne!(new_span, divided, "{context}");
                    assert_eq!(divided.start(&live_ranges), start, "{context}");
                    assert_eq!(divided.end(&live_ranges), at, "{context}");
                    assert_eq!(new_span.start(&live_ranges), at, "{context}");
                    assert_eq!(new_span.end(&live_ranges), end, "{context}");
                    assert_eq!(
                        divided.len_insts(&live_ranges) + new_span.len_insts(&live_ranges),
                        end.prev_point().inst().index() - start.inst().index() + 1,
                        "{context}: the pieces create or lose an instruction",
                    );

                    // No other span moved.
                    for (span, start, end) in unchanged {
                        assert_eq!(span.start(&live_ranges), start, "{context}");
                        assert_eq!(span.end(&live_ranges), end, "{context}");
                    }

                    // The uses were divided at the cut, and each one names the
                    // piece that now holds it.
                    let lo = divided.uses(&live_ranges).into_iter().collect::<Vec<_>>();
                    let hi = new_span.uses(&live_ranges).into_iter().collect::<Vec<_>>();
                    assert_eq!([lo.clone(), hi.clone()].concat(), uses, "{context}");
                    for (piece, pieces_uses) in [(divided, &lo), (new_span, &hi)] {
                        for &u in pieces_uses {
                            assert_eq!(live_ranges.use_span[u], piece, "{context}");
                            let point = u.point(&live_ranges);
                            assert!(
                                piece.start(&live_ranges) <= point
                                    && point < piece.end(&live_ranges),
                                "{context}: {u:?} is not inside {piece:?}",
                            );
                        }
                    }

                    // A fixed use is still fixed and did not become one: it went
                    // to whichever piece kept it.
                    assert_eq!(
                        divided.has_fixed_use(&live_ranges) || new_span.has_fixed_use(&live_ranges),
                        had_fixed_use,
                        "{context}",
                    );

                    // Each half holds the spans it should, in order, and each
                    // span names the half that holds it.
                    let want_prefix = [&spans[..i], &[divided]].concat();
                    let want_suffix = [&[new_span], &spans[i + 1..num_owned]].concat();
                    assert_eq!(
                        bundle.spans(&live_ranges).collect::<Vec<_>>(),
                        want_prefix,
                        "{context}",
                    );
                    assert_eq!(
                        suffix.spans(&live_ranges).collect::<Vec<_>>(),
                        want_suffix,
                        "{context}",
                    );
                    for (half, held) in [(bundle, &want_prefix), (suffix, &want_suffix)] {
                        for &span in held {
                            assert_eq!(span.bundle(&live_ranges), Some(half), "{context}");
                        }
                    }
                    for (follower, _) in &followers {
                        for span in follower.spans(&live_ranges) {
                            assert_eq!(span.bundle(&live_ranges), Some(*follower), "{context}");
                        }
                    }

                    // Both halves came out strictly shorter than the bundle
                    // they were cut from, which is what makes splitting
                    // terminate, and between them they cover just as much.
                    let halves = [
                        len_insts(&live_ranges, bundle),
                        len_insts(&live_ranges, suffix),
                    ];
                    assert_eq!(halves[0] + halves[1], parent_len_insts, "{context}");
                    for half in halves {
                        assert!(half < parent_len_insts, "{context}: {half} instructions");
                    }

                    // The runs are disjoint, the parent's slots that neither
                    // half took are exactly the hole relocation leaves behind,
                    // and nothing trod on the bundle that follows.
                    check_bundle_runs_are_disjoint(&live_ranges);
                    let prefix_run = bundle.spans_storage(&live_ranges);
                    let suffix_run = suffix.spans_storage(&live_ranges);
                    assert_eq!(prefix_run.indices().len(), i + 1, "{context}");
                    assert_eq!(suffix_run.indices().len(), num_owned - i, "{context}");
                    let hole = parent_run
                        .indices()
                        .filter(|slot| {
                            !prefix_run.indices().contains(slot)
                                && !suffix_run.indices().contains(slot)
                        })
                        .count();
                    assert_eq!(hole, i.min(num_owned - i - 1), "{context}");
                    for (follower, run) in &followers {
                        assert_eq!(
                            follower.spans_storage(&live_ranges),
                            *run,
                            "{context}: relocating a half moved {follower:?}",
                        );
                    }

                    // Finally, both halves' cached summaries are what
                    // `push_bundle` would have computed for the same span list.
                    // Rebuilding in place is destructive, so this goes last.
                    for (half, run) in [(bundle, prefix_run), (suffix, suffix_run)] {
                        let (constraint, has_fixed_uses, spill_weight, is_minimal) = (
                            half.constraint(&live_ranges),
                            half.has_fixed_uses(&live_ranges),
                            half.spill_weight(&live_ranges),
                            half.is_minimal(&live_ranges),
                        );
                        for slot in run {
                            let span = live_ranges.bundle_spans_storage[slot];
                            live_ranges.span_bundle[span] = None;
                        }
                        let want = test_input.with_input(|input| {
                            let want = LiveBundle::new(
                                &mut live_ranges,
                                input,
                                &mut output,
                                region,
                                OperandConstraint::Any,
                                run,
                            )
                            .unwrap();
                            want.recompute_constraint(&mut live_ranges, input);
                            want
                        });

                        assert_eq!(constraint, want.constraint(&live_ranges), "{context}");
                        assert_eq!(
                            has_fixed_uses,
                            want.has_fixed_uses(&live_ranges),
                            "{context}",
                        );
                        assert_eq!(spill_weight, want.spill_weight(&live_ranges), "{context}");
                        assert_eq!(is_minimal, want.is_minimal(&live_ranges), "{context}");
                    }
                }
            }
        }
    }

    /// The bundles' span lists do not overlap.
    ///
    /// The weaker half of [`check_bundle_runs_tile_storage`], and all that is
    /// left once a within-span split has relocated a half and left a hole
    /// where it was.
    fn check_bundle_runs_are_disjoint(live_ranges: &LiveRanges<u32>) {
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
            assert!(start >= next, "{bundle:?}'s run overlaps another");
            next = end;
        }
        assert!(next <= live_ranges.bundle_spans_storage.len());
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

    /// No gap left to cut, and, if the bundle holds any use at all, only one
    /// instruction left to cover.
    #[test]
    fn the_minimal_floor_is_no_cuttable_gap_and_one_instruction() {
        assert!(is_minimal_bundle(0, 1, 1));
        assert!(is_minimal_bundle(0, 0, 1));

        // Several uses of the same instruction are fine. A move can only go
        // between instructions, so there is nowhere to separate them; that is
        // also why they may share a bundle even when they are unrelated.
        assert!(is_minimal_bundle(0, 2, 1));
        assert!(is_minimal_bundle(0, usize::MAX, 1));

        // How long a use-free bundle is does not matter. Cutting it up would
        // only make more bundles to place, every one of them as happy on the
        // stack as the whole thing was.
        assert!(is_minimal_bundle(0, 0, 2));
        assert!(is_minimal_bundle(0, 0, usize::MAX));

        // With a use, though, length is the whole question: an extra
        // instruction is an interior boundary to cut at, and a move can go
        // there.
        assert!(!is_minimal_bundle(0, 1, 2));
        assert!(!is_minimal_bundle(0, 1, usize::MAX));

        // A cuttable gap settles it on its own, however few uses and however
        // little the bundle covers: the two sides could be handed out one
        // bundle each.
        assert!(!is_minimal_bundle(1, 1, 1));
        assert!(!is_minimal_bundle(1, 0, 1));
        assert!(!is_minimal_bundle(usize::MAX, 0, usize::MAX));
    }

    #[test]
    fn live_span_properties() -> CheckResult<TestInput> {
        // How many reads are split out into a doomed piece *only* because a
        // later tie names another read of the same value, rather than because
        // the value outlives the instruction. The walk below reached that case
        // zero times before the seeds were added, so every property here was
        // blind to how such a value is cut up.
        //
        // Derived from the input rather than counted in `analyze_spans`: its
        // `Counts` is local to it, and a `Count` stores nothing at all without
        // `feature = "trace-log"`.
        static TIE_ONLY_SPLITS: AtomicUsize = AtomicUsize::new(0);
        TIE_ONLY_SPLITS.store(0, Ordering::Relaxed);

        let result = Check::new().iters(10_000).run_with(
            m::default::<TestInput>(),
            seeds(),
            |test_input: &TestInput| -> Result<(), String> {
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
                            let this = reuse_aware_constraint(
                                input,
                                use_data.point(&live_ranges).inst(),
                                use_data.operand(&live_ranges),
                            );
                            match constraint.merge_resolved(&this, input.machine) {
                                Some(merged) => constraint = merged,
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

                // 1e. `uses_at` brackets exactly the uses at a point. It
                // binary searches, which property 1b's ascending order
                // licenses; the oracle here is the linear scan that the binary
                // search replaced.
                for span in live_ranges.spans() {
                    let mut points: Vec<LivePoint<u32>> = span
                        .uses(&live_ranges)
                        .into_iter()
                        .map(|u| u.point(&live_ranges))
                        .collect();
                    // Points with no use at all, on both sides of the span, so
                    // that the empty answer is checked too.
                    points.push(span.start(&live_ranges));
                    points.push(span.end(&live_ranges));
                    points.push(span.start(&live_ranges).inst_boundary_at_or_before());

                    for point in points {
                        let expected: Vec<_> = span
                            .uses(&live_ranges)
                            .into_iter()
                            .filter(|u| u.point(&live_ranges) == point)
                            .collect();
                        let actual: Vec<_> =
                            span.uses_at(&live_ranges, point).into_iter().collect();
                        if actual != expected {
                            return Err(format!(
                                "{span:?}'s uses at {point:?} are {expected:?}, but `uses_at` \
                                 answered {actual:?}",
                            ));
                        }
                    }
                }

                // 2. A value has at most one span per block, and its spans
                // barely overlap.
                //
                // Splitting a conflict is what makes it "at most one": a
                // value's pieces in a block ascend and leave no gap, and may
                // overlap only within the instruction the later one begins at,
                // which it always does at that instruction's boundary. Anything
                // wider, or a piece starting mid-instruction, would need a move
                // where there is no gap to put one.
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

                        // The later piece begins at an instruction boundary,
                        // which is the only place a move between the two
                        // allocations can go.
                        let start_is_legal = point.pos() == Position::Early;

                        // And the overlap stays inside that instruction.
                        let overlap_is_narrow =
                            first.end(&live_ranges) <= point.inst_boundary_after();

                        if !start_is_legal || !overlap_is_narrow {
                            return Err(format!(
                                "{span_a:?} ({a_start:?}..{a_end:?}) and {span_b:?} \
                                 ({b_start:?}..{b_end:?}) are both for {:?}, but {second:?} does \
                                 not begin at an instruction boundary or they overlap by more \
                                 than the instruction it begins at",
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

                    // 8. A span with no uses begins and ends at an
                    // instruction boundary.
                    //
                    // Such a piece only carries its value from one boundary to
                    // another, and a boundary is the only place a move into or
                    // out of it can go. One ending mid-instruction holds a
                    // register that nothing reads.
                    for &span in &spans_in[&block] {
                        if !span.uses(&live_ranges).is_empty() {
                            continue;
                        }
                        let (start, end) = (span.start(&live_ranges), span.end(&live_ranges));
                        if start.pos() != Position::Early || end.pos() != Position::Early {
                            return Err(format!(
                                "{span:?} covers {start:?}..{end:?} of {block:?} and has no \
                                 uses, so it holds a location that nothing reads",
                            ));
                        }
                    }
                }

                // 9. Every operand is accounted for: a def starts its value's
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

                // 10. Each use's weight is the cost model applied to that
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

                            // A tie strengthens `Any` into the value's class,
                            // which may hold one register, as construction saw.
                            any_fixed |= match reuse_aware_constraint(input, point.inst(), operand)
                            {
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

                // Count the reads the tie disjunct alone splits out, for the
                // non-vacuity assertion below. `end` is the value's live range
                // end in the block, which is what construction compares the
                // tie's point against, and so the last piece's end.
                test_input.with_input(|input| {
                    for &(block, point, i, kind, val) in &operands {
                        if kind != DefUse::Use {
                            continue;
                        }
                        let input_inst = input.func.inst(point.inst());
                        let end = spans_of[&(val, block)]
                            .iter()
                            .map(|span| span.end(&live_ranges))
                            .max()
                            .expect("property 9 found a span for every operand's value");
                        if is_reuse_target(&input_inst, i)
                            && end <= point.next_point()
                            && another_tie_follows(&input_inst, i)
                        {
                            TIE_ONLY_SPLITS.fetch_add(1, Ordering::Relaxed);
                        }
                    }
                });

                // 11. Constructing twice gives exactly the same spans and uses.
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

                // 12. Both halves reset cleanly, including the scratch that
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
            },
        );

        if result.is_ok() {
            assert!(
                TIE_ONLY_SPLITS.load(Ordering::Relaxed) > 0,
                "no input reached a read that only a later tie splits out, so no property \
                 here saw one",
            );
        }

        result
    }
}
