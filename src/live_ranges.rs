//! Constructs live ranges and bundles.

use crate::context::ContextInner;
use crate::counts::Counts;
use crate::entity::{
    Entity, EntityRange, EntityRepr, FixedEntitySet, Inst, PrimaryMap, Region, SecondaryMap, Val,
    WideInt, words_for,
};
use crate::error::IResult;
use crate::input::{DefUse, InputFunction, Position};
use crate::liveness::Liveness;
use crate::output::{Allocation, OutputInner};
use crate::region_tree::RegionTree;
use crate::timing::Timing;
use crate::{RegClass, RegSet};
use alloc::vec::Vec;
use core::range::Range;

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
}

/// Pack a non-negative `f32` into its most-significant `BITS` bits.
///
/// An `f32` is `[sign: 1, exponent: 8, mantissa: 23]`. Dropping the sign, which
/// is always clear for the weights we store, leaves 31 bits; we keep the top
/// `BITS` of those and truncate the rest.
///
/// Because the exponent sits immediately below the discarded sign, the packed
/// bits of two weights compare in the same order as the weights themselves.
///
/// `BITS` must be within `1..=31`.
#[inline]
fn pack_positive_f32<const BITS: u32>(weight: f32) -> u32 {
    debug_assert!(BITS >= 1 && BITS <= 31);
    debug_assert!(
        weight.is_sign_positive(),
        "the sign bit is not stored, so it must be clear"
    );
    (weight.to_bits() >> (31 - BITS)) & ((1u32 << BITS) - 1)
}

/// Unpack an `f32` packed by [`pack_positive_f32`], with the truncated low
/// mantissa bits restored as zeroes.
#[inline]
fn unpack_positive_f32<const BITS: u32>(bits: u32) -> f32 {
    debug_assert!(BITS >= 1 && BITS <= 31);
    debug_assert_eq!(bits >> BITS, 0, "bits above the packed field must be clear");
    f32::from_bits(bits << (31 - BITS))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SpillWeight {
    /// The top bits of an `f32`, except the sign bit, since weights are always
    /// positive. This is basically the same as `bfloat16`, except with an extra
    /// bit of mantissa instead of the sign.
    bits: u16,
}

impl SpillWeight {
    const BITS: u32 = (core::mem::size_of::<Self>() * (u8::BITS as usize)) as u32;

    #[inline]
    pub fn new(weight: f32) -> Self {
        SpillWeight {
            bits: pack_positive_f32::<{ Self::BITS }>(weight) as u16,
        }
    }

    #[inline]
    pub fn as_f32(self) -> f32 {
        unpack_positive_f32::<{ Self::BITS }>(u32::from(self.bits))
    }
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

    /// Whether this is a use or a def of `self.val`.
    weight: SpillWeight,
}

impl<E> UseData<E>
where
    E: EntityRepr,
{
    /// Create a `UseData` for the `operand`th operand of `point`'s instruction.
    ///
    /// TODO: the weight is a placeholder. Computing a real spill weight (and
    /// setting [`SPAN_HAS_FIXED_USE`] on the containing span) needs the
    /// operand's register constraint, and `Operand` does not carry one yet.
    #[inline]
    pub(crate) fn new(point: LivePoint<E>, operand: usize, weight: SpillWeight) -> Self {
        debug_assert!(operand < MAX_OPERANDS_PER_INST);
        UseData {
            point,
            operand: u16::try_from(operand).unwrap(),
            weight,
        }
    }

    #[inline]
    pub fn point(&self) -> LivePoint<E> {
        self.point
    }

    #[inline]
    pub fn operand(&self) -> usize {
        usize::try_from(self.operand).unwrap()
    }

    #[inline]
    pub fn weight(&self) -> SpillWeight {
        self.weight
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

    /// Bit:     1                  0
    ///        +------------------+-----------+
    /// Field: | has_fixed_use: 1 | pinned: 1 |
    ///        +------------------+-----------+
    flags: u8,
}

const SPAN_PINNED: u8 = 1 << 0;
const SPAN_HAS_FIXED_USE: u8 = 1 << 1;

impl<E> LiveSpanData<E>
where
    E: EntityRepr,
{
    /// Create a span covering `[start, end)` for `val`, with the given uses.
    ///
    /// The flags all start clear: pinning happens later, and `has_fixed_use`
    /// needs register constraints that `Operand` does not carry yet.
    #[inline]
    pub(crate) fn new(
        start: LivePoint<E>,
        end: LivePoint<E>,
        val: Val<E>,
        uses: EntityRange<Use<E>>,
    ) -> Self {
        debug_assert!(start < end);
        LiveSpanData {
            start,
            end,
            uses,
            val,
            flags: 0,
        }
    }

    /// This span's uses (and, possibly, def), in ascending program order.
    #[inline]
    pub fn uses(&self) -> EntityRange<Use<E>> {
        self.uses
    }

    #[inline]
    pub fn start(&self) -> LivePoint<E> {
        self.start
    }

    #[inline]
    pub fn end(&self) -> LivePoint<E> {
        self.end
    }

    #[inline]
    pub fn val(&self) -> Val<E> {
        self.val
    }

    #[inline]
    pub fn is_pinned(&self) -> bool {
        self.flags & SPAN_PINNED != 0
    }

    #[inline]
    pub fn has_fixed_use(&self) -> bool {
        self.flags & SPAN_HAS_FIXED_USE != 0
    }
}

pub struct LiveBundleData<E>
where
    E: EntityRepr,
{
    /// The spans contained inside this bundle.
    spans: EntityRange<LiveSpan<E>>,

    /// The region that this bundle is within.
    ///
    /// Bundles never span across regions.
    region: Region<E>,

    /// The registers that this bundle can be allocated to.
    class: RegClass<E>,

    /// The subset of `self.candidates` that this bundle would prefer to be
    /// allocated within.
    preferrence: RegSet,

    /// Where this bundle is currently allocated.
    allocation: Option<Allocation<E>>,

    /// Packed weight and flags.
    ///
    /// Keeping the flags *above* the weight is what makes a minimal bundle sort
    /// above every ordinary one under a plain integer comparison of
    /// `weight_and_flags`, rather than under a rule that every comparison site
    /// has to remember to apply.
    ///
    /// Bit:     31           30          29                  28     ...     0
    ///        +------------+-----------+-------------------+------------------+
    /// Field: | minimal: 1 | pinned: 1 | has_fixed_uses: 1 | spill_weight: 30 |
    ///        +------------+-----------+-------------------+------------------+
    weight_and_flags: u32,
}

const BUNDLE_SPILL_WEIGHT_BITS: u32 = 29;
const BUNDLE_SPILL_WEIGHT_MASK: u32 = (1 << BUNDLE_SPILL_WEIGHT_BITS) - 1;
const BUNDLE_HAS_FIXED_USES: u32 = 1 << 29;
const BUNDLE_PINNED: u32 = 1 << 30;
const BUNDLE_MINIMAL: u32 = 1 << 31;

impl<E> LiveBundleData<E>
where
    E: EntityRepr,
{
    #[inline]
    pub fn spans(&self) -> EntityRange<LiveSpan<E>> {
        self.spans
    }

    #[inline]
    pub fn region(&self) -> Region<E> {
        self.region
    }

    #[inline]
    pub fn class(&self) -> RegClass<E> {
        self.class
    }

    #[inline]
    pub fn preferrence(&self) -> &RegSet {
        &self.preferrence
    }

    #[inline]
    pub fn allocation(&self) -> Option<Allocation<E>> {
        self.allocation
    }

    #[inline]
    pub fn is_minimal(&self) -> bool {
        self.weight_and_flags & BUNDLE_MINIMAL != 0
    }

    #[inline]
    pub fn is_pinned(&self) -> bool {
        self.weight_and_flags & BUNDLE_PINNED != 0
    }

    #[inline]
    pub fn has_fixed_uses(&self) -> bool {
        self.weight_and_flags & BUNDLE_HAS_FIXED_USES != 0
    }

    #[inline]
    pub fn spill_weight(&self) -> f32 {
        unpack_positive_f32::<BUNDLE_SPILL_WEIGHT_BITS>(
            self.weight_and_flags & BUNDLE_SPILL_WEIGHT_MASK,
        )
    }
}

type Priority = u32;

pub struct LiveRanges<E>
where
    E: EntityRepr,
{
    /// Arena of all uses in the input function.
    uses: PrimaryMap<Use<E>, UseData<E>>,

    /// The live spans for the input function's values.
    spans: PrimaryMap<LiveSpan<E>, LiveSpanData<E>>,

    /// The live bundles.
    bundles: PrimaryMap<LiveBundle<E>, LiveBundleData<E>>,

    /// Each value's initial bundle, before we do any splitting during
    /// allocation.
    val_bundle: SecondaryMap<Val<E>, Option<LiveBundle<E>>>,
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
            val_bundle: SecondaryMap::new(None),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            uses,
            spans,
            bundles,
            val_bundle,
        } = self;
        uses.reset();
        spans.reset();
        bundles.reset();
        val_bundle.reset();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            uses,
            spans,
            bundles,
            val_bundle,
        } = self;
        uses.is_reset() && spans.is_reset() && bundles.is_reset() && val_bundle.is_reset()
    }

    /// How many live spans have been constructed?
    pub fn len_spans(&self) -> usize {
        self.spans.len()
    }

    /// Iterate over every live span that has been constructed.
    pub fn spans(&self) -> impl Iterator<Item = (LiveSpan<E>, &LiveSpanData<E>)> + '_ {
        self.spans.iter()
    }

    /// Get the data for one live span.
    pub fn span(&self, span: LiveSpan<E>) -> &LiveSpanData<E> {
        &self.spans[span]
    }

    /// How many uses have been recorded?
    pub fn len_uses(&self) -> usize {
        self.uses.len()
    }

    /// Get the data for one use.
    pub fn use_data(&self, u: Use<E>) -> &UseData<E> {
        &self.uses[u]
    }

    /// Get the uses for the given span, in ascending program order.
    pub fn uses(&self, span: LiveSpan<E>) -> &[UseData<E>] {
        let indices = self.span(span).uses.indices();
        &self.uses.as_slice()[indices]
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
        func: &impl InputFunction,
        counts: &mut Counts,
        region_tree: &RegionTree<E>,
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
            val_bundle: _,
        } = self;

        // Construct a span for each value live in or across this block.
        for (block, _input_block) in func.blocks() {
            let block = output.with_repr(block)?;
            for (start, end, val, span_uses) in liveness.block_spans(func, block, uses, output)? {
                spans.push(output, LiveSpanData::new(start, end, val, span_uses))?;
            }
        }

        counts.live_spans += spans.len();
        counts.uses += uses.len();
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dfs::Dfs;
    use crate::entity::Block;
    use crate::input::{InputBlock as _, InputInst as _};
    use crate::sccs::StronglyConnectedComponents;
    use crate::test::TestFunction;
    use mutatis::check::{Check, CheckResult};
    use std::{
        collections::{BTreeSet as Set, HashMap},
        format,
        string::{String, ToString},
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

    #[test]
    fn spill_weight_round_trips_approximately() {
        for weight in [0.0f32, 1e-20, 0.5, 1.0, 3.25, 123.456, 1e20] {
            let unpacked = SpillWeight::new(weight).as_f32();
            // Truncating the low mantissa bits only ever rounds towards zero,
            // and keeps 8 bits of mantissa.
            assert!(unpacked <= weight, "{unpacked} <= {weight}");
            assert!(
                unpacked >= weight * (1.0 - 1.0 / 256.0),
                "{unpacked} >= {weight} * (1 - 1/256)"
            );
        }

        // Infinity survives, since the exponent is kept whole.
        assert_eq!(SpillWeight::new(f32::INFINITY).as_f32(), f32::INFINITY);
    }

    /// Packed weights must compare in the same order as the weights they encode,
    /// since that is how they are used.
    #[test]
    fn spill_weight_bits_are_monotonic() {
        let mut previous = SpillWeight::new(0.0).bits;
        for weight in [1e-20f32, 0.5, 1.0, 2.0, 1000.0, 1e20] {
            let bits = SpillWeight::new(weight).bits;
            assert!(bits > previous, "{bits} > {previous} for {weight}");
            previous = bits;
        }
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

    #[test]
    fn span_flags_are_independent() {
        assert!(!span(0).is_pinned());
        assert!(!span(0).has_fixed_use());

        assert!(span(SPAN_PINNED).is_pinned());
        assert!(!span(SPAN_PINNED).has_fixed_use());

        assert!(!span(SPAN_HAS_FIXED_USE).is_pinned());
        assert!(span(SPAN_HAS_FIXED_USE).has_fixed_use());

        let both = span(SPAN_PINNED | SPAN_HAS_FIXED_USE);
        assert!(both.is_pinned());
        assert!(both.has_fixed_use());
    }

    fn bundle(weight_and_flags: u32) -> LiveBundleData<u32> {
        LiveBundleData {
            spans: EntityRange::empty(),
            region: Region::try_new(0).unwrap(),
            class: RegClass::try_new(0).unwrap(),
            preferrence: RegSet::new(),
            allocation: None,
            weight_and_flags,
        }
    }

    #[test]
    fn bundle_flags_do_not_disturb_the_weight() {
        let weight = pack_positive_f32::<BUNDLE_SPILL_WEIGHT_BITS>(3.25);

        let plain = bundle(weight);
        assert!(!plain.is_minimal());
        assert!(!plain.is_pinned());
        assert!(!plain.has_fixed_uses());
        assert_eq!(plain.spill_weight(), 3.25);

        let all = bundle(weight | BUNDLE_MINIMAL | BUNDLE_PINNED | BUNDLE_HAS_FIXED_USES);
        assert!(all.is_minimal());
        assert!(all.is_pinned());
        assert!(all.has_fixed_uses());
        assert_eq!(all.spill_weight(), 3.25);
    }

    /// The reason the flags sit above the weight: a minimal bundle outranks
    /// every ordinary one under a plain integer comparison, with no rule for a
    /// comparison site to remember.
    #[test]
    fn minimal_bundles_outrank_every_ordinary_weight() {
        let heaviest_ordinary = bundle(BUNDLE_SPILL_WEIGHT_MASK);
        let lightest_minimal = bundle(BUNDLE_MINIMAL);
        assert!(!heaviest_ordinary.is_minimal());
        assert!(lightest_minimal.is_minimal());
        assert!(lightest_minimal.weight_and_flags > heaviest_ordinary.weight_and_flags);
    }

    /// The flag bits and the weight field must exactly tile a `u32`.
    #[test]
    fn bundle_weight_and_flags_tile_a_u32() {
        assert_eq!(
            BUNDLE_SPILL_WEIGHT_MASK | BUNDLE_HAS_FIXED_USES | BUNDLE_PINNED | BUNDLE_MINIMAL,
            u32::MAX
        );
        for flag in [BUNDLE_HAS_FIXED_USES, BUNDLE_PINNED, BUNDLE_MINIMAL] {
            assert_eq!(flag & BUNDLE_SPILL_WEIGHT_MASK, 0);
        }
    }

    /// Compute `func`'s liveness and live spans.
    fn analyze_spans(func: &TestFunction) -> Result<(Liveness<u32>, LiveRanges<u32>), String> {
        let mut counts = Counts::new();
        let mut dfs = Dfs::<u32>::new();
        let mut sccs = StronglyConnectedComponents::<u32>::new();
        let mut region_tree = RegionTree::<u32>::new();
        let mut liveness = Liveness::<u32>::new();
        let mut live_ranges = LiveRanges::<u32>::new();
        let mut output = OutputInner::<u32>::new();

        assert!(live_ranges.is_reset());

        let result = sccs
            .construct(func, &mut counts, &mut dfs, &mut output)
            .and_then(|()| region_tree.construct(func, &mut counts, &sccs, &mut output))
            .and_then(|()| liveness.construct(func, &mut counts, &mut dfs, &mut output))
            .and_then(|()| {
                live_ranges.construct(func, &mut counts, &region_tree, &mut liveness, &mut output)
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
                        LivePoint::new(inst, operand.pos),
                        i,
                        operand.kind,
                        operand.val,
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

    #[test]
    fn live_span_properties() -> CheckResult<TestFunction> {
        Check::new()
            .iters(10_000)
            .run(|func: &TestFunction| -> Result<(), String> {
                let (mut liveness, live_ranges) = analyze_spans(func)?;

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
                for (span, data) in live_ranges.spans() {
                    if data.start() >= data.end() {
                        return Err(format!(
                            "{span:?} covers {:?}..{:?}, which is empty or backwards",
                            data.start(),
                            data.end(),
                        ));
                    }
                    if data.val().index() >= num_values {
                        return Err(format!(
                            "{span:?} is for {:?}, but the function only defines {num_values} \
                             values",
                            data.val(),
                        ));
                    }
                    let Some(&block) = inst_block.get(&data.start().inst()) else {
                        return Err(format!(
                            "{span:?} starts at {:?}, which is in no block",
                            data.start(),
                        ));
                    };
                    let (block_start, block_end) = bounds[&block];
                    if data.start() < block_start || data.end() > block_end {
                        return Err(format!(
                            "{span:?} covers {:?}..{:?}, which escapes {block:?}'s bounds \
                             {block_start:?}..{block_end:?}",
                            data.start(),
                            data.end(),
                        ));
                    }
                    spans_of.entry((data.val(), block)).or_default().push(span);
                    spans_in.get_mut(&block).unwrap().push(span);
                }

                // 1b. Each span's uses are inside it, are strictly ascending in
                // `(point, operand)`, and name real operands of that span's
                // value.
                for (span, data) in live_ranges.spans() {
                    let mut previous = None;
                    for use_data in live_ranges.uses(span) {
                        let key = (use_data.point(), use_data.operand());
                        if use_data.point() < data.start() || use_data.point() >= data.end() {
                            return Err(format!(
                                "{span:?} covers {:?}..{:?} but has a use at {:?}",
                                data.start(),
                                data.end(),
                                use_data.point(),
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
                            point == use_data.point()
                                && i == use_data.operand()
                                && val == data.val()
                        });
                        if !is_real {
                            return Err(format!(
                                "{span:?} records a use of {:?} at {:?}, operand {}, but no such \
                                 operand exists",
                                data.val(),
                                use_data.point(),
                                use_data.operand(),
                            ));
                        }
                    }
                }

                // 1c. The spans' use ranges tile the uses map exactly: every
                // recorded use belongs to exactly one span.
                let mut ranges: Vec<(usize, usize)> = live_ranges
                    .spans()
                    .map(|(_, data)| data.uses())
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

                // 2. A value has at most one span per block, and its spans are
                // pairwise disjoint.
                for ((val, block), spans) in &spans_of {
                    if spans.len() > 1 {
                        return Err(format!(
                            "{val:?} has {} spans in {block:?}, but should have at most one",
                            spans.len(),
                        ));
                    }
                }
                for (span_a, a) in live_ranges.spans() {
                    for (span_b, b) in live_ranges.spans() {
                        if span_a >= span_b || a.val() != b.val() {
                            continue;
                        }
                        if a.start() < b.end() && b.start() < a.end() {
                            return Err(format!(
                                "{span_a:?} ({:?}..{:?}) and {span_b:?} ({:?}..{:?}) are both \
                                 for {:?} and overlap",
                                a.start(),
                                a.end(),
                                b.start(),
                                b.end(),
                                a.val(),
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
                        .map(|&span| live_ranges.span(span))
                        .filter(|data| data.start() == block_start)
                        .map(|data| data.val())
                        .collect();
                    let mut expected: Set<Val> = liveness.live_in(block).collect();
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
                        .map(|&span| live_ranges.span(span))
                        .filter(|data| data.end() == block_end)
                        .map(|data| data.val())
                        .collect();
                    let mut expected: Set<Val> = liveness.live_out(block).collect();
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
                        if liveness.is_live_in(block, param) {
                            match spans.map(|s| s.as_slice()) {
                                Some([span]) => {
                                    let data = live_ranges.span(*span);
                                    if data.start() != block_start {
                                        return Err(format!(
                                            "{param:?} is live-in at {block:?}, but its span \
                                             starts at {:?} rather than the block's entry \
                                             {block_start:?}",
                                            data.start(),
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
                        let val = live_ranges.span(span).val();
                        let mentioned = operands
                            .iter()
                            .any(|&(b, _p, _i, _k, v)| b == block && v == val);
                        if !mentioned
                            && !liveness.is_live_in(block, val)
                            && !liveness.is_live_out(block, val)
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
                        if !liveness.is_live_in(block, val) || !liveness.is_live_out(block, val) {
                            continue;
                        }
                        let Some([span]) = spans_of.get(&(val, block)).map(|s| s.as_slice()) else {
                            return Err(format!(
                                "{val:?} is live across all of {block:?}, but does not have \
                                 exactly one span there",
                            ));
                        };
                        let data = live_ranges.span(*span);
                        if data.start() != block_start || data.end() != block_end {
                            return Err(format!(
                                "{val:?} is live across all of {block:?}, but its span covers \
                                 only {:?}..{:?} of {block_start:?}..{block_end:?}",
                                data.start(),
                                data.end(),
                            ));
                        }
                    }
                }

                // 8. Every operand is accounted for: a def starts its value's
                // span exactly at its own program point, a use is strictly
                // inside one, and either way the span records it.
                for &(block, point, i, kind, val) in &operands {
                    let Some([span]) = spans_of.get(&(val, block)).map(|s| s.as_slice()) else {
                        return Err(format!(
                            "{block:?} has an operand at {point:?} naming {val:?}, but {val:?} \
                             does not have exactly one span in {block:?}",
                        ));
                    };
                    let data = live_ranges.span(*span);
                    match kind {
                        DefUse::Def if data.start() != point => {
                            return Err(format!(
                                "{val:?} is defined at {point:?} in {block:?}, but its span \
                                 there starts at {:?}",
                                data.start(),
                            ));
                        }
                        DefUse::Use if point < data.start() || point >= data.end() => {
                            return Err(format!(
                                "{val:?} is used at {point:?} in {block:?}, but its span there \
                                 covers only {:?}..{:?}",
                                data.start(),
                                data.end(),
                            ));
                        }
                        _ => {}
                    }
                    let recorded = live_ranges
                        .uses(*span)
                        .iter()
                        .any(|use_data| use_data.point() == point && use_data.operand() == i);
                    if !recorded {
                        return Err(format!(
                            "{span:?} covers the operand {i} of {point:?}, which names {val:?}, \
                             but does not record it as one of its uses",
                        ));
                    }
                }

                // 9. Constructing twice gives exactly the same spans and uses.
                let (_, again) = analyze_spans(func)?;
                let first: Vec<_> = live_ranges.spans().map(|(_, data)| *data).collect();
                let second: Vec<_> = again.spans().map(|(_, data)| *data).collect();
                if first != second {
                    return Err("constructing twice gave different spans".to_string());
                }
                if live_ranges.len_uses() != again.len_uses() {
                    return Err("constructing twice gave different uses".to_string());
                }
                for index in 0..live_ranges.len_uses() {
                    let u = Use::try_new(index).unwrap();
                    if live_ranges.use_data(u) != again.use_data(u) {
                        return Err(format!("constructing twice gave {u:?} different data"));
                    }
                }

                // 10. Both halves reset cleanly, including the scratch that
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
