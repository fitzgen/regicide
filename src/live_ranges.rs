//! Constructs live ranges and bundles.

use crate::context::ContextInner;
use crate::entity::{
    Entity, EntityRange, EntityRepr, FixedEntitySet, Inst, PrimaryMap, Region, SecondaryMap, Val,
    WideInt, words_for,
};
use crate::error::IResult;
use crate::input::{DefUse, InputFunction, Position};
use crate::liveness::Liveness;
use crate::output::Allocation;
use crate::region_tree::RegionTree;
use crate::timing::Timing;
use crate::{RegClass, RegSet};
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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LivePoint<E>
where
    E: EntityRepr,
{
    /// +-------------------------+--------+
    /// | inst: bits(E::Wide) - 1 | pos: 1 |
    /// +-------------------------+--------+
    bits: E::Wide,
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

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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

    pub fn construct(
        &mut self,
        func: &impl InputFunction,
        region_tree: &RegionTree<E>,
        liveness: &Liveness<E>,
    ) -> IResult<()> {
        let _timing = Timing::new("live ranges");
        // TODO
        let _ = (func, region_tree, liveness);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
}
