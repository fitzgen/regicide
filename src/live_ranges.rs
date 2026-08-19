//! Constructs live ranges and bundles.

use crate::counts::Counts;
use crate::entity::{
    Entity, EntityRange, EntityRepr, Inst, PrimaryMap, Region, SecondaryMap, Val, WideInt,
};
use crate::error::IResult;
use crate::input::{Input, InputFunction, InputInst, OperandConstraint, Position};
use crate::liveness::Liveness;
use crate::output::{Allocation, OutputInner};
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

/// How much it would cost to spill a value, rather than keep it in a register.
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
    #[allow(dead_code, reason = "will probably need it")]
    pub const fn as_f32(self) -> f32 {
        self.0.as_f32()
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
    ///
    /// `Operand` does carry a constraint now, and live span construction reads
    /// it to split spans whose uses conflict. What is still missing is a way to
    /// ask a `Machine` whether a class holds a single register, which is what
    /// both the weight and `SPAN_HAS_FIXED_USE` need.
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
    #[allow(dead_code, reason = "will probably need it")]
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
    ///
    /// The constraints are reachable now; see [`UseData::new`] for what is still
    /// missing before `has_fixed_use` can be set here.
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
    #[allow(dead_code, reason = "will probably need it")]
    pub fn uses(&self) -> EntityRange<Use<E>> {
        self.uses
    }

    #[inline]
    #[allow(dead_code, reason = "will probably need it")]
    pub fn start(&self) -> LivePoint<E> {
        self.start
    }

    #[inline]
    #[allow(dead_code, reason = "will probably need it")]
    pub fn end(&self) -> LivePoint<E> {
        self.end
    }

    #[inline]
    #[allow(dead_code, reason = "will probably need it")]
    pub fn val(&self) -> Val<E> {
        self.val
    }

    #[inline]
    #[allow(dead_code, reason = "will probably need it")]
    pub fn is_pinned(&self) -> bool {
        self.flags & SPAN_PINNED != 0
    }

    #[inline]
    #[allow(dead_code, reason = "will probably need it")]
    pub fn has_fixed_use(&self) -> bool {
        self.flags & SPAN_HAS_FIXED_USE != 0
    }
}

#[expect(dead_code, reason = "will probably need it")]
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
    class: RegClass,

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
const BUNDLE_SPILL_WEIGHT_MASK: u32 = PackedPositiveFloat::<u32, BUNDLE_SPILL_WEIGHT_BITS>::MASK;
const BUNDLE_HAS_FIXED_USES: u32 = 1 << 29;
const BUNDLE_PINNED: u32 = 1 << 30;
const BUNDLE_MINIMAL: u32 = 1 << 31;

impl<E> LiveBundleData<E>
where
    E: EntityRepr,
{
    #[inline]
    #[expect(dead_code, reason = "will probably need it")]
    pub fn spans(&self) -> EntityRange<LiveSpan<E>> {
        self.spans
    }

    #[inline]
    #[expect(dead_code, reason = "will probably need it")]
    pub fn region(&self) -> Region<E> {
        self.region
    }

    #[inline]
    #[expect(dead_code, reason = "will probably need it")]
    pub fn class(&self) -> RegClass {
        self.class
    }

    #[inline]
    #[expect(dead_code, reason = "will probably need it")]
    pub fn preferrence(&self) -> &RegSet {
        &self.preferrence
    }

    #[inline]
    #[expect(dead_code, reason = "will probably need it")]
    pub fn allocation(&self) -> Option<Allocation<E>> {
        self.allocation
    }

    #[inline]
    #[allow(dead_code, reason = "will probably need it")]
    pub fn is_minimal(&self) -> bool {
        self.weight_and_flags & BUNDLE_MINIMAL != 0
    }

    #[inline]
    #[allow(dead_code, reason = "will probably need it")]
    pub fn is_pinned(&self) -> bool {
        self.weight_and_flags & BUNDLE_PINNED != 0
    }

    #[inline]
    #[allow(dead_code, reason = "will probably need it")]
    pub fn has_fixed_uses(&self) -> bool {
        self.weight_and_flags & BUNDLE_HAS_FIXED_USES != 0
    }

    #[inline]
    #[allow(dead_code, reason = "will probably need it")]
    pub fn spill_weight(&self) -> f32 {
        PackedPositiveFloat::<u32, BUNDLE_SPILL_WEIGHT_BITS>::from_bits(
            self.weight_and_flags & BUNDLE_SPILL_WEIGHT_MASK,
        )
        .as_f32()
    }
}

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
    #[expect(dead_code, reason = "will probably need it")]
    pub fn len_spans(&self) -> usize {
        self.spans.len()
    }

    /// Iterate over every live span that has been constructed.
    #[allow(dead_code, reason = "will probably need it")]
    pub fn spans(&self) -> impl Iterator<Item = (LiveSpan<E>, &LiveSpanData<E>)> + '_ {
        self.spans.iter()
    }

    /// Get the data for one live span.
    #[allow(dead_code, reason = "will probably need it")]
    pub fn span(&self, span: LiveSpan<E>) -> &LiveSpanData<E> {
        &self.spans[span]
    }

    /// How many uses have been recorded?
    #[allow(dead_code, reason = "will probably need it")]
    pub fn len_uses(&self) -> usize {
        self.uses.len()
    }

    /// Get the data for one use.
    #[allow(dead_code, reason = "will probably need it")]
    pub fn use_data(&self, u: Use<E>) -> &UseData<E> {
        &self.uses[u]
    }

    /// Get the uses for the given span, in ascending program order.
    #[allow(dead_code, reason = "will probably need it")]
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
            val_bundle: _,
        } = self;

        // Construct a span for each value live in or across this block.
        for (block, _input_block) in input.func.blocks() {
            let block = output.with_repr(block)?;
            for span in liveness.block_spans(input.func, block, uses, output)? {
                push_span_and_split_conflicts(input, uses, spans, counts, span, output)?;
            }
        }

        counts.live_spans += spans.len();
        counts.uses += uses.len();
        Ok(())
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
    output: &mut OutputInner<E>,
) -> IResult<()>
where
    E: EntityRepr,
{
    // The piece we are accumulating: where it starts, where its uses start, and
    // the merged constraint of everything folded into it so far.
    let mut piece_start = start;
    let mut piece_uses_start = span_uses.start;
    let mut piece_constraint = OperandConstraint::Any;

    let mut last_point = start;
    for use_ in span_uses {
        let use_data = &uses[use_];
        let point = use_data.point();

        let input_inst = input.func.inst(point.inst().with_repr32());
        let sibling = |j| input_inst.operand(j).constraint();
        let use_constraint = input_inst.operand(use_data.operand()).constraint();
        match piece_constraint.merge(
            &use_constraint,
            input.machine,
            |_| unreachable!("the accumulated constraint is always resolved"),
            &sibling,
        ) {
            // No conflict: we can fold `use_` into this piece.
            Some(merged) => {
                piece_constraint = merged.resolved(&sibling);
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
                    ),
                )?;
                counts.eager_splits += 1u64;

                piece_start = point;
                piece_uses_start = use_;
                piece_constraint = use_constraint.resolved(&sibling);
                last_point = point;
            }
        }
    }

    // The final piece runs to the end of the given span.
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
        ),
    )?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::DefUse;
    use crate::dfs::Dfs;
    use crate::entity::Block;
    use crate::input::InputBlock as _;
    use crate::region_tree::RegionTree;
    use crate::sccs::StronglyConnectedComponents;
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
        let weight = PackedPositiveFloat::<u32, BUNDLE_SPILL_WEIGHT_BITS>::new(3.25).bits();

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

    /// Compute the liveness and live spans of `test_input`'s function.
    fn analyze_spans(test_input: &TestInput) -> Result<(Liveness<u32>, LiveRanges<u32>), String> {
        let mut counts = Counts::new();
        let mut dfs = Dfs::<u32>::new();
        let mut sccs = StronglyConnectedComponents::<u32>::new();
        let mut region_tree = RegionTree::<u32>::new();
        let mut liveness = Liveness::<u32>::new();
        let mut live_ranges = LiveRanges::<u32>::new();
        let mut output = OutputInner::<u32>::new();

        assert!(live_ranges.is_reset());

        let result = test_input.with_input(|input| {
            let func = input.func;
            sccs.construct(func, &mut counts, &mut dfs, &mut output)
                .and_then(|()| region_tree.construct(func, &mut counts, &sccs, &mut output))
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

        let spans: Vec<_> = live_ranges
            .spans()
            .map(|(span, data)| (span, *data))
            .collect();
        assert_eq!(spans.len(), 2, "{spans:#?}");

        // The def, and then the two uses that cannot share a location.
        let def = LivePoint::new(inst(0), Position::Late);
        let first_use = LivePoint::new(inst(1), Position::Early);
        let second_use = LivePoint::new(inst(2), Position::Early);

        let (first, second) = (spans[0].1, spans[1].1);
        assert_eq!(first.val(), second.val());
        assert_eq!(first.start(), def);
        assert_eq!(
            first.end(),
            second_use,
            "the cut is just before the conflict"
        );
        assert_eq!(second.start(), second_use);
        assert!(second.end() > second_use);

        // Each use is recorded by the piece that can satisfy it, and the def by
        // the piece it starts.
        let points = |span| -> Vec<LivePoint<u32>> {
            live_ranges
                .uses(span)
                .iter()
                .map(|use_data| use_data.point())
                .collect()
        };
        assert_eq!(points(spans[0].0), vec![def, first_use]);
        assert_eq!(points(spans[1].0), vec![second_use]);

        // The control: `rc2` holds both registers, so it can be satisfied
        // alongside `rc0` and there is nothing to split.
        let test_input = TestInput::with_use_constraints(&[rc(0), rc(2)]);
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();
        assert_eq!(live_ranges.spans().count(), 1);
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

                // 1d. One span is one allocation, so all of a span's uses have
                // to be satisfiable by a single location. Fold their
                // constraints the way construction does; folding is exact,
                // because the machine's class list is closed under
                // intersection, so a fold that succeeds really does describe a
                // location that every use accepts. This is the property that
                // eager splitting buys.
                test_input.with_input(|input| -> Result<(), String> {
                    for (span, _data) in live_ranges.spans() {
                        let mut constraint = OperandConstraint::Any;
                        for use_data in live_ranges.uses(span) {
                            // Fold the way construction folds, down to
                            // resolving each answer against the instruction it
                            // came from, so that this is a check on where the
                            // spans were cut and not on a second reading of the
                            // same operands.
                            let input_inst = input.func.inst(use_data.point().inst());
                            let sibling = |j| input_inst.operand(j).constraint();
                            let this = input_inst.operand(use_data.operand()).constraint();
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
                                        use_data.point(),
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
                        let previous = live_ranges.span(pair[0]);
                        let next = live_ranges.span(pair[1]);
                        if next.start() < previous.start() || next.start() > previous.end() {
                            return Err(format!(
                                "{val:?}'s spans in {block:?} are out of order or leave a gap: \
                                 {:?}..{:?} is followed by {:?}..{:?}",
                                previous.start(),
                                previous.end(),
                                next.start(),
                                next.end(),
                            ));
                        }
                    }
                }
                for (span_a, a) in live_ranges.spans() {
                    for (span_b, b) in live_ranges.spans() {
                        if span_a >= span_b || a.val() != b.val() {
                            continue;
                        }
                        if a.start() >= b.end() || b.start() >= a.end() {
                            continue;
                        }

                        // Order the two by `(start, end)` rather than by start
                        // alone, so that two pieces that begin at the same point
                        // -- what a third conflicting use at that point leaves
                        // behind -- are still compared earlier-first.
                        let (first, second) = if (a.start(), a.end()) <= (b.start(), b.end()) {
                            (span_a, span_b)
                        } else {
                            (span_b, span_a)
                        };
                        let point = live_ranges.span(second).start();
                        let both_use_it = [first, second].into_iter().all(|span| {
                            live_ranges
                                .uses(span)
                                .iter()
                                .any(|use_data| use_data.point() == point)
                        });
                        if live_ranges.span(first).end() != point.next_point() || !both_use_it {
                            return Err(format!(
                                "{span_a:?} ({:?}..{:?}) and {span_b:?} ({:?}..{:?}) are both \
                                 for {:?} and overlap by more than the one program point at \
                                 which both of them record a use",
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
                                // A parameter is live-in, so its range starts
                                // at the entry however many pieces the range is
                                // later split into.
                                Some([first, ..]) => {
                                    let data = live_ranges.span(*first);
                                    if data.start() != block_start {
                                        return Err(format!(
                                            "{param:?} is live-in at {block:?}, but its first \
                                             span starts at {:?} rather than the block's entry \
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
                        let first = live_ranges.span(*spans.first().unwrap());
                        let last = live_ranges.span(*spans.last().unwrap());
                        if first.start() != block_start || last.end() != block_end {
                            return Err(format!(
                                "{val:?} is live across all of {block:?}, but its spans cover \
                                 only {:?}..{:?} of {block_start:?}..{block_end:?}",
                                first.start(),
                                last.end(),
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
                            let data = live_ranges.span(*spans.first().unwrap());
                            if data.start() != point {
                                return Err(format!(
                                    "{val:?} is defined at {point:?} in {block:?}, but its first \
                                     span there starts at {:?}",
                                    data.start(),
                                ));
                            }
                        }
                        // A use only has to fall inside one of the pieces.
                        DefUse::Use => {
                            let covered = spans.iter().any(|&span| {
                                let data = live_ranges.span(span);
                                point >= data.start() && point < data.end()
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
                        live_ranges
                            .uses(span)
                            .iter()
                            .any(|use_data| use_data.point() == point && use_data.operand() == i)
                    });
                    if !recorded {
                        return Err(format!(
                            "operand {i} of {point:?} names {val:?}, but no span of {val:?} in \
                             {block:?} records it as one of its uses",
                        ));
                    }
                }

                // 9. Constructing twice gives exactly the same spans and uses.
                let (_, again) = analyze_spans(test_input)?;
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
