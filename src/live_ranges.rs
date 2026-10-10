//! Constructs live ranges and bundles.

use crate::counts::Counts;
use crate::entity::{
    Block, Entity, EntityRange, EntityRepr, Inst, PrimaryMap, Region, SecondaryMap, Val, WideInt,
};
use crate::error::IResult;
use crate::events::EventsLog;
use crate::input::{
    BlockFrequency, DefUse, Input, InputBlock, InputFunction, InputInst, InputValue,
    OperandConstraint, Position, RematCost,
};
use crate::liveness::{Liveness, block_first_inst, block_last_inst};
use crate::machine::{Machine, Reg, RegClassMembers};
use crate::output::{OutputInner, RegAllocation};
use crate::packed_float::PackedPositiveFloat;
use crate::region_tree::RegionTree;
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

    /// A register held for one fixed operand, outside of any value's live
    /// range.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Reservation = "reservation";
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
/// in a register: holding a register across its live range buys nothing at all.
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

/// How much cheaper rematerializing a value makes holding it across a range.
///
/// This is a discount on length, not on uses.
pub(crate) fn remat_scale(remat_cost: Option<RematCost>) -> f32 {
    match remat_cost {
        None => 1.0,
        Some(RematCost::AlwaysRemat) => REMAT_ALWAYS_SCALE,
        Some(RematCost::CheaperThanMove) => REMAT_CHEAPER_THAN_MOVE_SCALE,
        Some(RematCost::CheaperThanReload) => REMAT_CHEAPER_THAN_RELOAD_SCALE,
    }
}

/// Like `use_spill_cost`, but scaled by block frequency.
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

    let weight = cost * frequency;
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

    /// The hints attached to this span's start, and to its end.
    ///
    /// A cross-region affinity is about one edge, so it wants a register only
    /// where the span meets that edge. Splitting would otherwise give a hint
    /// about the entry to the half covering the exit, where it competes with
    /// that half's own hint.
    preference_at_start: RegPreference,
    preference_at_end: RegPreference,
}

/// Which end of a span a hint is about.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum HintPos {
    Start,
    End,
}

impl<E> LiveSpanData<E>
where
    E: EntityRepr,
{
    /// Create a span covering `[start, end)` for `val`, with the given uses.
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
            preference_at_start: RegPreference::new(),
            preference_at_end: RegPreference::new(),
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

    /// The registers this bundle would prefer, within `self.constraint`.
    preference: RegPreference,

    /// The registers this bundle is currently allocated to.
    reg_allocation: Option<RegAllocation<E>>,

    /// Is this bundle recomputed wherever it is next wanted, rather than held
    /// anywhere at all?
    rematerialized: bool,

    /// Packed weight and flags.
    ///
    /// Keeping the flags *above* the weight is what makes a minimal bundle sort
    /// above every ordinary one under a plain integer comparison of
    /// `weight_and_flags`, rather than under a rule that every comparison site
    /// has to remember to apply.
    ///
    /// Bit:     31           30     ...     0
    ///        +------------+------------------+
    /// Field: | minimal: 1 | spill_weight: 31 |
    ///        +------------+------------------+
    weight_and_flags: u32,
}

const BUNDLE_SPILL_WEIGHT_BITS: u32 = 31;
const BUNDLE_SPILL_WEIGHT_MASK: u32 = PackedPositiveFloat::<u32, BUNDLE_SPILL_WEIGHT_BITS>::MASK;
const BUNDLE_MINIMAL: u32 = 1 << 31;

/// The registers hints have asked for, kept two ways.
///
/// `intersection` holds the registers satisfying every hint, and empties as
/// soon as two disagree, which is common once hints name single registers.
/// `union` is the fallback: satisfying one hint still elides one move.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RegPreference {
    intersection: RegSet,
    union: RegSet,
}

impl RegPreference {
    /// A preference nothing has hinted yet.
    pub(crate) fn new() -> Self {
        RegPreference {
            intersection: RegSet::new(),
            union: RegSet::new(),
        }
    }

    /// Fold `hint` in.
    pub(crate) fn add_hint(&mut self, hint: RegSet) {
        debug_assert!(!hint.is_empty());

        self.union.union_with(&hint);

        if self.intersection.is_empty() {
            // Take the first hint whole rather than intersect an empty set.
            self.intersection = hint;
            return;
        }

        let narrowed = self.intersection.intersection(&hint);

        // Keep the existing hint over an equally arbitrary alternative.
        if !narrowed.is_empty() {
            self.intersection = narrowed;
        }
    }

    /// Does every hint accept `reg`?
    pub(crate) fn intersection_contains(&self, reg: Reg) -> bool {
        self.intersection.contains(reg)
    }

    /// Did any hint ask for `reg`?
    pub(crate) fn union_contains(&self, reg: Reg) -> bool {
        self.union.contains(reg)
    }

    /// The registers satisfying every hint.
    pub(crate) fn intersection(&self) -> &RegSet {
        &self.intersection
    }

    /// Every register some hint asked for.
    pub(crate) fn union(&self) -> &RegSet {
        &self.union
    }

    /// Has anything hinted this at all?
    pub(crate) fn is_empty(&self) -> bool {
        self.union.is_empty()
    }
}

impl<E> LiveBundleData<E>
where
    E: EntityRepr,
{
    /// Fold `hint` into this bundle's preference.
    fn add_hint(&mut self, hint: RegSet) {
        self.preference.add_hint(hint);
    }
}

/// A register held across part of one instruction, either for the fixed
/// operands that name it for one value or because the instruction clobbers it.
///
/// A fixed operand, one whose resolved constraint names a class holding a
/// single register or register group, is not choosing among registers but
/// naming one. Rather than constrain the value's bundle to that class and make
/// it compete through the ordinary assign-evict-split ladder, the register is
/// held outright across the instruction and the value is move-connected and
/// hinted to it.
///
/// A reservation is unevictable, never a queue participant, and constrains
/// nothing, but it is porous to its own `val`, reads and definitions alike.
/// regalloc3 can make a definition a hard wall because it *excises* the fixed
/// half-instruction from the value's live range; regicide has no point to
/// excise to, so the value's own span covers its own reservation and a hard
/// wall would forbid the very assignment the hint asks for.
///
/// A clobber has no `val`, which makes it porous to nothing and so a hard wall
/// to every bundle. It also needs no move and biases no preference.
pub(crate) struct ReservationData<E>
where
    E: EntityRepr,
{
    /// The sole member of the operands' singleton class.
    reg: RegAllocation<E>,

    /// Where the reservation begins, inclusive.
    start: LivePoint<E>,

    /// Where it ends, exclusive.
    end: LivePoint<E>,

    /// The value delivered into, or produced out of, `reg`. `None` for a
    /// clobber.
    val: Option<Val<E>>,

    /// Whether some operand reads `val` out of `reg`, and so needs the move
    /// delivering it there.
    uses: bool,

    /// Whether some operand writes `val` into `reg`, and so needs the move
    /// carrying it back out.
    defs: bool,
}

impl<E> Reservation<E>
where
    E: EntityRepr,
{
    /// The register, or register group, this reservation holds.
    pub(crate) fn reg(self, live_ranges: &LiveRanges<E>) -> RegAllocation<E> {
        live_ranges.reservations[self].reg
    }

    /// Where this reservation begins.
    pub(crate) fn start(self, live_ranges: &LiveRanges<E>) -> LivePoint<E> {
        live_ranges.reservations[self].start
    }

    /// Where this reservation ends, exclusive.
    pub(crate) fn end(self, live_ranges: &LiveRanges<E>) -> LivePoint<E> {
        live_ranges.reservations[self].end
    }

    /// The value delivered into, or produced out of, the reserved register, or
    /// `None` for a clobber.
    pub(crate) fn val(self, live_ranges: &LiveRanges<E>) -> Option<Val<E>> {
        live_ranges.reservations[self].val
    }

    /// Whether some operand reads the value out of the reserved register.
    ///
    /// See `ReservationData::uses`.
    pub(crate) fn uses(self, live_ranges: &LiveRanges<E>) -> bool {
        live_ranges.reservations[self].uses
    }

    /// Whether some operand writes the value into the reserved register.
    ///
    /// See `ReservationData::defs`.
    pub(crate) fn defs(self, live_ranges: &LiveRanges<E>) -> bool {
        live_ranges.reservations[self].defs
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

    /// The registers held for the input function's fixed operands.
    ///
    /// Grouped by block, and in program order within a block, so that
    /// `block_reservations` can name each block's run as a range.
    reservations: PrimaryMap<Reservation<E>, ReservationData<E>>,

    /// Map from a block to the reservations within it.
    ///
    /// A reservation belongs to the instruction that asked for it, so this
    /// partitions `reservations` exactly once. Region allocation leans on
    /// that: a region's reservations are the union of its blocks' and belong
    /// to that region alone.
    block_reservations: SecondaryMap<Block<E>, EntityRange<Reservation<E>>>,

    /// Map from a region to the bundles that coalescing created for it.
    ///
    /// Does not include bundles created after coalescing, e.g. by splitting
    /// during region allocation.
    region_bundles: SecondaryMap<Region<E>, EntityRange<LiveBundle<E>>>,
}

/// Sort `spans` by value, then start, then end, so that each value's spans are
/// contiguous and in program order.
///
/// The span itself breaks ties between spans of one value over one range, so
/// the order is total. `keyed` is scratch, left empty.
pub(crate) fn sort_spans<E>(
    live_ranges: &LiveRanges<E>,
    spans: &mut alloc::vec::Vec<LiveSpan<E>>,
    keyed: &mut alloc::vec::Vec<(u128, LiveSpan<E>)>,
) where
    E: EntityRepr,
{
    debug_assert!(keyed.is_empty());
    keyed.extend(spans.iter().map(|&span| (span.sort_key(live_ranges), span)));

    // Bucketing by value first hands the comparison sort many short runs
    // instead of one long one, which only pays on a long list.
    if keyed.len() >= RADIX_SORT_SPANS_MIN {
        sort_keyed_by_val(keyed);
    } else {
        keyed.sort_unstable_by_key(|&(key, _)| key);
    }

    spans.clear();
    spans.extend(keyed.drain(..).map(|(_, span)| span));
}

/// How many spans make `sort_spans`'s bucketing pass worth its extra scan.
const RADIX_SORT_SPANS_MIN: usize = 64;

/// Sort `keyed` by key, bucketing on the value index the key's top bits hold.
fn sort_keyed_by_val<E>(keyed: &mut alloc::vec::Vec<(u128, LiveSpan<E>)>)
where
    E: EntityRepr,
{
    // Size the histogram by the values present, not by what `Val` can index.
    let val_of = |key: u128| (key >> 96) as usize;
    let (lo, hi) = keyed.iter().fold((usize::MAX, 0), |(lo, hi), &(key, _)| {
        (lo.min(val_of(key)), hi.max(val_of(key)))
    });
    let width = hi - lo + 1;

    // A histogram wider than the input is not worth filling.
    if width > keyed.len() {
        keyed.sort_unstable_by_key(|&(key, _)| key);
        return;
    }

    let mut starts = alloc::vec![0usize; width + 1];
    for &(key, _) in keyed.iter() {
        starts[val_of(key) - lo + 1] += 1;
    }
    for i in 1..starts.len() {
        starts[i] += starts[i - 1];
    }

    let mut out = alloc::vec::Vec::with_capacity(keyed.len());
    out.resize(keyed.len(), keyed[0]);
    let mut at = starts.clone();
    for &entry in keyed.iter() {
        let b = val_of(entry.0) - lo;
        out[at[b]] = entry;
        at[b] += 1;
    }

    // Each bucket is one value's spans, still unordered among themselves.
    for w in starts.windows(2) {
        out[w[0]..w[1]].sort_unstable_by_key(|&(key, _)| key);
    }

    keyed.clear();
    keyed.extend_from_slice(&out);
    debug_assert!(keyed.windows(2).all(|w| w[0].0 < w[1].0));
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
            reservations: PrimaryMap::new(),
            block_reservations: SecondaryMap::new(EntityRange::empty()),
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
            reservations,
            block_reservations,
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
        reservations.reset();
        block_reservations.reset();
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
            reservations,
            block_reservations,
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
            && reservations.is_reset()
            && block_reservations.is_reset()
            && use_span.is_reset()
            && region_bundles.is_reset()
    }

    /// Iterate over every reservation in the function, in program order.
    #[allow(dead_code, reason = "read by the tests")]
    pub fn reservations(&self) -> impl Iterator<Item = Reservation<E>> + '_ {
        self.reservations.keys()
    }

    /// How many live spans have been constructed?
    #[allow(dead_code, reason = "will probably need it")]
    pub fn len_spans(&self) -> usize {
        self.spans.len()
    }

    /// Iterate over every live span that has been constructed.
    pub fn spans(&self) -> impl ExactSizeIterator<Item = LiveSpan<E>> + '_ {
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

        // Construct a span for each value live in or across this block.
        for (block, input_block) in input.func.blocks() {
            let first_inst = output.with_repr(block_first_inst(&input_block))?;
            let last_inst = output.with_repr(block_last_inst(&input_block))?;
            let block_start = LivePoint::new(first_inst, Position::Early);
            let block_end = LivePoint::new(last_inst, Position::Late).next_point();

            let block = output.with_repr(block)?;
            let spans_start = self.spans.next_key(output)?;
            let uses_start = self.uses.next_key(output)?;

            // Collected before the spans, so that nothing below has to thread
            // reservations through the per-value walk.
            let reservations_start = self.reservations.next_key(output)?;
            collect_block_reservations(input, &mut self.reservations, &input_block, output)?;
            self.block_reservations[block] = EntityRange {
                start: reservations_start,
                end: self.reservations.next_key(output)?,
            };

            #[cfg(feature = "visualizer")]
            let events_start = events.len();

            for span in liveness.block_spans(input.func, block, &mut self.uses, output)? {
                push_span_and_split_conflicts(
                    input,
                    &self.uses,
                    &mut self.spans,
                    counts,
                    events,
                    span,
                    block,
                    block_end,
                    output,
                )?;
            }
            let uses_end = self.uses.next_key(output)?;
            let spans_end = self.spans.next_key(output)?;

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
                self.spans.as_slice()[block_span_range.clone()]
                    .iter()
                    .map(sort_key),
            );

            self.spans.as_mut_slice()[block_span_range.clone()].sort_unstable_by_key(sort_key);

            #[cfg(feature = "visualizer")]
            remap_block_span_events(
                events,
                events_start,
                spans_start,
                &keys_before,
                &alloc::vec::Vec::from_iter(
                    self.spans.as_slice()[block_span_range].iter().map(sort_key),
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
                let val = self.spans[span].val;
                for u in self.spans[span].uses {
                    self.use_span[u] = span;
                    self.uses[u].weight = use_spill_weight(input, &self.uses, frequency, val, u);
                }

                let next = LiveSpan::try_new(span.index() + 1).unwrap();
                if self.spans[span].start == block_start {
                    live_in_end = next;
                }
                if self.spans[span].end == block_end {
                    live_out_start.get_or_insert(span);
                    live_out_end = next;
                }
            }

            self.block_spans[block] = EntityRange {
                start: spans_start,
                end: spans_end,
            };

            self.block_uses[block] = EntityRange {
                start: uses_start,
                end: uses_end,
            };
            debug_assert!(
                self.block_uses[block]
                    .into_iter()
                    .all(|u| self.use_span[u] != LiveSpan::default())
            );

            self.live_in_spans[block] = EntityRange {
                start: spans_start,
                end: live_in_end,
            };
            debug_assert!(
                self.live_in_spans[block]
                    .into_iter()
                    .all(|s| self.spans[s].start == block_start)
            );
            debug_assert_eq!(
                self.live_in_spans[block].into_iter().count(),
                self.block_spans[block]
                    .into_iter()
                    .filter(|&s| self.spans[s].start == block_start)
                    .count(),
            );

            self.live_out_spans[block] = match live_out_start {
                Some(start) => EntityRange {
                    start,
                    end: live_out_end,
                },
                None => EntityRange::empty(),
            };
            debug_assert!(
                self.live_out_spans[block]
                    .into_iter()
                    .all(|s| self.spans[s].end == block_end)
            );
            debug_assert_eq!(
                self.live_out_spans[block].into_iter().count(),
                self.block_spans[block]
                    .into_iter()
                    .filter(|&s| self.spans[s].end == block_end)
                    .count(),
            );
        }

        counts.live_spans += self.spans.len();
        counts.uses += self.uses.len();
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
    /// Resolving the operand's constraint needs its siblings, hence the
    /// function rather than anything cached. Resolved exactly as reservation
    /// collection does, so the two agree on which operands are fixed.
    pub(crate) fn is_fixed(
        self,
        live_ranges: &LiveRanges<E>,
        func: &impl InputFunction,
        machine: &Machine,
    ) -> bool {
        fixed_operand_of(
            func,
            machine,
            self.point(live_ranges).inst().with_repr32(),
            self.operand(live_ranges),
        )
        .is_some()
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

    /// `(val, start, end, self)` packed into one integer, ordered the same way,
    /// so that sorting spans by it compares integers rather than reading each
    /// span's data on every comparison. See `sort_spans`.
    #[inline]
    fn sort_key(self, live_ranges: &LiveRanges<E>) -> u128 {
        let data = &live_ranges.spans[self];
        (data.val.index() as u128) << 96
            | (data.start.to_bits() as u128) << 64
            | (data.end.to_bits() as u128) << 32
            | self.index() as u128
    }

    /// The hints attached to one end of this span.
    #[inline]
    pub(crate) fn preference_at(self, live_ranges: &LiveRanges<E>, pos: HintPos) -> &RegPreference {
        let data = &live_ranges.spans[self];
        match pos {
            HintPos::Start => &data.preference_at_start,
            HintPos::End => &data.preference_at_end,
        }
    }

    /// Record that `hint` is wanted at one end of this span.
    #[inline]
    pub(crate) fn add_hint_at(self, live_ranges: &mut LiveRanges<E>, pos: HintPos, hint: RegSet) {
        let data = &mut live_ranges.spans[self];
        match pos {
            HintPos::Start => data.preference_at_start.add_hint(hint),
            HintPos::End => data.preference_at_end.add_hint(hint),
        }
    }

    /// The block this span lies within; spans never cross a block boundary.
    pub(crate) fn block(self, func: &impl InputFunction, live_ranges: &LiveRanges<E>) -> Block<E> {
        func.inst(self.start(live_ranges).inst().with_repr32())
            .block()
            .with_repr::<E>()
            .expect("every block index already fit in `E` in the earlier passes")
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
            let use_constraint = reservation_aware_constraint(
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

        // Adopt what this bundle's own spans ask for at the ends they cover.
        // A split hands each half only its own ends, so a piece never inherits
        // a hint about an edge the other half kept.
        let mut preference = RegPreference::new();
        for index in spans {
            let span = live_ranges.bundle_spans_storage[index];
            debug_assert!(live_ranges.span_bundle[span].is_none());
            live_ranges.span_bundle[span] = Some(bundle);

            for end in [HintPos::Start, HintPos::End] {
                let hinted = *span.preference_at(live_ranges, end).union();
                if !hinted.is_empty() {
                    preference.add_hint(hinted);
                }
            }
        }

        let pushed = live_ranges.bundles.push(
            output,
            LiveBundleData {
                spans,
                region,
                constraint,
                preference,
                reg_allocation: None,
                rematerialized: false,
                weight_and_flags: 0,
            },
        )?;
        debug_assert_eq!(pushed, bundle);

        bundle.recompute_weight_and_flags(live_ranges, input);
        Ok(bundle)
    }

    /// Recompute the cached `is_minimal` flag and spill weight from the spans
    /// this bundle currently holds.
    fn recompute_weight_and_flags(
        self,
        live_ranges: &mut LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
    ) {
        let mut total_use_cost = 0.0;
        let mut discounted_use_cost = 0.0;
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
            let uses = span.uses(live_ranges);
            len_uses += uses.len();
            let span_use_cost = uses
                .into_iter()
                .map(|u| u.weight(live_ranges).as_f32())
                .sum::<f32>();
            total_use_cost += span_use_cost;
            let val = span.val(live_ranges);
            discounted_use_cost +=
                span_use_cost * remat_scale(input.func.value(val.with_repr32()).remat_cost());
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

        // A minimal bundle can't punt by splitting uses off into remats, so it
        // pays the full price.
        let is_minimal = is_minimal_bundle(len_cuttable_gaps, len_uses, len_insts);
        let use_cost = if is_minimal {
            total_use_cost
        } else {
            discounted_use_cost
        };

        let mut weight_and_flags = PackedPositiveFloat::<u32, BUNDLE_SPILL_WEIGHT_BITS>::new(
            normalize_spill_weight(use_cost, sum_len_insts),
        )
        .bits();
        debug_assert_eq!(weight_and_flags & !BUNDLE_SPILL_WEIGHT_MASK, 0);
        if is_minimal {
            weight_and_flags |= BUNDLE_MINIMAL;
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
            cfg!(any(
                debug_assertions,
                feature = "trace-log",
                feature = "visualizer"
            )),
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
            preference_at_start,
            preference_at_end,
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

        // Rewrite the divided span in place as the first piece; because we are
        // rewriting this span in place, its uses are already associated with it
        // and its `span_bundle` entry remains valid.
        // Each half keeps only the hints about the end it still covers; the
        // cut itself is hinted by neither.
        let mut lo = LiveSpanData::new(start, at, val, lo_uses);
        lo.preference_at_start = preference_at_start;
        live_ranges.spans[old] = lo;

        // The new span takes second piece.
        let mut hi = LiveSpanData::new(at, end, val, hi_uses);
        hi.preference_at_end = preference_at_end;
        let new_span = live_ranges.spans.push(output, hi)?;

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

    /// Move this bundle's early reads onto their own half-instruction bundle,
    /// leaving it a use-less carrier for the caller to spill.
    ///
    /// ```text
    ///                    inst:Early       inst:Late      (inst+1):Early
    ///                        |                |                |
    /// reload (returned):     [reads===========)
    /// carrier (self):        [=================================)
    /// ```
    ///
    /// It is the whole-instruction footprint that cannot be satisfied, not the
    /// half the reads are in, so the carry goes to the stack and the reads keep
    /// a register.
    pub(crate) fn narrow_to_early_half(
        self,
        live_ranges: &mut LiveRanges<E>,
        input: &Input<'_, impl InputFunction>,
        events: &mut EventsLog<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<LiveBundle<E>> {
        debug_assert!(live_ranges.bundles[self].reg_allocation.is_none());

        let span = {
            let mut spans = self.spans(live_ranges);
            let span = spans
                .next()
                .expect("a bundle always holds at least one span");
            debug_assert_eq!(spans.next(), None, "only a single-span bundle narrows");
            span
        };

        let LiveSpanData {
            start,
            end,
            uses,
            val,
            preference_at_start,
            preference_at_end,
        } = live_ranges.spans[span];

        debug_assert_eq!(start.pos(), Position::Early);
        debug_assert_eq!(span.len_insts(live_ranges), 1);
        debug_assert!(!uses.is_empty());
        debug_assert!(
            uses.into_iter().all(|u| u.point(live_ranges) == start
                && input
                    .func
                    .inst(start.inst().with_repr32())
                    .operand(u.operand(live_ranges))
                    .kind()
                    == DefUse::Use),
            "every operand must be a read at {start:?}",
        );

        // The mid-instruction point, not `inst_boundary_after`: that wider
        // footprint is what is being shed.
        let reload_end = start.next_point();
        debug_assert_eq!(reload_end.pos(), Position::Late);
        debug_assert!(reload_end < end, "the span must be wider than to narrow to");

        let block = span.block(input.func, live_ranges);
        let constraint = span.constraint(live_ranges, input);

        let reload = push_span(
            &mut live_ranges.spans,
            output,
            events,
            val,
            (start, reload_end),
            (uses.start, uses.end),
            constraint,
            block,
        )?;
        // The reload covers the early reads, so the start's hints go with it.
        live_ranges.spans[reload].preference_at_start = preference_at_start;
        live_ranges.spans[span].preference_at_start = RegPreference::new();
        let _ = preference_at_end;
        live_ranges.spans[span].uses = EntityRange {
            start: uses.start,
            end: uses.start,
        };
        for u in uses {
            live_ranges.use_span[u] = reload;
        }

        // Now use-less, so its constraint drops to `Any`, which is what lets
        // the caller spill it.
        self.recompute_weight_and_flags(live_ranges, input);
        self.recompute_constraint(live_ranges, input);
        debug_assert_eq!(self.constraint(live_ranges), OperandConstraint::Any);

        let reload = live_ranges.push_bundle(
            input,
            output,
            self.region(live_ranges),
            constraint,
            core::iter::once(reload),
        )?;

        event!(
            events,
            BundleNarrowedToEarlyHalf {
                bundle: self,
                reload,
                at: reload_end,
            }
        );

        Ok(reload)
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
    pub(crate) fn preference(self, live_ranges: &LiveRanges<E>) -> &RegPreference {
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

    /// Is this bundle recomputed where next wanted, rather than held anywhere?
    #[inline]
    pub(crate) fn is_rematerialized(self, live_ranges: &LiveRanges<E>) -> bool {
        live_ranges.bundles[self].rematerialized
    }

    /// Record that nothing holds this bundle's value over its range.
    #[inline]
    pub(crate) fn set_rematerialized(self, live_ranges: &mut LiveRanges<E>) {
        debug_assert!(live_ranges.bundles[self].reg_allocation.is_none());
        live_ranges.bundles[self].rematerialized = true;
    }

    /// Is this bundle minimal, i.e. too small to be split any further?
    #[inline]
    pub(crate) fn is_minimal(self, live_ranges: &LiveRanges<E>) -> bool {
        live_ranges.bundles[self].weight_and_flags & BUNDLE_MINIMAL != 0
    }

    /// How expensive it would be to spill this bundle.
    #[inline]
    pub(crate) fn spill_weight(self, live_ranges: &LiveRanges<E>) -> f32 {
        PackedPositiveFloat::<u32, BUNDLE_SPILL_WEIGHT_BITS>::from_bits(
            live_ranges.bundles[self].weight_and_flags & BUNDLE_SPILL_WEIGHT_MASK,
        )
        .as_f32()
    }

    /// How much the blocks of this bundle's hinted spans weigh, all together:
    /// what honoring the hints saves, since each saves a move in its own block.
    ///
    /// Blocks in one region share its loop depth, so within a region this is
    /// the hinted-span count times one weight, unless the embedder varies
    /// frequency within a region. Bundles in different regions are never
    /// compared, so this cannot rank a deep hint above a shallow one.
    pub(crate) fn hinted_span_weight(
        self,
        input: &Input<'_, impl InputFunction>,
        region_tree: &RegionTree<E>,
        live_ranges: &LiveRanges<E>,
        unusable: &RegSet,
    ) -> f64 {
        self.hinted_spans(live_ranges, unusable)
            .map(|span| {
                span.block(input.func, live_ranges)
                    .weight(input, region_tree)
            })
            .sum()
    }

    /// This bundle's spans that carry a hint, at either end, towards some
    /// register outside `unusable`.
    fn hinted_spans<'a>(
        self,
        live_ranges: &'a LiveRanges<E>,
        unusable: &'a RegSet,
    ) -> impl Iterator<Item = LiveSpan<E>> + 'a {
        self.spans(live_ranges).filter(move |span| {
            [HintPos::Start, HintPos::End].iter().any(|&end| {
                !span
                    .preference_at(live_ranges, end)
                    .union()
                    .is_subset_of(unusable)
            })
        })
    }

    /// Bias this bundle towards the registers that `constraint` names, on
    /// behalf of `from`.
    ///
    /// Hinting a whole class is still the right shape for a hint whose source
    /// does not name one register.
    #[allow(dead_code, reason = "cross-region hinting names a register instead")]
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
        live_ranges.bundles[self].add_hint(*regs);
        event!(
            events,
            BundleHint {
                bundle: self,
                hint: *regs,
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

    /// How often the embedder estimates this block runs.
    pub(crate) fn frequency(self, func: &impl InputFunction) -> BlockFrequency {
        func.block(self.with_repr32()).frequency()
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

    /// Get the registers held for this block's fixed operands.
    pub(crate) fn reservations(self, live_ranges: &LiveRanges<E>) -> EntityRange<Reservation<E>> {
        live_ranges.block_reservations[self]
    }

    /// A subrange of this block's reservations that holds every one
    /// overlapping `range`, and possibly others that do not.
    #[inline]
    pub(crate) fn reservations_near(
        self,
        live_ranges: &LiveRanges<E>,
        range: core::ops::Range<LivePoint<E>>,
    ) -> EntityRange<Reservation<E>> {
        // Scanning a short run is cheaper than searching it.
        let all = self.reservations(live_ranges);
        if all.len() <= 32 {
            return all;
        }
        search_reservations(live_ranges, all, range)
    }
}

/// See `Block::reservations_near`.
#[inline(never)]
fn search_reservations<E>(
    live_ranges: &LiveRanges<E>,
    all: EntityRange<Reservation<E>>,
    range: core::ops::Range<LivePoint<E>>,
) -> EntityRange<Reservation<E>>
where
    E: EntityRepr,
{
    let indices = all.indices();
    let sorted = &live_ranges.reservations.as_slice()[indices.clone()];

    // A reservation starts and ends within its instruction and the gap after
    // it, so instruction order is enough to bound the overlapping ones: those
    // of earlier instructions end by `range.start`'s.
    let inst_of = |r: &ReservationData<E>| r.start.inst_boundary_at_or_before();
    let first_inst = range.start.inst_boundary_at_or_before();
    let first = sorted.partition_point(|r| inst_of(r) < first_inst);
    let last = first + sorted[first..].partition_point(|r| inst_of(r) < range.end);
    debug_assert!(
        sorted[..first]
            .iter()
            .chain(&sorted[last..])
            .all(|r| !LivePoint::spans_overlap(range.start, range.end, r.start, r.end))
    );

    EntityRange {
        start: Reservation::new_unchecked(indices.start + first),
        end: Reservation::new_unchecked(indices.start + last),
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

impl<E> Val<E>
where
    E: EntityRepr,
{
    /// Does `block` pass this value as an argument to any of its successors?
    pub(crate) fn is_passed_to_a_successor(
        self,
        func: &impl InputFunction,
        block: Block<E>,
    ) -> bool {
        let input_block = func.block(block.with_repr32());
        let val = self.with_repr32();
        (0..input_block.len_successors())
            .any(|i| input_block.successor_block_args(i).any(|arg| arg == val))
    }
}

/// The same register, or register group, in this allocation's entity
/// representation.
fn with_repr_reg_allocation<E>(
    reg: RegAllocation,
    output: &mut OutputInner<E>,
) -> IResult<RegAllocation<E>>
where
    E: EntityRepr,
{
    Ok(match reg {
        RegAllocation::Reg(reg) => RegAllocation::Reg(output.with_repr(reg)?),
        RegAllocation::RegGroup(group) => RegAllocation::RegGroup(group),
    })
}

/// What a fixed operand asks for: one particular register, for one particular
/// value, over one particular range of program points.
///
/// The allocator makes good on it by holding that register over `held_range`
/// rather than by constraining the operand's value (see `ReservationData`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FixedOperand {
    /// The single register, or register group, the operand names.
    pub reg: RegAllocation,

    /// The value it reads out of, or writes into, `reg`.
    pub val: Val,

    /// Whether the operand reads `reg` or defines it.
    pub kind: DefUse,

    /// The half-instruction the operand itself occupies.
    pub pos: Position,
}

/// The program points a reservation holds its register over, for an operand of
/// `kind` in the `pos` half of `inst`.
///
/// A read reaches back over the gap before the instruction, where the move
/// delivering it lives; a definition reaches forward over the gap after. So an
/// early read and a late definition of one register want disjoint halves of
/// it, the shape report 000 could not allocate. A clobber is a definition of
/// nothing, and takes the definition's range.
pub(crate) fn held_range<E>(
    kind: DefUse,
    pos: Position,
    inst: Inst<E>,
) -> core::ops::Range<LivePoint<E>>
where
    E: EntityRepr,
{
    let point = LivePoint::new(inst, pos);
    if kind.is_use() {
        point.inst_boundary_at_or_before()..point.next_point()
    } else {
        point..point.inst_boundary_after()
    }
}

impl FixedOperand {
    /// The program points a reservation for this operand holds its register
    /// over. See the free `held_range`.
    pub(crate) fn held_range<E>(&self, inst: Inst<E>) -> core::ops::Range<LivePoint<E>>
    where
        E: EntityRepr,
    {
        held_range(self.kind, self.pos, inst)
    }

    /// Does the hold cover `pos` of `inst`, the operand's own instruction?
    ///
    /// Derived from `held_range` rather than restated, so that
    /// `validation::check_inst_fixed_operands` rejects exactly the overlaps
    /// `collect_block_reservations` could not hold registers for.
    pub(crate) fn holds<E>(&self, inst: Inst<E>, pos: Position) -> bool
    where
        E: EntityRepr,
    {
        let range = self.held_range(inst);
        let point = LivePoint::new(inst, pos);
        range.start <= point && point < range.end
    }
}

/// What `operand` of `inst` names, when it is a fixed operand, and `None` when
/// it is not.
///
/// This is the one definition of "is this operand fixed", consulted by
/// `collect_block_reservations`, `reservation_aware_constraint`,
/// `validation::check_inst_fixed_operands`,
/// `OutputInner::reserve_block_inst_allocs` and `Use::is_fixed`. None of the
/// ways they can disagree fails loudly: relaxing without reserving leaves the
/// register unprotected, reserving without relaxing pins the value into a
/// singleton class again, and reporting without reserving shows the checker a
/// register nobody held.
///
/// An operand naming no value names a register the allocator does not own
/// (`check_block_reg_classes`), which covers no register unit and so never
/// appears in the matrix.
///
/// The constraint is resolved first, because a `Reuse` of a fixed target is
/// itself fixed and gets its own reservation on the same register, satisfying
/// the tie by construction.
pub(crate) fn fixed_operand_of(
    func: &impl InputFunction,
    machine: &Machine,
    inst: Inst,
    operand: usize,
) -> Option<FixedOperand> {
    let input_inst = func.inst(inst);
    let operand_ref = input_inst.operand(operand);

    let OperandConstraint::Reg(class) = reuse_aware_constraint(func, machine, inst, operand) else {
        return None;
    };

    let reg = class.fixed_reg(machine)?;
    let val = operand_ref.val()?;

    Some(FixedOperand {
        reg,
        val,
        kind: operand_ref.kind(),
        pos: operand_ref.pos(),
    })
}

/// Record a reservation for each fixed operand of each of `block`'s
/// instructions.
///
/// Instructions are walked in program order and hold their registers no
/// further than the gap after them, so the reservations come out in
/// non-decreasing order of their instruction. Within one instruction they are
/// not sorted by start point: a late operand may precede an early one. See
/// `ReservationData` for why a fixed operand gets one instead of a constraint.
fn collect_block_reservations<'a, E>(
    input: &Input<'_, impl InputFunction>,
    reservations: &mut PrimaryMap<Reservation<E>, ReservationData<E>>,
    input_block: &impl InputBlock<'a>,
    output: &mut OutputInner<E>,
) -> IResult<()>
where
    E: EntityRepr,
{
    let block_start = reservations.len();
    for (inst, input_inst) in input_block.insts() {
        let repr32_inst = inst;
        let inst = output.with_repr(inst)?;

        // The whole search space for the merge below: only operands of one
        // instruction can name one register for one value at one time.
        let inst_start = reservations.len();

        for i in 0..input_inst.operands_len() {
            let Some(fixed) = fixed_operand_of(input.func, input.machine, repr32_inst, i) else {
                continue;
            };

            let reg = with_repr_reg_allocation(fixed.reg, output)?;
            let val = output.with_repr(fixed.val)?;
            let core::ops::Range { start, end } = fixed.held_range(inst);

            // Naming one register for one value twice asks no more than
            // naming it once, so hold it over the union of what the operands
            // ask for. That has to be one reservation and not two, since
            // reservations on a register may not overlap; anything else
            // claiming it here is a conflict `check_inst_fixed_operands` has
            // already rejected.
            if let Some(held) = reservations.as_mut_slice()[inst_start..]
                .iter_mut()
                .find(|r| r.reg == reg && r.val == Some(val))
            {
                held.start = held.start.min(start);
                held.end = held.end.max(end);
                held.uses |= fixed.kind.is_use();
                held.defs |= fixed.kind.is_def();
                continue;
            }

            reservations.push(
                output,
                ReservationData {
                    reg,
                    start,
                    end,
                    val: Some(val),
                    uses: fixed.kind.is_use(),
                    defs: fixed.kind.is_def(),
                },
            )?;
        }

        // A val-less reservation for each register the instruction destroys,
        // over the late half a definition of it would have held. These belong
        // to this instruction too, so the run stays in instruction order.
        let core::ops::Range { start, end } = held_range(DefUse::Def, Position::Late, inst);
        for reg in input_inst.clobbers().iter() {
            // `is_non_allocatable` indexes the machine's registers, and
            // `validation`, which reports this properly, is off by default in
            // release.
            debug_assert!(
                reg.index() < input.machine.num_registers(),
                "`InputInst::clobbers` named a register this machine does not define",
            );

            // A register the allocator does not own holds nothing to destroy.
            if reg.is_non_allocatable(input.machine) {
                continue;
            }

            let reg = RegAllocation::Reg(output.with_repr(reg)?);

            // Reservations on a register may not overlap, and two clobbers of
            // one register agree, so fold them together. A fixed operand is
            // left alone: only an early read can name this register, and it
            // holds the other half.
            if reservations.as_mut_slice()[inst_start..]
                .iter()
                .any(|r| r.reg == reg && r.val.is_none())
            {
                continue;
            }

            reservations.push(
                output,
                ReservationData {
                    reg,
                    start,
                    end,
                    val: None,
                    uses: false,
                    defs: false,
                },
            )?;
        }
    }

    // `Block::reservations_near` searches on this order.
    debug_assert!(
        reservations.as_slice()[block_start..]
            .is_sorted_by_key(|r| r.start.inst_boundary_at_or_before())
    );
    Ok(())
}

/// Get the constraint that an instruction's `operand` places on its span.
///
/// Resolves a `Reuse` to its target's constraint, narrows both halves of a tie
/// by the same sibling reads, and then strengthens both to demand a register:
/// a stack home belongs to one value alone and so cannot be reused for two
/// different values.
pub(crate) fn reuse_aware_constraint(
    func: &impl InputFunction,
    machine: &Machine,
    inst: Inst,
    operand: usize,
) -> OperandConstraint {
    let input_inst = func.inst(inst);
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
    //
    // A sibling naming one particular register is not such a sibling: its
    // value is delivered into the reserved register rather than read out of
    // the tie's location, so it says nothing about where that location is.
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
            if other.is_fixed_reg(machine) {
                continue;
            }
            resolved = match resolved {
                OperandConstraint::Any => OperandConstraint::Reg(other),
                OperandConstraint::Reg(rc) => rc
                    .intersect(machine, other)
                    .map_or(resolved, OperandConstraint::Reg),
                resolved => resolved,
            };
        }
    }

    let is_tied = tie_target.is_some();
    match resolved {
        OperandConstraint::Any if is_tied => {
            let val = input_inst.operand(operand).val().unwrap();
            OperandConstraint::Reg(func.value(val).reg_class())
        }
        resolved => resolved,
    }
}

/// Get the constraint that an instruction's `operand` places on the span its
/// value lands in.
///
/// This is `reuse_aware_constraint`, minus the fixed operands: an operand that
/// names one particular register constrains its value not at all, since the
/// register is held for it by a reservation (see `ReservationData`).
///
/// That freedom is the entire point. A constraint naming a single register
/// leaves its bundle exactly one place to go, with no second candidate, no
/// narrower piece to split off and no stack slot to fall back on. Two values
/// each pinned to the other's register across one instruction cannot both be
/// satisfied at all where a value has one location at a time, which is what
/// `reports/000-early-use-late-def-both-in-fixed-reg.md` and
/// `reports/001-eviction-and-fixed-reg.md` are about.
fn reservation_aware_constraint(
    input: &Input<'_, impl InputFunction>,
    inst: Inst,
    operand: usize,
) -> OperandConstraint {
    // `fixed_operand_of`, without computing the constraint twice.
    let constraint = reuse_aware_constraint(input.func, input.machine, inst, operand);
    if let OperandConstraint::Reg(class) = constraint
        && class.fixed_reg(input.machine).is_some()
        && input.func.inst(inst).operand(operand).val().is_some()
    {
        return OperandConstraint::Any;
    }
    constraint
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
            crate::events::Event::OverwriteSplit { before, copy, .. } => {
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
    block: Block<E>,
) -> IResult<LiveSpan<E>>
where
    E: EntityRepr,
{
    let uses = EntityRange {
        start: uses_start,
        end: uses_end,
    };
    let span = spans.push(output, LiveSpanData::new(start, end, val, uses))?;
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
        let constraint = reservation_aware_constraint(input, point.inst().with_repr32(), operand);
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
            is_read,
        }
    }

    /// Which split, if any, a definition tied to this read by a `Reuse`
    /// demands of the piece accumulated so far.
    ///
    /// A definition merely pinned to the register this read is pinned to no
    /// longer asks for any: neither operand constrains its value, so there is
    /// no shared register to overwrite. See `reservation_aware_constraint`.
    fn tie_split(
        &self,
        input: &Input<'_, impl InputFunction>,
        end: LivePoint<E>,
        piece: &Piece<E>,
    ) -> Option<TieSplit> {
        if !self.is_read {
            return None;
        }
        let inst = self.point.inst().with_repr32();
        let input_inst = input.func.inst(inst);

        // The value outlives this instruction, so it needs a second copy to
        // carry it to its later uses.
        let survives = end > self.point.next_point();

        if !is_reuse_target(&input_inst, self.operand) {
            return None;
        }

        // The value outlives the tie, so it needs a second copy for its later
        // uses; or a later tie names another read of it, which the definition
        // overwriting that read cannot share a register with.
        if survives || another_tie_follows(&input_inst, self.operand) {
            return Some(TieSplit::AtOverwrite);
        }

        // The value dies here, but folding it in would narrow it below what
        // the tie itself allows, pinning the definition tied to it to a
        // register it may not be able to use.
        let narrowed = piece
            .constraint
            .merge_resolved(&self.constraint, input.machine)
            .is_none_or(|merged| merged != self.constraint);
        if narrowed && !piece.is_empty(self) {
            return Some(TieSplit::Before);
        }

        None
    }
}

/// Which split a definition overwriting the register behind a read demands.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum TieSplit {
    /// The three-piece shape `Piece::split_at_overwrite` draws.
    AtOverwrite,

    /// A plain cut just before the read, which the loop's tail push then
    /// completes into a span holding the tied read alone.
    Before,
}

/// Does a piece being cut off reach the use that cut it?
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Reach {
    /// Yes: the two pieces abut, so a move between them has a source to read.
    Yes,

    /// No: the piece stops just past its own last point, leaving a gap that
    /// whoever wants the value next fills by recomputing it.
    No,
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

    /// The piece's last point, thus far.
    point: LivePoint<E>,

    /// The point of the earliest read folded in, if the piece holds any.
    first_read: Option<LivePoint<E>>,

    /// Whether the piece holds the value's definition.
    holds_def: bool,

    /// Where its run on uses starts.
    run_start: Use<E>,

    /// The merged constraint of just the run of uses.
    run_constraint: OperandConstraint,
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
            point: start,
            first_read: None,
            holds_def: false,
            run_start: uses_start,
            run_constraint: OperandConstraint::Any,
        }
    }

    /// A piece beginning at `start` that holds `u`, and nothing before it.
    fn restarting_at(start: LivePoint<E>, u: &ResolvedUse<E>) -> Self {
        Piece {
            start,
            uses_start: u.use_,
            constraint: u.constraint,
            point: u.point,
            first_read: u.is_read.then_some(u.point),
            holds_def: !u.is_read,
            run_start: u.use_,
            run_constraint: u.constraint,
        }
    }

    /// Has nothing reached this piece yet, so that cutting before `u` would
    /// cut off nothing at all?
    fn is_empty(&self, u: &ResolvedUse<E>) -> bool {
        self.start >= u.point && self.uses_start == u.use_
    }

    /// Fold the given use into this piece.
    ///
    /// `merged` is the merge of `u`'s constraint with the piece's.
    fn fold(&mut self, u: &ResolvedUse<E>, merged: OperandConstraint, machine: &Machine) {
        if u.point != self.point {
            self.run_start = u.use_;
            self.run_constraint = u.constraint;
        } else {
            // The run accumulates only its own uses, not the piece's: whether
            // it can join a tie is only about the uses that would move into the
            // tie's span; the rest of the piece would stay behind.
            self.run_constraint = self
                .run_constraint
                .merge_resolved(&u.constraint, machine)
                .expect("the run admits everything the piece does, which merged with `u`");
        }
        self.constraint = merged;
        if self.first_read.is_none() && u.is_read {
            self.first_read = Some(u.point);
        }
        self.holds_def |= !u.is_read;
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

    /// Push the piece so far as its own span, stopping short of `u`, and log
    /// the cut.
    ///
    /// The caller is left to decide what accumulates `u` itself.
    fn push_before(
        &self,
        spans: &mut PrimaryMap<LiveSpan<E>, LiveSpanData<E>>,
        output: &mut OutputInner<E>,
        events: &mut EventsLog<E>,
        val: Val<E>,
        block: Block<E>,
        u: &ResolvedUse<E>,
        reaches_u: Reach,
    ) -> IResult<()> {
        let end = match reaches_u {
            Reach::Yes => core::cmp::max(u.point, self.point.next_point()),
            // A piece holding the definition keeps its register until the
            // instruction boundary, where a spill of the value would store it.
            Reach::No if self.holds_def => self.point.inst_boundary_after(),
            Reach::No => self.point.next_point(),
        };
        let before = push_span(
            spans,
            output,
            events,
            val,
            (self.start, end),
            (self.uses_start, u.use_),
            self.constraint,
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
        Ok(())
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
        reaches_u: Reach,
    ) -> IResult<Self> {
        self.push_before(spans, output, events, val, block, u, reaches_u)?;
        Ok(Piece::restarting_at(
            u.point.inst_boundary_at_or_before(),
            u,
        ))
    }

    /// Split this piece around the read at `u`, whose register a definition of
    /// the same instruction overwrites.
    ///
    /// Two shapes arrive here. A `Reuse` is a definition, so it overwrites the
    /// location it shares with its target; and a definition pinned to the one
    /// register a read is pinned to overwrites that register just the same. In
    /// both, the definition lands at `Late` and no move may be placed in the
    /// middle of an instruction, so a value that outlives the instruction
    /// needs a second copy for its later uses, and is split like this:
    ///
    /// ```ignore
    ///        def               overwritten read           use
    /// span1: [d================)
    /// span2:                   [r==)
    /// span3:                   [==========================u)
    /// ```
    ///
    /// `span2` holds only the overwritten read and the early half of its
    /// instruction. It is the copy the definition destroys, and nothing ever
    /// reads its end. For a `Reuse`, coalescing bundles it with the span
    /// containing the other tied half. `span3` starts at the same point,
    /// overlapping `span2`, rather than after it, since it exists to keep the
    /// value alive across the instruction for subsequent uses. Coalescing will
    /// also try bundling `span1` with `span3`, when possible, so that the
    /// survivor pays no move.
    ///
    /// This method pushes `span1` and `span2`, and returns `span3` so more uses
    /// can be accumulated into it.
    fn split_at_overwrite(
        &self,
        spans: &mut PrimaryMap<LiveSpan<E>, LiveSpanData<E>>,
        output: &mut OutputInner<E>,
        events: &mut EventsLog<E>,
        machine: &Machine,
        val: Val<E>,
        block: Block<E>,
        u: &ResolvedUse<E>,
    ) -> IResult<Self> {
        // Earlier uses at this same point belong to the overwritten read's
        // span rather than the piece, if they can share a location with it.
        let run_at_this_point = self.point == u.point && self.run_start != u.use_;
        let run_joins_the_tie = run_at_this_point
            && self
                .run_constraint
                .merge_resolved(&u.constraint, machine)
                .is_some();

        // Where the piece ends and where its uses end.
        let (end, uses_end) = if run_joins_the_tie {
            // The run belongs to the tie: the piece stops short of it.
            (u.point, self.run_start)
        } else if run_at_this_point {
            // The run conflicts with the tie, so it stays in the piece, which
            // must reach past the early half to contain it.
            (u.point.next_point(), u.use_)
        } else {
            // Nothing here is in the piece, so it ends where the instruction
            // begins.
            (u.point, u.use_)
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
                block,
            )?)
        } else {
            None
        };

        // `span2`: the reads at this point and the early half of their
        // instruction, existing only to be overwritten by the definition.
        let after = output.entity::<Use<E>>(u.use_.index() + 1)?;
        let copy = push_span(
            spans,
            output,
            events,
            val,
            (u.point, u.point.next_point()),
            (uses_end, after),
            u.constraint,
            block,
        )?;
        event!(
            events,
            OverwriteSplit {
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
/// * a value is named as a `Reuse` target and outlives its instruction,
///
/// * a value is named as a `Reuse` target and the piece so far would narrow it
///   below what the tie allows,
///
/// * a value is read from the one register that a definition of the same
///   instruction overwrites, and outlives that instruction,
///
/// * a use that could be in a register would unnecessarily be constrained to
///   the stack, or
///
/// * the value is `RematCost::AlwaysRemat` and the next use is at a different
///   instruction.
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
    // A value we will always recompute holds a register only at the
    // instructions that actually mention it, so each one gets its own piece.
    let always_remat =
        input.func.value(val.with_repr32()).remat_cost() == Some(RematCost::AlwaysRemat);

    // And a block that never mentions such a value holds it nowhere at all:
    // whoever wants it next recomputes it, so there is nothing to carry
    // through, not even when the value is live on both sides.
    if always_remat && span_uses.is_empty() && !val.is_passed_to_a_successor(input.func, block) {
        return Ok(());
    }

    let mut piece = Piece::empty(start, span_uses.start);
    for use_ in span_uses {
        let u = ResolvedUse::new(input, uses, use_);

        // A value we will always recompute begins a fresh piece at every
        // instruction that mentions it.
        if always_remat && u.point.inst() != piece.point.inst() {
            if piece.uses_start != use_ {
                counts.eager_splits.inc();
                piece.push_before(spans, output, events, val, block, &u, Reach::No)?;
            }
            piece = Piece::empty(u.point.inst_boundary_at_or_before(), use_);
        }

        match u.tie_split(input, end, &piece) {
            Some(TieSplit::AtOverwrite) => {
                debug_assert_eq!(u.point.pos(), Position::Early);
                piece = piece.split_at_overwrite(
                    spans,
                    output,
                    events,
                    input.machine,
                    val,
                    block,
                    &u,
                )?;
                counts.overwrite_splits.inc();
                continue;
            }
            Some(TieSplit::Before) => {
                piece = piece.split_before(spans, output, events, val, block, &u, Reach::Yes)?;
                counts.eager_splits.inc();
                continue;
            }
            None => {}
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
                piece = piece.split_before(spans, output, events, val, block, &u, Reach::Yes)?;
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
    use crate::test::{TestFunction, TestInput, TestMachine};
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

    fn bundle(weight_and_flags: u32) -> LiveBundleData<u32> {
        LiveBundleData {
            spans: EntityRange::empty(),
            region: Region::try_new(0).unwrap(),
            constraint: OperandConstraint::Any,
            preference: RegPreference::new(),
            reg_allocation: None,
            rematerialized: false,
            weight_and_flags,
        }
    }

    fn is_minimal(bundle: &LiveBundleData<u32>) -> bool {
        bundle.weight_and_flags & BUNDLE_MINIMAL != 0
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
        assert_eq!(spill_weight(&plain), 3.25);

        let minimal = bundle(weight | BUNDLE_MINIMAL);
        assert!(is_minimal(&minimal));
        assert_eq!(spill_weight(&minimal), 3.25);
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
        assert_eq!(BUNDLE_SPILL_WEIGHT_MASK | BUNDLE_MINIMAL, u32::MAX);
        assert_eq!(BUNDLE_MINIMAL & BUNDLE_SPILL_WEIGHT_MASK, 0);
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
        assert_eq!(*bundle.preference.intersection(), regs(&[0, 2]));
        assert_eq!(*bundle.preference.union(), regs(&[0, 2]));
    }

    /// A second hint narrows the preference to the registers both hints want.
    #[test]
    fn a_later_hint_narrows_the_preference() {
        let mut bundle = bundle(0);
        bundle.add_hint(regs(&[0, 2]));

        bundle.add_hint(regs(&[2, 3]));
        assert_eq!(*bundle.preference.intersection(), regs(&[2]));
        assert_eq!(*bundle.preference.union(), regs(&[0, 2, 3]));

        // And narrowing again keeps narrowing, rather than starting over from
        // the newest hint.
        bundle.add_hint(regs(&[1, 2]));
        assert_eq!(*bundle.preference.intersection(), regs(&[2]));
        assert_eq!(*bundle.preference.union(), regs(&[0, 1, 2, 3]));
    }

    /// ... but a hint that wants none of the registers the preference does is
    /// dropped, rather than replacing one arbitrary choice with another.
    #[test]
    fn a_conflicting_hint_leaves_the_preference_alone() {
        let mut bundle = bundle(0);
        bundle.add_hint(regs(&[0, 2]));

        bundle.add_hint(regs(&[1, 3]));
        assert_eq!(*bundle.preference.intersection(), regs(&[0, 2]));
        // The union still records what the dropped hint wanted.
        assert_eq!(*bundle.preference.union(), regs(&[0, 1, 2, 3]));
    }

    /// Every register held for a fixed operand, as
    /// `(reg, start, end, reads, writes)`.
    fn reservations(
        live_ranges: &LiveRanges<u32>,
    ) -> Vec<(
        RegAllocation<u32>,
        LivePoint<u32>,
        LivePoint<u32>,
        bool,
        bool,
    )> {
        live_ranges
            .reservations()
            .map(|r| {
                (
                    r.reg(live_ranges),
                    r.start(live_ranges),
                    r.end(live_ranges),
                    r.uses(live_ranges),
                    r.defs(live_ranges),
                )
            })
            .collect()
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

    /// Which values each block passes to a successor as a block-call argument.
    fn all_block_args(func: &TestFunction) -> Set<(Block, Val)> {
        let mut args = Set::new();
        for (block, input_block) in func.blocks() {
            for i in 0..input_block.len_successors() {
                for val in input_block.successor_block_args(i) {
                    args.insert((block, val));
                }
            }
        }
        args
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

    /// A value we will always recompute holds a register for one instruction
    /// at a time: every instruction that mentions it gets its own piece, and
    /// the stretches in between are nobody's.
    #[test]
    fn an_always_remat_value_gets_one_span_per_instruction() {
        let any = OperandConstraint::Any;
        let mut test_input = TestInput::with_use_constraints(&[any, any, any]);

        // The control first: with no remat cost, one unbroken run from the def
        // to the last use, since every gap would need a move to cross it.
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();
        let spans: Vec<LiveSpan> = live_ranges.spans().collect();
        assert_eq!(spans.len(), 1, "{spans:#?}");
        assert_eq!(
            spans[0].start(&live_ranges),
            LivePoint::new(inst(0), Position::Late)
        );
        assert_eq!(
            spans[0].end(&live_ranges),
            LivePoint::new(inst(3), Position::Late)
        );

        test_input.set_remat_costs(Some(RematCost::AlwaysRemat));
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();

        let spans: Vec<LiveSpan> = live_ranges.spans().collect();
        let geometry: Vec<(LivePoint<u32>, LivePoint<u32>)> = spans
            .iter()
            .map(|s| (s.start(&live_ranges), s.end(&live_ranges)))
            .collect();

        let early = |i| LivePoint::new(inst(i), Position::Early);
        let late = |i| LivePoint::new(inst(i), Position::Late);
        assert_eq!(
            geometry,
            vec![
                // The def keeps its own start, and runs to the instruction
                // boundary rather than stopping at its own point: a spill of
                // the value stores it there, out of the register the definition
                // wrote.
                (late(0), early(1)),
                // Then one piece per reading instruction, each ending at its
                // use. The value is dead after the last one, so that piece
                // stops there too.
                (early(1), late(1)),
                (early(2), late(2)),
                (early(3), late(3)),
            ],
            "{spans:#?}"
        );

        // Each use is recorded by the piece that covers it, and none is lost to
        // a gap.
        let points = |span: LiveSpan| -> Vec<LivePoint<u32>> {
            span.uses(&live_ranges)
                .into_iter()
                .map(|u| u.point(&live_ranges))
                .collect()
        };
        assert_eq!(points(spans[0]), vec![late(0)]);
        assert_eq!(points(spans[1]), vec![early(1)]);
        assert_eq!(points(spans[2]), vec![early(2)]);
        assert_eq!(points(spans[3]), vec![early(3)]);
    }

    /// A value we will always recompute is not handed to a block that has no
    /// use for it yet: its span there begins at the instruction that reads it,
    /// however long the value has been live.
    #[test]
    fn an_always_remat_span_starts_at_its_first_use_not_the_block_entry() {
        let mut test_input = TestInput::with_a_value_read_in_two_distant_blocks();
        test_input.set_remat_costs(Some(RematCost::AlwaysRemat));

        let (liveness, live_ranges) = analyze_spans(&test_input).unwrap();
        let val = Val::try_new(0).unwrap();

        // `block3` reads the value at its second instruction, and is live-in
        // because of that read.
        let block = Block::<u32>::try_new(3).unwrap();
        assert!(block.is_live_in(&liveness, val));

        test_input.with_input(|input| {
            let in_block: Vec<LiveSpan> = live_ranges
                .spans()
                .filter(|s| s.block(input.func, &live_ranges) == block)
                .collect();
            assert_eq!(in_block.len(), 1, "{in_block:#?}");

            let read = LivePoint::new(inst(7), Position::Early);
            assert_eq!(in_block[0].start(&live_ranges), read);
            assert!(
                block.start_point(input) < read,
                "the read is not the block's first point, so starting there is a \
                 trim and not a coincidence"
            );
        });
    }

    /// A value we will always recompute keeps the tail of its last span in a
    /// block it is live out of, even though nothing there reads it that late.
    ///
    /// Gaps elsewhere are free because a destination missing its source
    /// recomputes the value instead. That escape is closed for one destination:
    /// a successor's parameter that lives in a spill slot, filled across the
    /// edge from the argument passed to it, since a `Remat` writes a register
    /// and never a slot. Such an edge would reach the `unreachable!` in
    /// `move_generation::MoveGenerator::resolve`, so the block's exit has to
    /// have a span to read the value out of.
    #[test]
    fn an_always_remat_value_keeps_its_live_out_tail() {
        let mut test_input = TestInput::with_a_value_read_in_two_distant_blocks();
        test_input.set_remat_costs(Some(RematCost::AlwaysRemat));

        let (liveness, live_ranges) = analyze_spans(&test_input).unwrap();
        let val = Val::try_new(0).unwrap();

        // `block1` reads the value at its first instruction and nowhere else,
        // and `block3` reads it again, so it is live out of `block1`.
        let block = Block::<u32>::try_new(1).unwrap();
        assert!(block.is_live_out(&liveness, val));

        test_input.with_input(|input| {
            let in_block: Vec<LiveSpan> = live_ranges
                .spans()
                .filter(|s| s.block(input.func, &live_ranges) == block)
                .collect();
            assert_eq!(in_block.len(), 1, "{in_block:#?}");

            let read = LivePoint::new(inst(2), Position::Early);
            assert_eq!(in_block[0].start(&live_ranges), read);
            assert_eq!(
                in_block[0].end(&live_ranges),
                block.end_point(input),
                "the span runs past its only use, all the way to the exit"
            );
        });
    }

    /// A block that never mentions a value we will always recompute holds it
    /// nowhere, however live it is on both sides: nothing there wants it in a
    /// register, and whoever wants it next recomputes it.
    #[test]
    fn an_always_remat_value_that_flows_through_a_block_gets_no_span() {
        let mut test_input = TestInput::with_a_value_read_in_two_distant_blocks();
        test_input.set_remat_costs(Some(RematCost::AlwaysRemat));

        let (liveness, live_ranges) = analyze_spans(&test_input).unwrap();
        let val = Val::try_new(0).unwrap();

        // `block2` is between the two reads, mentions neither the value nor any
        // block argument, and the value is live across all of it.
        let block = Block::<u32>::try_new(2).unwrap();
        assert!(block.is_live_in(&liveness, val));
        assert!(block.is_live_out(&liveness, val));

        test_input.with_input(|input| {
            let in_block: Vec<LiveSpan> = live_ranges
                .spans()
                .filter(|s| s.block(input.func, &live_ranges) == block)
                .collect();
            assert!(in_block.is_empty(), "{in_block:#?}");
        });

        // The control: without a remat cost the value has to be carried across
        // the block, so it gets a span tiling the whole of it.
        let test_input = TestInput::with_a_value_read_in_two_distant_blocks();
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();
        test_input.with_input(|input| {
            let in_block: Vec<LiveSpan> = live_ranges
                .spans()
                .filter(|s| s.block(input.func, &live_ranges) == block)
                .collect();
            assert_eq!(in_block.len(), 1, "{in_block:#?}");
            assert_eq!(in_block[0].start(&live_ranges), block.start_point(input));
            assert_eq!(in_block[0].end(&live_ranges), block.end_point(input));
        });
    }

    /// The point of eager splitting, stated directly: a value whose uses want
    /// locations that no one location satisfies gets one span per demand, cut
    /// just before the use that conflicts.
    ///
    /// The property test above says that no span is left unsatisfiable; this
    /// says where the split lands, which no invariant pins down.
    #[test]
    fn split_a_span_whose_uses_conflict() {
        let rc = |i| OperandConstraint::Reg(RegClass::try_new(i).unwrap());
        let stack = OperandConstraint::Stack;

        let test_input = TestInput::with_use_constraints(&[rc(2), stack]);
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

        // The control: `rc0` and `rc1` are singleton classes, so those uses
        // hold their registers outright rather than constraining the value,
        // and no longer disagree about anything.
        let test_input = TestInput::with_use_constraints(&[rc(0), rc(1)]);
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
        let stack = OperandConstraint::Stack;
        let test_input = TestInput::with_use_constraints(&[rc(2), stack]);
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
        assert_eq!(constraint, rc(2));
        assert_eq!(conflicting, stack);
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

    /// The cut at every instruction is logged like any other eager split, once
    /// per instruction that mentions the value.
    #[test]
    #[cfg(feature = "visualizer")]
    fn per_instruction_splits_of_an_always_remat_value_are_logged() {
        use crate::events::Event;

        let any = OperandConstraint::Any;
        let mut test_input = TestInput::with_use_constraints(&[any, any, any]);
        test_input.set_remat_costs(Some(RematCost::AlwaysRemat));
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
                (val, LivePoint::new(inst(1), Position::Early), any, any),
                (val, LivePoint::new(inst(2), Position::Early), any, any),
                (val, LivePoint::new(inst(3), Position::Early), any, any),
            ],
            "{splits:#?}"
        );

        // And each piece the cuts left behind is itself logged, so the
        // visualizer sees the whole broken shape and not just the last piece.
        let constructed: Vec<_> = events
            .iter()
            .filter_map(|(_, e)| match e {
                Event::SpanConstructed {
                    span, start, end, ..
                } => Some((*span, *start, *end)),
                _ => None,
            })
            .collect();
        assert_eq!(constructed.len(), 4, "{constructed:#?}");
        for (span, start, end) in constructed {
            assert_eq!(start, span.start(&live_ranges));
            assert_eq!(end, span.end(&live_ranges));
        }
    }

    /// An overwrite split names the use it was made for and the one-point span
    /// the definition overwrites.
    ///
    /// Only a `Reuse` triggers one now: a definition merely pinned to the
    /// register a read is pinned to holds it by reservation instead.
    #[test]
    #[cfg(feature = "visualizer")]
    fn overwrite_splits_are_logged() {
        use crate::events::Event;

        for (i, test_input) in [TestInput::with_reuse_of_a_surviving_value()]
            .into_iter()
            .enumerate()
        {
            let (_liveness, live_ranges, events) = analyze_spans_and_events(&test_input).unwrap();

            let splits: Vec<_> = events
                .iter()
                .filter_map(|(_, e)| match e {
                    Event::OverwriteSplit {
                        val,
                        at,
                        target_use,
                        before,
                        copy,
                    } => Some((*val, *at, *target_use, *before, *copy)),
                    _ => None,
                })
                .collect();
            assert_eq!(splits.len(), 1, "fixture {i}: {splits:#?}");
            let (val, at, target_use, before, copy) = splits[0];

            assert_eq!(val, copy.val(&live_ranges), "fixture {i}");
            assert_eq!(at, target_use.point(&live_ranges), "fixture {i}");
            assert_eq!(copy.start(&live_ranges), at, "fixture {i}");
            assert_eq!(copy.end(&live_ranges), at.next_point(), "fixture {i}");
            let before = before.expect("the value is live before the overwritten read");
            assert_eq!(before.end(&live_ranges), at, "fixture {i}");

            // The pieces were logged as they were pushed, before the split that
            // explains them.
            let kinds: Vec<_> = events
                .iter()
                .map(|(_, e)| match e {
                    Event::SpanConstructed { .. } => "span",
                    Event::OverwriteSplit { .. } => "split",
                    _ => "other",
                })
                .collect();
            let split = kinds.iter().position(|k| *k == "split").unwrap();
            assert_eq!(kinds[split - 1], "span", "fixture {i}");
        }
    }

    /// A `Reuse` whose target outlives the instruction gets the three-piece
    /// shape `split_at_overwrite` draws. The properties above say only that the
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

    /// A read pinned to the one register its own instruction's late definition
    /// overwrites does not split its value's span at all.
    ///
    /// This is report 000's shape. The pin no longer constrains the value:
    /// the instruction holds the register across each of its halves, one
    /// reservation for the read and one for the definition, and the value is
    /// free to live somewhere else entirely and be moved in.
    #[test]
    fn a_read_overwritten_by_a_fixed_def_is_not_split() {
        let test_input = TestInput::with_a_read_overwritten_by_a_fixed_def();
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();

        // Operand 0 of `inst1` is the pinned read, whose value outlives it.
        let survivor =
            test_input.with_input(|input| input.func.inst(inst(1)).operand(0).val().unwrap());
        let spans: Vec<LiveSpan> = live_ranges
            .spans()
            .filter(|span| span.val(&live_ranges) == survivor)
            .collect();
        assert_eq!(spans.len(), 1, "{spans:#?}");

        let def = LivePoint::new(inst(0), Position::Late);
        let read = LivePoint::new(inst(1), Position::Early);
        let overwritten = LivePoint::new(inst(1), Position::Late);
        let later_use = LivePoint::new(inst(2), Position::Late);

        assert_eq!(spans[0].start(&live_ranges), def);
        assert_eq!(spans[0].end(&live_ranges), later_use.next_point());
        assert_eq!(
            spans[0]
                .uses(&live_ranges)
                .into_iter()
                .map(|u| u.point(&live_ranges))
                .collect::<Vec<_>>(),
            vec![def, read, later_use],
        );

        // And it is free to live anywhere: the pin is a reservation now, not
        // a constraint.
        test_input.with_input(|input| {
            assert_eq!(
                spans[0].constraint(&live_ranges, input),
                OperandConstraint::Any,
                "{:#?}",
                spans[0],
            );
        });

        // The register is held across the read's half and then across the
        // definition's, by two adjacent reservations rather than one: they
        // deliver different values, and the second one's value is written
        // where the first one's was read.
        let held = reservations(&live_ranges);
        assert_eq!(held.len(), 2, "{held:#?}");
        assert_eq!(
            held[0].0, held[1].0,
            "both name the same register: {held:#?}"
        );
        assert_eq!(held[0], (held[0].0, read, overwritten, true, false));
        assert_eq!(
            held[1],
            (
                held[1].0,
                overwritten,
                overwritten.inst_boundary_after(),
                false,
                true,
            ),
        );

        // The control: with no later read the value dies at the pinned read,
        // and its span ends at the instruction's late half either way.
        let test_input = TestInput::with_a_dying_read_overwritten_by_a_fixed_def();
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();
        let survivor =
            test_input.with_input(|input| input.func.inst(inst(1)).operand(0).val().unwrap());
        let spans: Vec<LiveSpan> = live_ranges
            .spans()
            .filter(|span| span.val(&live_ranges) == survivor)
            .collect();
        assert_eq!(spans.len(), 1, "{spans:#?}");
        assert_eq!(spans[0].end(&live_ranges), overwritten);
    }

    /// Two reads of one value pinned to the register their instruction
    /// overwrites hold that register once between them.
    ///
    /// Naming one register for one value twice asks for nothing more than
    /// naming it once, and there is only ever the one move that delivers it.
    #[test]
    fn two_reads_overwritten_by_a_fixed_def_hold_one_register_once() {
        let test_input = TestInput::with_two_reads_overwritten_by_a_fixed_def();
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();

        let survivor =
            test_input.with_input(|input| input.func.inst(inst(1)).operand(0).val().unwrap());
        let spans: Vec<LiveSpan> = live_ranges
            .spans()
            .filter(|span| span.val(&live_ranges) == survivor)
            .collect();
        assert_eq!(spans.len(), 1, "{spans:#?}");

        let read = LivePoint::new(inst(1), Position::Early);
        let overwritten = LivePoint::new(inst(1), Position::Late);

        // Both reads are in the one span, and the two of them share the one
        // reservation the definition then takes over from.
        assert_eq!(
            spans[0]
                .uses(&live_ranges)
                .into_iter()
                .filter(|u| u.point(&live_ranges) == read)
                .map(|u| u.operand(&live_ranges))
                .collect::<Vec<_>>(),
            vec![0, 1],
        );

        let held = reservations(&live_ranges);
        assert_eq!(held.len(), 2, "{held:#?}");
        assert_eq!(held[0], (held[0].0, read, overwritten, true, false));
        assert_eq!(
            held[1],
            (
                held[1].0,
                overwritten,
                overwritten.inst_boundary_after(),
                false,
                true,
            ),
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
    ///
    /// The tie is what splits here, not the pin: the pinned read reserves
    /// `r0` and leaves every piece free to live wherever it likes.
    #[test]
    fn a_fixed_read_beside_a_reuse_still_splits_at_the_overwrite() {
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

        // Both halves of the tie resolve to the survivor's own class, which
        // is what keeps them in one bundle. The pinned read beside them
        // narrows neither, since its value is delivered into the reserved
        // register rather than read out of the tie's location.
        test_input.with_input(|input| {
            let pinned = reuse_aware_constraint(input.func, input.machine, inst(1), 0);
            let target = reuse_aware_constraint(input.func, input.machine, inst(1), 1);
            let def = reuse_aware_constraint(input.func, input.machine, inst(1), 2);
            assert!(
                fixed_operand_of(input.func, input.machine, inst(1), 0).is_some(),
                "the plain read names a single register: {pinned:?}",
            );
            assert_eq!(def, target, "both halves of the tie must agree");
            assert_eq!(
                target,
                OperandConstraint::Reg(input.func.value(survivor).reg_class()),
                "and on the survivor's own class, not the pinned read's",
            );
        });

        // But the pinned read no longer pins the piece that holds it: one
        // reservation holds the register over the read instead, and the piece
        // answers to the tie alone.
        test_input.with_input(|input| {
            assert_eq!(
                spans[1].constraint(&live_ranges, input),
                OperandConstraint::Reg(input.func.value(survivor).reg_class()),
                "the overwritten piece is constrained by the tie alone: {:#?}",
                spans[1],
            );
        });
        let held = reservations(&live_ranges);
        assert_eq!(held.len(), 1, "{held:#?}");
        assert_eq!(held[0], (held[0].0, tie, overwritten, true, false));
    }

    /// A clobbered register is reserved over the instruction's late half, and
    /// that reservation delivers and carries out nothing.
    #[test]
    fn a_clobber_reserves_its_register_over_the_late_half() {
        let test_input = TestInput::with_an_early_read_beside_a_clobber_of_every_register();
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();

        // The read names the two-register class, not a singleton, so it is
        // not a fixed operand: every reservation below is a clobber's.
        test_input.with_input(|input| {
            let inst1 = input.func.inst(inst(1));
            assert_eq!(inst1.operand(0).pos(), Position::Early);
            assert_eq!(inst1.operand(0).kind(), DefUse::Use);
            assert_eq!(
                inst1.clobbers().iter().collect::<Vec<_>>(),
                vec![Reg::try_new(0).unwrap(), Reg::try_new(1).unwrap()],
            );
        });

        let late = LivePoint::new(inst(1), Position::Late);
        let held = reservations(&live_ranges);
        assert_eq!(held.len(), 2, "one per clobbered register: {held:#?}");
        for (i, entry) in held.iter().enumerate() {
            assert_eq!(
                *entry,
                (
                    RegAllocation::Reg(Reg::try_new(i).unwrap()),
                    late,
                    late.inst_boundary_after(),
                    // No move on either side of a clobber.
                    false,
                    false,
                ),
                "{held:#?}",
            );
        }

        // Val-less, which is what makes it a wall rather than porous.
        for r in live_ranges.reservations() {
            assert_eq!(r.val(&live_ranges), None, "a clobber names no value");
        }
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
            let pinned = reuse_aware_constraint(input.func, input.machine, inst(1), 0);
            let tie = reuse_aware_constraint(input.func, input.machine, inst(2), 2);
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

    /// Reads of one value pinned to two different registers, one of them
    /// beside a tie, leave its span whole.
    ///
    /// Each read holds its own register and has the value delivered into it,
    /// so neither pins the piece it is in and the tie's target has nothing to
    /// fold into or stay out of.
    #[test]
    fn reads_pinned_to_two_registers_leave_a_tie_unsplit() {
        let test_input = TestInput::with_a_pinned_read_before_a_reuse_of_an_unpinned_read();
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();

        // The reuse at `inst2` names operand 0; operand 1 reads the same value
        // at the same point under a pin, and `inst1` read it under a different
        // one at an earlier point.
        let survivor =
            test_input.with_input(|input| input.func.inst(inst(2)).operand(0).val().unwrap());
        let spans: Vec<LiveSpan> = live_ranges
            .spans()
            .filter(|span| span.val(&live_ranges) == survivor)
            .collect();
        assert_eq!(spans.len(), 1, "{spans:#?}");

        let def = LivePoint::new(inst(0), Position::Late);
        let pinned_read = LivePoint::new(inst(1), Position::Early);
        let tie = LivePoint::new(inst(2), Position::Early);
        let overwritten = LivePoint::new(inst(2), Position::Late);

        // One piece holds every read, and runs to the definition that
        // overwrites the value's last one.
        assert_eq!(spans[0].start(&live_ranges), def);
        assert_eq!(spans[0].end(&live_ranges), overwritten);

        let uses = |span: LiveSpan| -> Vec<(usize, LivePoint<u32>)> {
            span.uses(&live_ranges)
                .into_iter()
                .map(|u| (u.operand(&live_ranges), u.point(&live_ranges)))
                .collect()
        };
        assert_eq!(
            uses(spans[0]),
            vec![(0, def), (0, pinned_read), (0, tie), (1, tie)],
        );

        // Neither pin reaches it. All that does is the tie's own half, which
        // asks for the value's own class: a tie has to name where its target
        // is, so `Any` is not an answer it can give.
        test_input.with_input(|input| {
            assert_eq!(
                spans[0].constraint(&live_ranges, input),
                OperandConstraint::Reg(input.func.value(survivor).reg_class()),
                "{:#?}",
                spans[0],
            );
            for operand in [(inst(1), 0), (inst(2), 1)] {
                let (inst, operand) = operand;
                assert!(
                    fixed_operand_of(input.func, input.machine, inst, operand).is_some(),
                    "operand {operand} of {inst:?} names a single register",
                );
                assert_eq!(
                    reservation_aware_constraint(input, inst, operand),
                    OperandConstraint::Any,
                    "and asks nothing of the piece that holds it",
                );
            }
        });

        // Each read holds its register over its own half instead, and the two
        // of them hold different registers.
        let held = reservations(&live_ranges);
        assert_eq!(held.len(), 2, "{held:#?}");
        assert_ne!(
            held[0].0, held[1].0,
            "the two reads name different registers: {held:#?}",
        );
        assert_eq!(
            held[0],
            (
                held[0].0,
                pinned_read,
                pinned_read.next_point(),
                true,
                false
            ),
        );
        assert_eq!(held[1], (held[1].0, tie, overwritten, true, false));

        // And so the definition's span can share a bundle with its target's:
        // the two constraints merge, which is what coalescing needs.
        let tied =
            test_input.with_input(|input| input.func.inst(inst(2)).operand(2).val().unwrap());
        let def_span = live_ranges
            .spans()
            .find(|span| span.val(&live_ranges) == tied)
            .unwrap();
        test_input.with_input(|input| {
            let target = spans[0].constraint(&live_ranges, input);
            let definition = def_span.constraint(&live_ranges, input);
            assert!(
                target.merge_resolved(&definition, input.machine).is_some(),
                "the tie's halves must be coalescable: {target:?} and {definition:?}",
            );
        });
    }

    /// A tie's target that *dies* at it needs no span of its own when an
    /// earlier read named a register the tie cannot use.
    ///
    /// That read holds the register for itself, so it never narrows the piece
    /// it is in, and the tie's two halves are left free to agree on one
    /// location the definition can also be read from.
    #[test]
    fn a_reuse_of_a_dying_value_pinned_earlier_is_not_split() {
        let test_input = TestInput::with_a_pinned_read_before_a_reuse_of_a_dying_value();
        let (_liveness, live_ranges) = analyze_spans(&test_input).unwrap();

        // The reuse at `inst2` names operand 0, the value's last read; `inst1`
        // read it earlier under a pin the tie's own half cannot satisfy.
        let dying =
            test_input.with_input(|input| input.func.inst(inst(2)).operand(0).val().unwrap());
        test_input.with_input(|input| {
            assert_eq!(input.func.inst(inst(1)).operand(0).val(), Some(dying));
            let pinned = reuse_aware_constraint(input.func, input.machine, inst(1), 0);
            let tie = reuse_aware_constraint(input.func, input.machine, inst(2), 0);
            assert!(
                fixed_operand_of(input.func, input.machine, inst(1), 0).is_some(),
                "the earlier read names a single register: {pinned:?}",
            );
            assert_eq!(
                pinned.merge_resolved(&tie, input.machine),
                Some(pinned),
                "one the tie's class holds, so the fixture asks for a \
                 narrowing and not a conflict: {pinned:?} and {tie:?}",
            );
            assert_ne!(pinned, tie, "and strictly narrower than it");

            // But a narrowing the piece never sees: the register is held for
            // the read and the value moved into it.
            assert_eq!(
                reservation_aware_constraint(input, inst(1), 0),
                OperandConstraint::Any,
            );
        });

        let spans: Vec<LiveSpan> = live_ranges
            .spans()
            .filter(|span| span.val(&live_ranges) == dying)
            .collect();
        assert_eq!(spans.len(), 1, "{spans:#?}");

        let def = LivePoint::new(inst(0), Position::Late);
        let pinned_read = LivePoint::new(inst(1), Position::Early);
        let tie = LivePoint::new(inst(2), Position::Early);
        let overwritten = LivePoint::new(inst(2), Position::Late);

        // One piece holds both reads and ends where the tie overwrites the
        // second of them.
        assert_eq!(spans[0].start(&live_ranges), def);
        assert_eq!(spans[0].end(&live_ranges), overwritten);
        assert_eq!(
            spans[0]
                .uses(&live_ranges)
                .into_iter()
                .map(|u| u.point(&live_ranges))
                .collect::<Vec<_>>(),
            vec![def, pinned_read, tie],
        );

        // Each pinned read holds its register over its own half.
        let held = reservations(&live_ranges);
        assert_eq!(held.len(), 2, "{held:#?}");
        assert_ne!(
            held[0].0, held[1].0,
            "the two reads name different registers: {held:#?}",
        );
        assert_eq!(
            held[0],
            (
                held[0].0,
                pinned_read,
                pinned_read.next_point(),
                true,
                false
            ),
        );
        let tied_read = LivePoint::new(inst(3), Position::Early);
        assert_eq!(
            held[1],
            (held[1].0, tied_read, tied_read.next_point(), true, false),
        );

        // Which is what lets the tie coalesce: the target's span keeps the
        // tie's own class, not the earlier read's.
        let tied =
            test_input.with_input(|input| input.func.inst(inst(2)).operand(1).val().unwrap());
        let def_span = live_ranges
            .spans()
            .find(|span| span.val(&live_ranges) == tied)
            .unwrap();
        test_input.with_input(|input| {
            let target = spans[0].constraint(&live_ranges, input);
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
        let rc = |i: u8| OperandConstraint::Reg(RegClass::try_new(i.into()).unwrap());
        let (first, second) = (
            rc(TestMachine::FIRST_PAIR_CLASS),
            rc(TestMachine::SECOND_PAIR_CLASS),
        );

        // Alternating conflicting classes, so that span construction cuts the
        // one value into a span per use and there are several cuts to try.
        // Neither class names a single register, which a use would reserve
        // instead of constraining its span, leaving nothing to cut.
        let test_input = TestInput::with_use_constraints_in(
            TestMachine::four_registers(),
            TestMachine::ALL_FOUR_REGS_CLASS,
            OperandConstraint::Any,
            &[first, second, first, second, first],
        );
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
        let rc = |i: u8| OperandConstraint::Reg(RegClass::try_new(i.into()).unwrap());
        let pairs = [
            rc(TestMachine::FIRST_PAIR_CLASS),
            rc(TestMachine::SECOND_PAIR_CLASS),
        ];
        let any = OperandConstraint::Any;

        // Two conflicting classes, each held for three instructions at a time,
        // so that span construction cuts the value into spans that cover
        // several instructions and hold several uses. That gives every span an
        // interior instruction boundary to cut at, with uses on both sides.
        // Neither class names a single register, which a use would reserve
        // instead of constraining its span, leaving nothing to cut.
        let constraints: Vec<_> = (0..5).flat_map(|k| [pairs[k % 2], any, any]).collect();
        let test_input = TestInput::with_use_constraints_in(
            TestMachine::four_registers(),
            TestMachine::ALL_FOUR_REGS_CLASS,
            any,
            &constraints,
        );
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
                        let (constraint, spill_weight, is_minimal) = (
                            half.constraint(&live_ranges),
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

    /// Recomputing a value discounts *holding* it, not its uses: a minimal
    /// bundle pays full price, a bundle with gaps the discounted one.
    #[test]
    fn rematerializable_values_are_cheaper_to_hold() {
        let rc = |i: u8| OperandConstraint::Reg(RegClass::try_new(i.into()).unwrap());
        let (first, second) = (
            rc(TestMachine::FIRST_PAIR_CLASS),
            rc(TestMachine::SECOND_PAIR_CLASS),
        );

        // A bundle over `pick`'s spans: weight, minimality, and the
        // undiscounted cost and length behind that weight.
        let weigh = |remat, pick: fn(Vec<LiveSpan>) -> Vec<LiveSpan>| -> (f32, bool, f32, usize) {
            // Alternating conflicting classes, so span construction cuts a
            // span per use at every remat cost, not just the always-remat one.
            // Neither class names a single register, which a use would reserve
            // instead of constraining its span, leaving nothing to cut.
            let mut test_input = TestInput::with_use_constraints_in(
                TestMachine::four_registers(),
                TestMachine::ALL_FOUR_REGS_CLASS,
                OperandConstraint::Any,
                &[first, second, first, second],
            );
            test_input.set_remat_costs(remat);

            let (_liveness, mut live_ranges) = analyze_spans(&test_input).unwrap();
            let spans = pick(live_ranges.spans().collect());
            let mut output = OutputInner::<u32>::new();
            let bundle = test_input
                .with_input(|input| {
                    live_ranges.push_bundle(
                        input,
                        &mut output,
                        Region::try_new(0).unwrap(),
                        OperandConstraint::Any,
                        spans.iter().copied(),
                    )
                })
                .unwrap();

            let raw_cost = bundle
                .spans(&live_ranges)
                .flat_map(|span| span.uses(&live_ranges).into_iter())
                .map(|u| u.weight(&live_ranges).as_f32())
                .sum::<f32>();
            let len_insts = bundle
                .spans(&live_ranges)
                .map(|span| span.len_insts(&live_ranges))
                .sum::<usize>();

            (
                bundle.spill_weight(&live_ranges),
                bundle.is_minimal(&live_ranges),
                raw_cost,
                len_insts,
            )
        };

        // Neighbouring spans conflict, so a bundle with room in it takes
        // every other one.
        let with_gaps: fn(Vec<LiveSpan>) -> Vec<LiveSpan> =
            |spans| spans.into_iter().step_by(2).collect();
        let one_use: fn(Vec<LiveSpan>) -> Vec<LiveSpan> = |spans| vec![spans[2]];

        let expected = |cost: f32, len_insts: usize| {
            round_bundle_spill_weight(normalize_spill_weight(cost, len_insts))
        };

        let costs = [
            (None, 1.0),
            (
                Some(RematCost::CheaperThanReload),
                REMAT_CHEAPER_THAN_RELOAD_SCALE,
            ),
            (
                Some(RematCost::CheaperThanMove),
                REMAT_CHEAPER_THAN_MOVE_SCALE,
            ),
            (Some(RematCost::AlwaysRemat), REMAT_ALWAYS_SCALE),
        ];

        for (remat, _) in costs {
            let (weight, minimal, raw_cost, len_insts) = weigh(remat, one_use);
            assert!(minimal, "{remat:?}: wanted a minimal bundle to price");
            assert_eq!(
                weight,
                expected(raw_cost, len_insts),
                "{remat:?}: a minimal bundle pays the full price of its use",
            );
            assert!(weight > 0.0, "{remat:?}");
        }

        for (remat, scale) in costs {
            let (weight, minimal, raw_cost, len_insts) = weigh(remat, with_gaps);
            assert!(
                !minimal,
                "{remat:?}: wanted a bundle with length to give up"
            );
            assert_eq!(
                weight,
                expected(scale * raw_cost, len_insts),
                "{remat:?}: a bundle with gaps pays its value's discounted price",
            );
        }

        assert_eq!(
            weigh(Some(RematCost::AlwaysRemat), with_gaps).0,
            0.0,
            "holding a value that is always cheaper to recompute across a gap \
             buys nothing at all",
        );
    }

    /// A use that names a class holding one register does not constrain its
    /// span at all: the register is held for it by a reservation instead.
    #[test]
    fn a_use_that_names_one_register_becomes_a_reservation() {
        let rc = |i| OperandConstraint::Reg(RegClass::try_new(i).unwrap());

        let summarize = |test_input: &TestInput| -> (Vec<OperandConstraint>, usize) {
            let (_liveness, live_ranges) = analyze_spans(test_input).unwrap();
            let constraints = test_input.with_input(|input| {
                live_ranges
                    .spans()
                    .map(|s| s.constraint(&live_ranges, input))
                    .collect::<Vec<_>>()
            });
            (constraints, live_ranges.reservations().count())
        };

        // `rc0` holds exactly one of `two_registers`' two registers, so the
        // use is reserved out of the span's constraint entirely...
        assert_eq!(
            summarize(&TestInput::with_use_constraints(&[rc(0)])),
            (vec![OperandConstraint::Any], 1),
        );

        // ...while `rc2` holds both, so the use still constrains its span and
        // reserves nothing.
        assert_eq!(
            summarize(&TestInput::with_use_constraints(&[rc(2)])),
            (vec![rc(2)], 0),
        );

        // A stack use and a fixed register use still split the value, because
        // the stack use is a constraint like any other; only the fixed half
        // becomes a reservation.
        assert_eq!(
            summarize(&TestInput::with_use_constraints(&[
                OperandConstraint::Stack,
                rc(0),
            ])),
            (vec![OperandConstraint::Stack, OperandConstraint::Any], 1),
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

        let result = Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run_with(
                m::default::<TestInput>(),
                crate::test::corpus(),
                |test_input: &TestInput| -> Result<(), String> {
                    let func = &test_input.func;
                    let (mut liveness, live_ranges) = analyze_spans(test_input)?;

                    let num_values = func.len_values();
                    let operands = all_operands(func);
                    let block_args = all_block_args(func);

                    // A value we will always recompute is cut into one piece per
                    // instruction that mentions it, leaving gaps between them, so
                    // several of the properties below hold only in the unbroken
                    // shape every other value's live range has. See
                    // `push_span_and_split_conflicts`.
                    let always_remat =
                        |val: Val| func.value(val).remat_cost() == Some(RematCost::AlwaysRemat);
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
                                let this = reservation_aware_constraint(
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

                    // 2. A value's pieces in a block ascend, and they barely
                    // overlap.
                    //
                    // Splitting is what makes several pieces out of one range. They
                    // may overlap only within the instruction the later one begins
                    // at, which it always does at that instruction's boundary.
                    // Anything wider, or a piece starting mid-instruction, would
                    // need a move where there is no gap to put one.
                    //
                    // Nor do they usually leave a gap, since the move out of one
                    // piece and into the next has to read the value from
                    // somewhere. The exception is a value we will always recompute,
                    // which is cut at every instruction precisely so that the
                    // stretches in between are registers nobody has to hold: the
                    // piece across such a gap recomputes the value rather than
                    // receiving it, so it begins at an instruction boundary and
                    // holds that instruction's uses.
                    for ((val, block), spans) in &spans_of {
                        for pair in spans.windows(2) {
                            let (previous, next) = (pair[0], pair[1]);
                            let (previous_start, previous_end) =
                                (previous.start(&live_ranges), previous.end(&live_ranges));
                            let next_start = next.start(&live_ranges);

                            let ascends = previous_start <= next_start;
                            let gap_is_legal = next_start <= previous_end
                                || (always_remat(*val) && next_start.pos() == Position::Early);

                            if !ascends || !gap_is_legal {
                                return Err(format!(
                                    "{val:?}'s spans in {block:?} are out of order or leave a gap it \
                                     has no way to fill: {previous_start:?}..{previous_end:?} is \
                                     followed by {next_start:?}..{:?}",
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
                        let first_inst = input_block.insts().next().unwrap().0;
                        let last_inst = input_block.insts().next_back().unwrap().0;

                        // Does this block mention `val` at `inst`, or anywhere at
                        // all?
                        let mentioned_at = |inst: Inst, val: Val| {
                            operands
                                .iter()
                                .any(|&(b, p, _i, _k, v)| b == block && p.inst() == inst && v == val)
                        };
                        let mentioned_anywhere = |val: Val| {
                            operands
                                .iter()
                                .any(|&(b, _p, _i, _k, v)| b == block && v == val)
                        };

                        // Does this block hold the value anywhere at all?
                        //
                        // It always does for a value it mentions, and for any value
                        // live across it -- except one we will always recompute,
                        // which a block that never mentions it holds nowhere:
                        // nothing here wants it in a register, and whoever wants it
                        // next recomputes it. Passing it to a successor is the
                        // exception, because a parameter that lands in a spill slot
                        // is filled from the argument across the edge, and a
                        // rematerialization writes a register and never a slot.
                        let carried_through = |val: Val| {
                            !always_remat(val)
                                || mentioned_anywhere(val)
                                || block_args.contains(&(block, val))
                        };

                        // 3. A span starts at the block's entry exactly when its
                        // value is live-in there, or is defined by the very first
                        // program point in the block.
                        //
                        // A value we will always recompute is the exception, since
                        // its pieces begin where its uses do: being live-in only
                        // starts it at the entry when the first instruction is one
                        // of the ones mentioning it, or when the block never
                        // mentions it at all and the one piece carried through for
                        // its successors is never cut.
                        let starting_at_entry: Set<Val> = spans_in[&block]
                            .iter()
                            .filter(|&&span| span.start(&live_ranges) == block_start)
                            .map(|&span| span.val(&live_ranges))
                            .collect();
                        let mut expected: Set<Val> = block
                            .live_in(&liveness)
                            .filter(|&val| {
                                !always_remat(val)
                                    || mentioned_at(first_inst, val)
                                    || (!mentioned_anywhere(val) && carried_through(val))
                            })
                            .collect();
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
                        let mut expected: Set<Val> = block
                            .live_out(&liveness)
                            .filter(|&val| carried_through(val))
                            .collect();
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
                        //
                        // A value we will always recompute tiles only the far end.
                        // Where it starts is property 3's business and the gaps its
                        // pieces leave are property 2's, but its last piece still
                        // has to reach the block's exit: a `Remat` writes a register
                        // and never a slot, so an outgoing edge filling a
                        // stack-allocated parameter has to find a source to read
                        // rather than the `unreachable!` in `resolve`. And a block
                        // that neither mentions such a value nor passes it on holds
                        // it nowhere, however live it is on both sides.
                        for val_index in 0..num_values {
                            let val = Val::try_new(val_index).unwrap();
                            if !block.is_live_in(&liveness, val) || !block.is_live_out(&liveness, val) {
                                continue;
                            }
                            let spans = spans_of.get(&(val, block)).filter(|s| !s.is_empty());
                            let Some(spans) = spans else {
                                if !carried_through(val) {
                                    continue;
                                }
                                return Err(format!(
                                    "{val:?} is live across all of {block:?}, but does not have any \
                                     span there",
                                ));
                            };
                            if !carried_through(val) {
                                return Err(format!(
                                    "{block:?} neither mentions {val:?} nor passes it to a successor, \
                                     and it is a value we would always recompute, so the block should \
                                     hold it nowhere; it got {spans:?}",
                                ));
                            }

                            // Property 2 has already established that the pieces
                            // are ascending and, remat aside, leave no gap, so
                            // tiling the block is the first one starting at its
                            // entry and the last one ending at its exit.
                            let first = *spans.first().unwrap();
                            let last = *spans.last().unwrap();
                            let starts_at_entry =
                                always_remat(val) || first.start(&live_ranges) == block_start;
                            if !starts_at_entry || last.end(&live_ranges) != block_end {
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
                    // use's own operand, in that use's own block.
                    test_input.with_input(|input| -> Result<(), String> {
                        for span in live_ranges.spans() {
                            let val = span.val(&live_ranges);

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
                                    (use_spill_cost(input, val, raw, resolved) * frequency).max(0.0),
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
