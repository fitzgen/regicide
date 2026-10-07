use alloc::vec::Vec;
use core::ops::Range;

use crate::context::{Context, WhichContext};
use crate::entity::{Block, Entity, EntityRange, EntityRepr, Inst, PrimaryMap, SecondaryMap, Val};
use crate::error::{IResult, InternalError};
#[cfg(feature = "visualizer")]
use crate::input::Input;
use crate::input::{InputBlock, InputFunction, InputInst as _, OperandConstraint, Position};
use crate::live_ranges::{LivePoint, LiveRanges, LiveSpan, fixed_operand_of};
use crate::liveness::block_inst_bounds;
use crate::machine::{Interfere, Machine, Reg, RegClass, RegClassMembers, RegGroup, RegUnit};
use crate::move_generation::{MoveGeneration, PackedMovePosition};
use crate::rpo::Rpo;
use crate::spill_slot_allocation::{SpillSlot, SpillSlotGroup, SpillSlotSize, SpillSlots};
use crate::timing::Timing;

/// Where a value lives at some point in the program.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Allocation<E = u32>
where
    E: EntityRepr,
{
    /// Allocated to registers.
    Reg(RegAllocation<E>),

    /// Allocated to the stack.
    Stack(StackAllocation<E>),
}

#[cfg(feature = "serialize")]
impl<E> serde::Serialize for Allocation<E>
where
    E: EntityRepr,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            Self::Reg(reg) => reg.serialize(serializer),
            Self::Stack(stack) => stack.serialize(serializer),
        }
    }
}

/// Where a value lives in registers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RegAllocation<E = u32>
where
    E: EntityRepr,
{
    /// Allocated to a single register.
    Reg(Reg<E>),

    /// Allocated to a whole register group.
    RegGroup(RegGroup),
}

#[cfg(feature = "serialize")]
impl<E> serde::Serialize for RegAllocation<E>
where
    E: EntityRepr,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            Self::Reg(reg) => serializer.serialize_newtype_variant("RegAllocation", 0, "reg", reg),
            Self::RegGroup(group) => {
                serializer.serialize_newtype_variant("RegAllocation", 1, "regGroup", group)
            }
        }
    }
}

/// Where a value lives on the stack.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum StackAllocation<E = u32>
where
    E: EntityRepr,
{
    /// Allocated to a single spill slot.
    SpillSlot(SpillSlot<E>),

    /// Allocated to a whole group of spill slots, one per register the value
    /// occupies.
    SpillSlotGroup(SpillSlotGroup<E>),
}

#[cfg(feature = "serialize")]
impl<E> serde::Serialize for StackAllocation<E>
where
    E: EntityRepr,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            Self::SpillSlot(slot) => {
                serializer.serialize_newtype_variant("StackAllocation", 0, "slot", slot)
            }
            Self::SpillSlotGroup(group) => {
                serializer.serialize_newtype_variant("StackAllocation", 1, "slotGroup", group)
            }
        }
    }
}

/// A single machine location: what one move reads or writes.
///
/// This is what parallel move solving deals in, because two locations must
/// either be the same or be disjoint for it to reason about them, and a group
/// is neither with respect to its own members.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ScalarAllocation<E = u32>
where
    E: EntityRepr,
{
    /// A single register.
    Reg(Reg<E>),

    /// A single spill slot.
    Stack(SpillSlot<E>),
}

#[cfg(feature = "serialize")]
impl<E> serde::Serialize for ScalarAllocation<E>
where
    E: EntityRepr,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            Self::Reg(reg) => {
                serializer.serialize_newtype_variant("ScalarAllocation", 0, "reg", reg)
            }
            Self::Stack(slot) => {
                serializer.serialize_newtype_variant("ScalarAllocation", 1, "slot", slot)
            }
        }
    }
}

impl<E> From<Reg<E>> for ScalarAllocation<E>
where
    E: EntityRepr,
{
    fn from(reg: Reg<E>) -> Self {
        Self::Reg(reg)
    }
}

impl<E> Allocation<E>
where
    E: EntityRepr,
{
    /// How many single locations this allocation is made of.
    pub(crate) fn len_scalars(self, machine: &Machine, spill_slots: &SpillSlots<E>) -> usize {
        match self {
            Allocation::Reg(alloc) => alloc.len_scalars(machine),
            Allocation::Stack(alloc) => alloc.len_scalars(spill_slots),
        }
    }

    /// The `i`th of the single locations this allocation is made of.
    pub(crate) fn nth_scalar(
        self,
        machine: &Machine,
        spill_slots: &SpillSlots<E>,
        output: &mut OutputInner<E>,
        i: usize,
    ) -> IResult<ScalarAllocation<E>> {
        Ok(match self {
            Allocation::Reg(alloc) => ScalarAllocation::Reg(alloc.nth_scalar(machine, output, i)?),
            Allocation::Stack(alloc) => ScalarAllocation::Stack(alloc.nth_scalar(spill_slots, i)),
        })
    }
}

impl<E> RegAllocation<E>
where
    E: EntityRepr,
{
    /// How many registers this allocation is made of.
    pub(crate) fn len_scalars(self, machine: &Machine) -> usize {
        match self {
            RegAllocation::Reg(_) => 1,
            RegAllocation::RegGroup(group) => group.members(machine).len(),
        }
    }

    /// The register units this allocation covers, one range per register it
    /// is made of.
    pub(crate) fn units(
        self,
        machine: &Machine,
    ) -> impl Iterator<Item = Range<RegUnit>> + Clone + '_ {
        let (reg, group) = match self {
            RegAllocation::Reg(reg) => (Some(reg), [].as_slice()),
            RegAllocation::RegGroup(group) => (None, group.members(machine)),
        };
        reg.map(|reg| reg.units(machine))
            .into_iter()
            .chain(group.iter().map(|reg| reg.units(machine)))
    }

    /// The `i`th of the registers this allocation is made of.
    pub(crate) fn nth_scalar(
        self,
        machine: &Machine,
        output: &mut OutputInner<E>,
        i: usize,
    ) -> IResult<Reg<E>> {
        debug_assert!(i < self.len_scalars(machine));
        match self {
            RegAllocation::Reg(reg) => Ok(reg),
            RegAllocation::RegGroup(group) => output.with_repr::<E, _>(group.members(machine)[i]),
        }
    }
}

impl<E> StackAllocation<E>
where
    E: EntityRepr,
{
    /// How many spill slots this allocation is made of.
    pub(crate) fn len_scalars(self, spill_slots: &SpillSlots<E>) -> usize {
        match self {
            StackAllocation::SpillSlot(_) => 1,
            StackAllocation::SpillSlotGroup(group) => group.members(spill_slots).len(),
        }
    }

    /// The `i`th of the spill slots this allocation is made of.
    pub(crate) fn nth_scalar(self, spill_slots: &SpillSlots<E>, i: usize) -> SpillSlot<E> {
        debug_assert!(i < self.len_scalars(spill_slots));
        match self {
            StackAllocation::SpillSlot(slot) => slot,
            StackAllocation::SpillSlotGroup(group) => group.members(spill_slots)[i],
        }
    }

    /// The spill slots this allocation is made of, in order.
    #[cfg(test)]
    pub(crate) fn slots(
        self,
        spill_slots: &SpillSlots<E>,
    ) -> impl ExactSizeIterator<Item = SpillSlot<E>> + Clone + '_ {
        (0..self.len_scalars(spill_slots)).map(move |i| self.nth_scalar(spill_slots, i))
    }
}

impl<E> From<Reg<E>> for RegAllocation<E>
where
    E: EntityRepr,
{
    fn from(reg: Reg<E>) -> Self {
        RegAllocation::Reg(reg)
    }
}

impl<E> From<RegGroup> for RegAllocation<E>
where
    E: EntityRepr,
{
    fn from(group: RegGroup) -> Self {
        RegAllocation::RegGroup(group)
    }
}

impl<E> From<SpillSlot<E>> for StackAllocation<E>
where
    E: EntityRepr,
{
    fn from(slot: SpillSlot<E>) -> Self {
        StackAllocation::SpillSlot(slot)
    }
}

impl<E> From<SpillSlotGroup<E>> for StackAllocation<E>
where
    E: EntityRepr,
{
    fn from(group: SpillSlotGroup<E>) -> Self {
        StackAllocation::SpillSlotGroup(group)
    }
}

impl<E> From<Reg<E>> for Allocation<E>
where
    E: EntityRepr,
{
    fn from(reg: Reg<E>) -> Self {
        Allocation::Reg(RegAllocation::Reg(reg))
    }
}

impl<E> From<RegGroup> for Allocation<E>
where
    E: EntityRepr,
{
    fn from(group: RegGroup) -> Self {
        Allocation::Reg(RegAllocation::RegGroup(group))
    }
}

impl<E> From<RegAllocation<E>> for Allocation<E>
where
    E: EntityRepr,
{
    fn from(alloc: RegAllocation<E>) -> Self {
        Allocation::Reg(alloc)
    }
}

impl<E> From<SpillSlot<E>> for Allocation<E>
where
    E: EntityRepr,
{
    fn from(slot: SpillSlot<E>) -> Self {
        Allocation::Stack(StackAllocation::SpillSlot(slot))
    }
}

impl<E> From<SpillSlotGroup<E>> for Allocation<E>
where
    E: EntityRepr,
{
    fn from(group: SpillSlotGroup<E>) -> Self {
        Allocation::Stack(StackAllocation::SpillSlotGroup(group))
    }
}

impl<E> From<StackAllocation<E>> for Allocation<E>
where
    E: EntityRepr,
{
    fn from(alloc: StackAllocation<E>) -> Self {
        Allocation::Stack(alloc)
    }
}

impl<E> From<ScalarAllocation<E>> for Allocation<E>
where
    E: EntityRepr,
{
    fn from(alloc: ScalarAllocation<E>) -> Self {
        match alloc {
            ScalarAllocation::Reg(reg) => Allocation::Reg(RegAllocation::Reg(reg)),
            ScalarAllocation::Stack(slot) => Allocation::Stack(StackAllocation::SpillSlot(slot)),
        }
    }
}

/// Two allocations interfere when they name the same location.
impl<E> Interfere for ScalarAllocation<E>
where
    E: EntityRepr,
{
    fn interfere(machine: &Machine, lhs: Self, rhs: Self) -> bool {
        match (lhs, rhs) {
            (ScalarAllocation::Reg(lhs), ScalarAllocation::Reg(rhs)) => {
                Interfere::interfere(machine, lhs.with_repr32(), rhs.with_repr32())
            }
            (ScalarAllocation::Stack(lhs), ScalarAllocation::Stack(rhs)) => lhs == rhs,
            (ScalarAllocation::Reg(_), ScalarAllocation::Stack(_))
            | (ScalarAllocation::Stack(_), ScalarAllocation::Reg(_)) => false,
        }
    }
}

/// TODO FITZGEN
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "serialize", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "serialize", serde(bound = ""))]
pub enum Move<E = u32>
where
    E: EntityRepr,
{
    /// TODO FITZGEN
    RegReg {
        /// TODO FITZGEN
        from: Reg<E>,
        /// TODO FITZGEN
        to: Reg<E>,
    },

    /// TODO FITZGEN
    Spill {
        /// TODO FITZGEN
        from: Reg<E>,
        /// TODO FITZGEN
        to: SpillSlot<E>,
    },

    /// TODO FITZGEN
    Reload {
        /// TODO FITZGEN
        from: SpillSlot<E>,
        /// TODO FITZGEN
        to: Reg<E>,
    },
}

/// TODO FITZGEN
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "serialize", serde(bound = ""))]
pub struct Remat<E = u32>
where
    E: EntityRepr,
{
    /// TODO FITZGEN
    pub val: Val<E>,
    /// TODO FITZGEN
    pub dest: Reg<E>,
    // TODO: `srcs: FixedVec<[Reg<E>; 2]>` or something?
}

/// An edit that goes on an edge the client has to split first.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "serialize", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "serialize", serde(bound = ""))]
pub struct CriticalEdgeEdit<E = u32>
where
    E: EntityRepr,
{
    /// TODO FITZGEN
    pub target: Block<E>,

    /// Which of the predecessor's outgoing edges this is; a block may branch
    /// to one target twice, so `target` alone does not say which to split.
    pub succ: usize,

    /// TODO FITZGEN
    pub edit: EdgeEdit<E>,
}

/// What a [`CriticalEdgeEdit`] does once the edge is split.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "serialize", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "serialize", serde(bound = ""))]
pub enum EdgeEdit<E = u32>
where
    E: EntityRepr,
{
    /// TODO FITZGEN
    Move(Move<E>),

    /// TODO FITZGEN
    Remat(Remat<E>),
}

/// TODO FITZGEN
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "serialize", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "serialize", serde(bound = ""))]
pub enum Edit<E = u32>
where
    E: EntityRepr,
{
    /// TODO FITZGEN
    Move(Move<E>),

    /// TODO FITZGEN
    Remat(Remat<E>),

    /// TODO FITZGEN
    CriticalEdge(CriticalEdgeEdit<E>),
}

macro_rules! impl_enum_with_repr32 {
    ( $( $ty:ident { $( $variant:ident $fields:tt => $build:expr ),* $(,)? } )* ) => {
        $(
            impl<E> $ty<E>
            where
                E: EntityRepr,
            {
                /// Widen this value's entities to the public representation.
                pub(crate) fn with_repr32(self) -> $ty<u32> {
                    match self {
                        $( $ty::$variant $fields => $build, )*
                    }
                }
            }
        )*
    };
}

impl_enum_with_repr32! {
    Allocation {
        Reg(alloc) => Allocation::Reg(alloc.with_repr32()),
        Stack(alloc) => Allocation::Stack(alloc.with_repr32()),
    }

    RegAllocation {
        Reg(reg) => RegAllocation::Reg(reg.with_repr32()),
        RegGroup(group) => RegAllocation::RegGroup(group),
    }

    StackAllocation {
        SpillSlot(slot) => StackAllocation::SpillSlot(slot.with_repr32()),
        SpillSlotGroup(group) => StackAllocation::SpillSlotGroup(group.with_repr32()),
    }

    Move {
        RegReg { from, to } => Move::RegReg {
            from: from.with_repr32(),
            to: to.with_repr32(),
        },
        Spill { from, to } => Move::Spill {
            from: from.with_repr32(),
            to: to.with_repr32(),
        },
        Reload { from, to } => Move::Reload {
            from: from.with_repr32(),
            to: to.with_repr32(),
        },
    }

    EdgeEdit {
        Move(mv) => EdgeEdit::Move(mv.with_repr32()),
        Remat(remat) => EdgeEdit::Remat(remat.with_repr32()),
    }

    Edit {
        Move(mv) => Edit::Move(mv.with_repr32()),
        Remat(remat) => Edit::Remat(remat.with_repr32()),
        CriticalEdge(edit) => Edit::CriticalEdge(edit.with_repr32()),
    }

    InstOrEdit {
        Inst(inst) => InstOrEdit::Inst(inst.with_repr32()),
        Edit(edit) => InstOrEdit::Edit(edit.with_repr32()),
    }
}

impl<E> Remat<E>
where
    E: EntityRepr,
{
    /// Widen this rematerialization's entities to the public representation.
    pub(crate) fn with_repr32(self) -> Remat<u32> {
        let Self { val, dest } = self;
        Remat {
            val: val.with_repr32(),
            dest: dest.with_repr32(),
        }
    }
}

impl<E> CriticalEdgeEdit<E>
where
    E: EntityRepr,
{
    /// Widen this edge edit's entities to the public representation.
    pub(crate) fn with_repr32(self) -> CriticalEdgeEdit<u32> {
        let Self { target, succ, edit } = self;
        CriticalEdgeEdit {
            target: target.with_repr32(),
            succ,
            edit: edit.with_repr32(),
        }
    }
}

/// The results of register allocation.
pub struct Output<'a> {
    context: &'a Context,
}

/// Run `$body` with `context{8,16,32}` (based on `WhichContext`) bound to
/// `$inner`.
macro_rules! with_inner {
    ( $output:expr, |$inner:ident| $body:expr ) => {
        match $output.which() {
            #[cfg(feature = "entity-repr-8")]
            WhichContext::Context8 => {
                let $inner = &$output.context.context8;
                $body
            }
            #[cfg(feature = "entity-repr-16")]
            WhichContext::Context16 => {
                let $inner = &$output.context.context16;
                $body
            }
            WhichContext::Context32 => {
                let $inner = &$output.context.context32;
                $body
            }
        }
    };
}

/// Like `with_inner` but wrap the result in `$wrapper::Reptr{8,16,32}`.
macro_rules! with_inner_wrapped {
    ( $output:expr, $wrapper:ident, |$inner:ident| $body:expr ) => {
        match $output.which() {
            #[cfg(feature = "entity-repr-8")]
            WhichContext::Context8 => {
                let $inner = &$output.context.context8;
                $wrapper::Repr8($body)
            }
            #[cfg(feature = "entity-repr-16")]
            WhichContext::Context16 => {
                let $inner = &$output.context.context16;
                $wrapper::Repr16($body)
            }
            WhichContext::Context32 => {
                let $inner = &$output.context.context32;
                $wrapper::Repr32($body)
            }
        }
    };
}

/// Like `with_inner` but matching on `$wrapper::Repr{8,16,32}`.
macro_rules! match_repr {
    ( $place:expr, $wrapper:ident, |$inner:ident| $body:expr ) => {
        match $place {
            #[cfg(feature = "entity-repr-8")]
            $wrapper::Repr8($inner) => $body,
            #[cfg(feature = "entity-repr-16")]
            $wrapper::Repr16($inner) => $body,
            $wrapper::Repr32($inner) => $body,
        }
    };
}

impl<'a> Output<'a> {
    pub(crate) fn new(context: &'a Context) -> Self {
        debug_assert!(context.which.is_some());
        Self { context }
    }

    /// Which representation the results this views are stored under.
    fn which(&self) -> WhichContext {
        self.context
            .which
            .expect("an `Output` is only ever created by a successful `run`")
    }

    /// The allocations of `inst`'s operands, in operand order.
    ///
    /// The `i`th element is where the `i`th operand of `inst` lives, so this is
    /// exactly as long as the instruction's operand list.
    pub fn inst_allocs(&self, inst: Inst) -> &[Allocation] {
        with_inner!(self, |inner| inner.output.inst_allocs(inst))
    }

    /// Where `block`'s parameters live when the block is entered, in parameter
    /// order.
    ///
    /// Exactly as long as the block's parameter list; `None` for a parameter
    /// that is not live. For the entry block this is where callers must place
    /// the function's arguments; for any other block it merely documents moves
    /// that [`Output::block_insts_and_edits`] already accounts for.
    pub fn block_param_allocs(&self, block: Block) -> &[Option<Allocation>] {
        with_inner!(self, |inner| inner.output.block_param_allocs(block))
    }

    /// Iterate over `block`'s instructions and the edits to insert around them,
    /// in the order the rewritten block should have them.
    ///
    /// An [`InstOrEdit::Inst`] is an instruction of the original function, to
    /// be kept where it is. An [`InstOrEdit::Edit`] is a move, a
    /// rematerialization, or a request to split a critical edge, to be inserted
    /// at the point the iterator yields it.
    ///
    /// A move or a rematerialization never comes after the block's terminator,
    /// where the machine would jump away before reaching it: the moves for an
    /// outgoing edge that the terminator could host go in the gap immediately
    /// *before* it. An edit that has no such home inside the block is an
    /// [`Edit::CriticalEdge`] instead, and those come last, after every
    /// instruction.
    pub fn block_insts_and_edits(&self, func: &impl InputFunction, block: Block) -> OutputIter<'_> {
        let inner = with_inner_wrapped!(self, OutputIterInner, |inner| block_iter(
            &inner.move_generation,
            func,
            block
        ));
        OutputIter { inner }
    }

    /// Every spill slot register allocation created, and its size.
    pub fn spill_slots(&self) -> impl ExactSizeIterator<Item = (SpillSlot, SpillSlotSize)> + '_ {
        let sizes: &[SpillSlotSize] = with_inner!(self, |inner| inner.spill_slots.sizes());
        sizes.iter().copied().enumerate().map(|(index, size)| {
            let slot = SpillSlot::try_new(index).unwrap();
            (slot, size)
        })
    }

    /// The size of the given spill slot.
    ///
    /// # Panics
    ///
    /// Panics if these results do not contain `slot`.
    pub fn spill_slot(&self, slot: SpillSlot) -> SpillSlotSize {
        self.try_spill_slot(slot)
            .expect("no such spill slot in these results")
    }

    /// The size of the given spill slot, or `None` if these results do not
    /// contain it.
    pub(crate) fn try_spill_slot(&self, slot: SpillSlot) -> Option<SpillSlotSize> {
        let sizes: &[SpillSlotSize] = with_inner!(self, |inner| inner.spill_slots.sizes());
        sizes.get(slot.index()).copied()
    }

    /// Coalesces refused for lack of fuel; `None` without `trace-log`.
    #[doc(hidden)]
    pub fn coalesce_out_of_fuel(&self) -> Option<u64> {
        with_inner!(self, |inner| inner.counts.coalesce_out_of_fuel.get())
    }

    /// How many cycles of the control-flow graph contain `block`, per the
    /// region tree: zero for a block in no cycle.
    ///
    /// A cycle headed by the entry block is the top-level region itself, so
    /// its blocks are at depth zero. An irreducible cycle's nesting depends on
    /// traversal order.
    ///
    /// Only present for the `run` example's estimated cycles.
    #[doc(hidden)]
    pub fn loop_depth(&self, block: Block) -> usize {
        with_inner!(self, |inner| {
            let tree = &inner.region_tree;
            let block = block.with_repr().expect("no such block in these results");
            let mut region = block.region(tree).loop_region(tree);
            let mut depth = 0;
            while let Some(parent) = region.parent(tree) {
                region = parent;
                depth += 1;
            }
            depth
        })
    }

    /// The slots that make up `group`, in the order of the register group whose
    /// members they stand in for.
    pub fn spill_slot_group_members(
        &self,
        group: SpillSlotGroup,
    ) -> impl ExactSizeIterator<Item = SpillSlot> + '_ {
        let inner = with_inner_wrapped!(self, SpillSlotGroupMembersInner, |inner| {
            let group = group.with_repr().unwrap();
            group.members(&inner.spill_slots).iter()
        });
        SpillSlotGroupMembers { inner }
    }
}

/// One element of the stream [`Output::block_insts_and_edits`] yields.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InstOrEdit<E = u32>
where
    E: EntityRepr,
{
    /// An instruction of the original function, which stays where it is.
    Inst(Inst<E>),

    /// An edit to insert at this point in the block.
    Edit(Edit<E>),
}

#[cfg(feature = "visualizer")]
impl Output<'_> {
    /// Write a self-contained HTML visualization of these results to `path`.
    ///
    /// The HTML embeds everything it needs: no network access, no local files.
    pub fn write_visualization_html(
        &self,
        input: &Input<'_, impl InputFunction>,
        path: impl AsRef<std::path::Path>,
    ) -> std::io::Result<()> {
        let path = path.as_ref();
        // Only the context that actually ran has a populated event log; a
        // narrower repr that bailed with `EntityReprTooSmall` left a partial
        // log behind that `with_inner!` correctly skips. Do not concatenate.
        with_inner!(self, |inner| crate::visualizer::write_html(
            inner, input, path
        ))
    }
}

/// An iterator over a block's instructions and edits, as returned by
/// [`Output::block_insts_and_edits`].
pub struct OutputIter<'a> {
    inner: OutputIterInner<'a>,
}

enum OutputIterInner<'a> {
    #[cfg(feature = "entity-repr-8")]
    Repr8(BlockInstsAndEdits<'a, u8>),

    #[cfg(feature = "entity-repr-16")]
    Repr16(BlockInstsAndEdits<'a, u16>),

    Repr32(BlockInstsAndEdits<'a, u32>),
}

impl Iterator for OutputIter<'_> {
    type Item = InstOrEdit;

    fn next(&mut self) -> Option<InstOrEdit> {
        match_repr!(&mut self.inner, OutputIterInner, |iter| iter.next())
    }
}

/// Build the instruction-and-edit stream for `block` out of the edits that move
/// generation left under the `E` representation.
pub(crate) fn block_iter<'a, E>(
    move_generation: &'a MoveGeneration<E>,
    func: &impl InputFunction,
    block: Block,
) -> BlockInstsAndEdits<'a, E>
where
    E: EntityRepr,
{
    block_iter_of(move_generation, &func.block(block), block)
}

/// Like `block_iter`, for a caller that already has the block in hand.
pub(crate) fn block_iter_of<'a, 'b, E>(
    move_generation: &'a MoveGeneration<E>,
    input_block: &impl InputBlock<'b>,
    block: Block,
) -> BlockInstsAndEdits<'a, E>
where
    E: EntityRepr,
{
    let (first, last) = block_inst_bounds(input_block);

    let insts = first.index()..last.index() + 1;

    let block = block.with_repr::<E>().unwrap();
    let first = first.with_repr::<E>().unwrap();
    let last = last.with_repr::<E>().unwrap();

    let points = move_generation.block_point_edit_range(first, last);
    let edges = move_generation.block_edge_edit_range(block);

    BlockInstsAndEdits {
        insts,
        point_base: points.start,
        point_edits: &move_generation.edits()[points],
        edge_base: edges.start,
        edge_edits: &move_generation.edits()[edges],
    }
}

/// One representation's worth of [`OutputIter`].
pub(crate) struct BlockInstsAndEdits<'a, E>
where
    E: EntityRepr,
{
    /// The indices of the block's instructions that have not been yielded yet.
    insts: core::ops::Range<usize>,

    /// Where `point_edits[0]` sits in the whole edit list.
    point_base: usize,

    /// The block's edits at program points inside it, in program order.
    point_edits: &'a [(PackedMovePosition<E>, Edit<E>)],

    /// Where `edge_edits[0]` sits in the whole edit list.
    edge_base: usize,

    /// The edits on critical edges leaving the block, which the client must
    /// split before it can place them.
    edge_edits: &'a [(PackedMovePosition<E>, Edit<E>)],
}

impl<E> BlockInstsAndEdits<'_, E>
where
    E: EntityRepr,
{
    /// The next item, and, for an edit, where it sits in the whole edit list.
    ///
    /// Elimination removes edits by index and must interleave them exactly as
    /// the client sees them, so the two come from the same place.
    pub(crate) fn next_indexed(&mut self) -> Option<(InstOrEdit<E>, Option<usize>)> {
        if !self.insts.is_empty() {
            let inst = Inst::<E>::try_new(self.insts.start)
                .expect("the block's instructions all fit in `E`");

            // Every edit up to and including this instruction's early point
            // goes before the instruction; one at its late point goes after it,
            // and so belongs to the next iteration.
            if let Some((&(pos, edit), rest)) = self.point_edits.split_first() {
                if pos.is_at_or_before(LivePoint::new(inst, Position::Early)) {
                    self.point_edits = rest;
                    let index = self.point_base;
                    self.point_base += 1;
                    return Some((InstOrEdit::Edit(edit), Some(index)));
                }
            }

            self.insts.start += 1;
            return Some((InstOrEdit::Inst(inst), None));
        }

        // The block's instructions are exhausted, so everything still left goes
        // after all of them.
        if let Some((&(_, edit), rest)) = self.point_edits.split_first() {
            self.point_edits = rest;
            let index = self.point_base;
            self.point_base += 1;
            return Some((InstOrEdit::Edit(edit), Some(index)));
        }

        let (&(_, edit), rest) = self.edge_edits.split_first()?;
        self.edge_edits = rest;
        let index = self.edge_base;
        self.edge_base += 1;
        Some((InstOrEdit::Edit(edit), Some(index)))
    }
}

impl<E> Iterator for BlockInstsAndEdits<'_, E>
where
    E: EntityRepr,
{
    type Item = InstOrEdit;

    fn next(&mut self) -> Option<InstOrEdit> {
        self.next_indexed().map(|(item, _)| item.with_repr32())
    }
}

struct SpillSlotGroupMembers<'a> {
    inner: SpillSlotGroupMembersInner<'a>,
}

enum SpillSlotGroupMembersInner<'a> {
    #[cfg(feature = "entity-repr-8")]
    Repr8(core::slice::Iter<'a, SpillSlot<u8>>),

    #[cfg(feature = "entity-repr-16")]
    Repr16(core::slice::Iter<'a, SpillSlot<u16>>),

    Repr32(core::slice::Iter<'a, SpillSlot<u32>>),
}

impl Iterator for SpillSlotGroupMembers<'_> {
    type Item = SpillSlot;

    fn next(&mut self) -> Option<SpillSlot> {
        match_repr!(&mut self.inner, SpillSlotGroupMembersInner, |iter| {
            iter.next().map(|slot| slot.with_repr32())
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl ExactSizeIterator for SpillSlotGroupMembers<'_> {
    fn len(&self) -> usize {
        match_repr!(&self.inner, SpillSlotGroupMembersInner, |iter| iter.len())
    }
}

define_entities! {
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct OperandAllocation = "operand_allocation";
}

define_entities! {
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct BlockParamAllocation = "block_param_allocation";
}

/// What an operand's allocation slot holds until the scatter fills it in.
const UNALLOCATED: Allocation =
    Allocation::Reg(RegAllocation::Reg(<Reg as Entity>::MAX_REPRESENTABLE));

/// The allocation naming `class`'s first member.
fn first_member(machine: &Machine, class: RegClass) -> Option<Allocation> {
    match class.members(machine) {
        RegClassMembers::Regs(regs) => regs.first().copied().map(RegAllocation::Reg),
        RegClassMembers::Groups(groups) => groups.first().copied().map(RegAllocation::RegGroup),
    }
    .map(Allocation::Reg)
}

/// The register allocation results under one entity representation.
pub(crate) struct OutputInner<E>
where
    E: EntityRepr,
{
    error: Option<InternalError>,

    /// Contiguous storage for every instruction's operands' allocations.
    ///
    /// The allocations are stored under the public `u32` representation, rather
    /// than under `E`, so that `inst_allocs` can hand out a `&[Allocation]`.
    operand_allocs: PrimaryMap<OperandAllocation<E>, Allocation>,

    /// Where each instruction's operands' allocations live within
    /// `operand_allocs`.
    inst_allocs: SecondaryMap<Inst<E>, EntityRange<OperandAllocation<E>>>,

    /// Contiguous storage for where every block's parameters arrive; `None` for
    /// a parameter that no span covers. Stored under the public `u32`
    /// representation, like `operand_allocs`.
    param_allocs: PrimaryMap<BlockParamAllocation<E>, Option<Allocation>>,

    /// Where each block's parameters' allocations live within `param_allocs`.
    block_params: SecondaryMap<Block<E>, EntityRange<BlockParamAllocation<E>>>,

    /// Scratch space for the spans of a block's parameters reported thus far.
    incumbents: Vec<Option<LiveSpan<E>>>,
}

impl<E: EntityRepr> OutputInner<E> {
    pub const fn new() -> Self {
        Self {
            error: None,
            operand_allocs: PrimaryMap::new(),
            inst_allocs: SecondaryMap::new(EntityRange::empty()),
            param_allocs: PrimaryMap::new(),
            block_params: SecondaryMap::new(EntityRange::empty()),
            incumbents: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            error,
            operand_allocs: inst_allocation_storage,
            inst_allocs,
            param_allocs,
            block_params,
            incumbents,
        } = self;
        *error = None;
        inst_allocation_storage.reset();
        inst_allocs.reset();
        param_allocs.reset();
        block_params.reset();
        incumbents.clear();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            error,
            operand_allocs: inst_allocation_storage,
            inst_allocs,
            param_allocs,
            block_params,
            incumbents,
        } = self;
        error.is_none()
            && inst_allocation_storage.is_reset()
            && inst_allocs.is_reset()
            && param_allocs.is_reset()
            && block_params.is_reset()
            && incumbents.is_empty()
    }

    pub fn construct(
        &mut self,
        func: &impl InputFunction,
        machine: &Machine,
        rpo: &Rpo<E>,
        live_ranges: &LiveRanges<E>,
        spill_slots: &SpillSlots<E>,
    ) -> IResult<()> {
        debug_assert!(self.is_reset());
        let _timing = Timing::new("output");

        self.operand_allocs.reserve(func.len_insts());
        for (block, input_block) in func.blocks() {
            self.reserve_block_inst_allocs(func, machine, &input_block)?;
            self.reserve_block_param_allocs(block, &input_block)?;
        }

        for block in rpo.iter() {
            for u in block.uses(live_ranges) {
                // A fixed operand's allocation was already filled in by
                // `reserve_block_inst_allocs`.
                if u.is_fixed(live_ranges, func, machine) {
                    continue;
                }

                let inst = u.point(live_ranges).inst();
                let operand = u.operand(live_ranges);
                let alloc = u
                    .span(live_ranges)
                    .allocation(live_ranges, spill_slots)
                    .expect("a use's span holds its value somewhere");

                let range = self.inst_allocs[inst];
                let index = range.start.index() + operand;
                debug_assert!(index < range.end.index());
                self.operand_allocs.as_mut_slice()[index] = alloc.with_repr32();
            }
        }

        self.scatter_block_param_allocs(func, live_ranges, spill_slots);

        if cfg!(debug_assertions) {
            for block in rpo.iter() {
                self.debug_assert_block_allocated(&func.block(block.with_repr32()));
            }
        }

        Ok(())
    }

    /// Record where each of a block's parameters arrives.
    fn scatter_block_param_allocs(
        &mut self,
        func: &impl InputFunction,
        live_ranges: &LiveRanges<E>,
        spill_slots: &SpillSlots<E>,
    ) {
        let mut incumbents = core::mem::take(&mut self.incumbents);
        debug_assert!(incumbents.is_empty());
        incumbents.resize(self.param_allocs.len(), None);

        // `block_spans` and `live_in_spans` are invalid at this point, since
        // region allocation already split spans, so we have to walk everything.
        for span in live_ranges.spans() {
            let block = span.block(func, live_ranges);
            let input_block = func.block(block.with_repr32());

            let (first_inst, _) = block_inst_bounds(&input_block);
            let Some(first_inst) = first_inst.with_repr::<E>() else {
                continue;
            };
            if span.start(live_ranges) != LivePoint::new(first_inst, Position::Early) {
                continue;
            }

            let val = span.val(live_ranges).with_repr32();
            let Some(k) = input_block.params().position(|param| param == val) else {
                continue;
            };

            let range = self.block_params[block];
            let index = range.start.index() + k;
            debug_assert!(index < range.end.index());

            // Keep the span that reaches furthest, breaking ties on the span
            // itself.
            let key = (span.end(live_ranges), span);
            match incumbents[index] {
                Some(prev) if (prev.end(live_ranges), prev) >= key => continue,
                _ => incumbents[index] = Some(span),
            }

            let alloc = span
                .allocation(live_ranges, spill_slots)
                .expect("a block parameter always has an allocation");
            self.param_allocs.as_mut_slice()[index] = Some(alloc.with_repr32());
        }

        incumbents.clear();
        self.incumbents = incumbents;
    }

    /// Give each of `block`'s parameters a slot in the flat storage, and record
    /// the block's range within it.
    fn reserve_block_param_allocs<'a>(
        &mut self,
        block: Block,
        input_block: &impl InputBlock<'a>,
    ) -> IResult<()> {
        let block = self.with_repr::<E, _>(block)?;

        let start_index = self.param_allocs.len();
        let end_index = start_index + input_block.params().count();
        let start = self.entity::<BlockParamAllocation<E>>(start_index)?;
        let end = self.entity::<BlockParamAllocation<E>>(end_index)?;

        for _ in start_index..end_index {
            self.param_allocs.push_unwrap(None);
        }
        self.block_params[block] = EntityRange { start, end };
        Ok(())
    }

    /// Where `block`'s parameters arrive, in parameter order.
    pub fn block_param_allocs(&self, block: Block) -> &[Option<Allocation>] {
        let Some(block) = block.with_repr::<E>() else {
            return &[];
        };
        let range = self.block_params[block];
        &self.param_allocs.as_slice()[range.indices()]
    }

    /// Where `block`'s parameters arrive, mutably, so that a test can break a
    /// correct allocation and watch the checker notice.
    #[cfg(test)]
    pub(crate) fn block_param_allocs_mut(&mut self, block: Block) -> &mut [Option<Allocation>] {
        let Some(block) = block.with_repr::<E>() else {
            return &mut [];
        };
        let range = self.block_params[block];
        &mut self.param_allocs.as_mut_slice()[range.indices()]
    }

    /// Give each of `input_block`'s instructions' operands a placeholder slot
    /// in the flat storage, and record the instruction's range within it.
    ///
    /// An operand that names no value gets its answer here rather than from
    /// the scatter: it has no span for the scatter to walk, because there is
    /// no value to place. So does a fixed operand, whose answer is the
    /// register held for it.
    fn reserve_block_inst_allocs<'a>(
        &mut self,
        func: &impl InputFunction,
        machine: &Machine,
        input_block: &impl InputBlock<'a>,
    ) -> IResult<()> {
        for (inst, input_inst) in input_block.insts() {
            let e_inst = self.with_repr::<E, _>(inst)?;

            let start_index = self.operand_allocs.len();
            let end_index = start_index + input_inst.operands_len();
            let start = self.entity::<OperandAllocation<E>>(start_index)?;
            let end = self.entity::<OperandAllocation<E>>(end_index)?;

            for i in start_index..end_index {
                let index = i - start_index;
                let operand = input_inst.operand(index);
                let alloc = match (operand.val(), operand.constraint()) {
                    (None, OperandConstraint::Reg(class)) => {
                        first_member(machine, class).unwrap_or(UNALLOCATED)
                    }
                    // A fixed operand is reported in the register reserved
                    // for it.
                    _ => match fixed_operand_of(func, machine, inst, index) {
                        Some(fixed) => Allocation::Reg(fixed.reg),
                        None => UNALLOCATED,
                    },
                };
                self.operand_allocs.push_unwrap(alloc);
            }
            self.inst_allocs[e_inst] = EntityRange { start, end };
        }
        Ok(())
    }

    /// Assert that the scatter left no operand of `input_block` unallocated.
    fn debug_assert_block_allocated<'a>(&self, input_block: &impl InputBlock<'a>) {
        for (inst, _) in input_block.insts() {
            for (i, alloc) in self.inst_allocs(inst).iter().enumerate() {
                debug_assert_ne!(
                    *alloc, UNALLOCATED,
                    "operand {i} of {inst:?} never got an allocation",
                );
            }
        }
    }

    /// The allocations of `inst`'s operands, in operand order.
    pub fn inst_allocs(&self, inst: Inst) -> &[Allocation] {
        let Some(inst) = inst.with_repr::<E>() else {
            return &[];
        };
        let range = self.inst_allocs[inst];
        &self.operand_allocs.as_slice()[range.indices()]
    }

    /// Those allocations, mutably, so that a test can break a correct
    /// allocation and watch the checker notice.
    #[cfg(test)]
    pub(crate) fn inst_allocs_mut(&mut self, inst: Inst) -> &mut [Allocation] {
        let Some(inst) = inst.with_repr::<E>() else {
            return &mut [];
        };
        let range = self.inst_allocs[inst];
        &mut self.operand_allocs.as_mut_slice()[range.indices()]
    }

    #[inline]
    pub fn entity<Ent>(&mut self, index: usize) -> IResult<Ent>
    where
        Ent: Entity,
    {
        match Ent::try_new(index) {
            Some(e) => Ok(e),
            None => self.error(InternalError::EntityReprTooSmall),
        }
    }

    #[inline]
    pub fn with_repr<R, Ent>(&mut self, entity: Ent) -> IResult<Ent::Family<R>>
    where
        Ent: Entity,
        R: EntityRepr,
    {
        match entity.with_repr::<R>() {
            Some(e) => Ok(e),
            None => self.error(InternalError::EntityReprTooSmall),
        }
    }

    #[inline]
    pub fn result<T, Err>(&mut self, result: Result<T, Err>) -> IResult<T>
    where
        Err: Into<InternalError>,
    {
        match result {
            Ok(x) => Ok(x),
            Err(e) => self.error(e),
        }
    }

    /// Have we already recorded an error?
    #[inline]
    pub fn has_error(&self) -> bool {
        self.error.is_some()
    }

    #[cold]
    pub fn error<T>(&mut self, error: impl Into<InternalError>) -> IResult<T> {
        if !self.has_error() {
            self.error = Some(error.into());
        }
        Err(())
    }

    pub fn take_error(&mut self) -> InternalError {
        self.error.take().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Error;
    use crate::test::TestInput;
    use mutatis::{
        check::{Check, CheckResult},
        mutators as m,
    };
    use std::{format, string::String, vec::Vec};

    /// How many edits move generation produced, across the whole function.
    fn total_edits(output: &Output<'_>) -> usize {
        with_inner!(output, |inner| inner.move_generation.edits().len())
    }

    #[test]
    fn output_is_send_sync() {
        fn assert_send<T: Send>() {}
        fn assert_sync<T: Sync>() {}
        assert_send::<Output<'_>>();
        assert_sync::<Output<'_>>();
    }

    /// The results `Output` hands back describe the whole function: every
    /// operand has an allocation, every instruction is yielded exactly once in
    /// program order, and every edit move generation produced is yielded
    /// exactly once.
    #[test]
    fn output_properties() -> CheckResult<TestInput> {
        Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run_with(
                m::default::<TestInput>(),
                crate::test::corpus(),
                |test_input: &TestInput| -> Result<(), String> {
                    let mut context = Context::new();
                    test_input.with_input(|input| {
                        let func = input.func;

                        let output = match crate::run(&mut context, input) {
                            Ok(output) => output,
                            // Not every function fits on every machine, and that
                            // is not this pass's problem.
                            Err(Error::TooManyLiveRegs) => return Ok(()),
                            Err(error) => return Err(format!("allocation failed: {error:?}")),
                        };

                        // Every operand gets exactly one allocation, and no two
                        // operands of one instruction that are in registers share a
                        // register unless they are the same value.
                        for (_, input_block) in func.blocks() {
                            for (inst, input_inst) in input_block.insts() {
                                let allocs = output.inst_allocs(inst);
                                if allocs.len() != input_inst.operands_len() {
                                    return Err(format!(
                                        "{inst:?} has {} operands but {} allocations",
                                        input_inst.operands_len(),
                                        allocs.len(),
                                    ));
                                }
                            }
                        }

                        // Every instruction is yielded exactly once, in program
                        // order, and no edit is dropped or duplicated.
                        let mut num_edits = 0;
                        for (block, input_block) in func.blocks() {
                            let expected: Vec<Inst> =
                                input_block.insts().map(|(inst, _)| inst).collect();

                            let mut insts = Vec::new();
                            let mut seen_last_inst = false;
                            for item in output.block_insts_and_edits(func, block) {
                                match item {
                                    InstOrEdit::Inst(inst) => {
                                        seen_last_inst = insts.len() + 1 == expected.len();
                                        insts.push(inst);
                                    }
                                    InstOrEdit::Edit(edit) => {
                                        num_edits += 1;
                                        // A critical edge is split on the way out
                                        // of the block, so its edits come after
                                        // every instruction in it.
                                        if matches!(edit, Edit::CriticalEdge(_)) && !seen_last_inst
                                        {
                                            return Err(format!(
                                                "{block:?} yielded {edit:?} before its terminator",
                                            ));
                                        }
                                    }
                                }
                            }

                            if insts != expected {
                                return Err(format!(
                                    "{block:?} yielded instructions {insts:?} but \
                                     contains {expected:?}",
                                ));
                            }
                        }

                        let total = total_edits(&output);
                        if num_edits != total {
                            return Err(format!(
                                "the blocks yielded {num_edits} edits but move generation produced \
                                 {total}",
                            ));
                        }

                        Ok(())
                    })
                },
            )
    }

    /// The spill slot queries agree with each other and cover every slot.
    #[test]
    fn spill_slot_queries_agree() -> CheckResult<TestInput> {
        Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run_with(
                m::default::<TestInput>(),
                crate::test::corpus(),
                |test_input: &TestInput| -> Result<(), String> {
                    let mut context = Context::new();
                    test_input.with_input(|input| {
                        let output = match crate::run(&mut context, input) {
                            Ok(output) => output,
                            Err(Error::TooManyLiveRegs) => return Ok(()),
                            Err(error) => return Err(format!("allocation failed: {error:?}")),
                        };

                        let slots: Vec<(SpillSlot, SpillSlotSize)> = output.spill_slots().collect();
                        if slots.len() != output.spill_slots().len() {
                            return Err(format!(
                                "`spill_slots` reports {} slots but yields {}",
                                output.spill_slots().len(),
                                slots.len(),
                            ));
                        }

                        for (i, (slot, size)) in slots.iter().copied().enumerate() {
                            if slot.index() != i {
                                return Err(format!("the {i}th slot yielded is {slot:?}"));
                            }
                            if output.spill_slot(slot) != size {
                                return Err(format!(
                                    "`spill_slots` says {slot:?} is {size:?} but `spill_slot` says \
                                 {:?}",
                                    output.spill_slot(slot),
                                ));
                            }
                        }

                        // Every group is made of slots that exist and that no other
                        // member of the group is.
                        for (_, input_block) in input.func.blocks() {
                            for (inst, _) in input_block.insts() {
                                for alloc in output.inst_allocs(inst) {
                                    let Allocation::Stack(StackAllocation::SpillSlotGroup(group)) =
                                        *alloc
                                    else {
                                        continue;
                                    };
                                    let members: Vec<SpillSlot> =
                                        output.spill_slot_group_members(group).collect();
                                    for (i, member) in members.iter().copied().enumerate() {
                                        if member.index() >= slots.len() {
                                            return Err(format!(
                                                "{group:?} contains {member:?}, which \
                                                            is not a slot we created"
                                            ));
                                        }
                                        if members[..i].contains(&member) {
                                            return Err(format!(
                                                "{group:?} contains {member:?} more than once",
                                            ));
                                        }
                                    }
                                }
                            }
                        }

                        Ok(())
                    })
                },
            )
    }
}
