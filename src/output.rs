use crate::context::ContextInner;
use crate::entity::{Block, Entity, EntityRepr, Val};
use crate::error::{IResult, InternalError};
use crate::input::InputFunction;
use crate::machine::{Interfere, Machine, Reg, RegGroup};
use crate::spill_slot_allocation::{SpillSlot, SpillSlotGroup, SpillSlots};
use crate::timing::Timing;
use alloc::vec::Vec;

/// Everywhere a value lives at some point in the program.
///
/// A value occupies one location per register of its register class, which is
/// more than one when that class is a class of register groups, so this is a
/// register or a group of them, or a spill slot or a group of them. The
/// locations of a group are enumerated by [`Self::len_scalars`] and
/// [`Self::nth_scalar`], and a [`ScalarAllocation`] is a single one of them.
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

/// Everywhere a value lives when it lives in registers.
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

/// Everywhere a value lives when it lives on the stack.
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
            StackAllocation::SpillSlotGroup(group) => group
                .members(spill_slots)
                .nth(i)
                .expect("checked just above"),
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
pub struct Remat<E = u32>
where
    E: EntityRepr,
{
    /// TODO FITZGEN
    pub val: Val<E>,

    /// The registers the rematerializing instruction reads, always
    /// `[None, None]` today, as regicide only rematerializes values whose
    /// definition has no register operands.
    ///
    /// TODO FITZGEN: needs a more expressive representation before we
    /// rematerialize instructions that do read registers.
    pub srcs: [Option<Reg<E>>; 2],

    /// TODO FITZGEN
    pub dest: Reg<E>,
}

/// An edit that goes on an edge the client has to split first.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
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

/// What a [`CriticalEdgeEdit`] does once the edge is split: [`Edit`] without
/// the edge itself, an edge being no different from anywhere else.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
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

/// TODO FITZGEN
pub struct Output {
    pub(crate) which: Option<WhichOutput>,
    #[cfg(feature = "entity-repr-8")]
    pub(crate) output8: OutputInner<u8>,
    #[cfg(feature = "entity-repr-16")]
    pub(crate) output16: OutputInner<u16>,
    pub(crate) output32: OutputInner<u32>,
}

#[allow(dead_code, reason = "not consumed yet")] // TODO FITZGEN
pub(crate) enum WhichOutput {
    #[cfg(feature = "entity-repr-8")]
    Output8,
    #[cfg(feature = "entity-repr-16")]
    Output16,
    Output32,
}

impl Default for Output {
    fn default() -> Self {
        Self::new()
    }
}

impl Output {
    /// TODO FITZGEN
    pub const fn new() -> Self {
        Self {
            which: None,
            #[cfg(feature = "entity-repr-8")]
            output8: OutputInner::new(),
            #[cfg(feature = "entity-repr-16")]
            output16: OutputInner::new(),
            output32: OutputInner::new(),
        }
    }

    /// TODO FITZGEN
    pub fn reset(&mut self) {
        let Self {
            which,
            #[cfg(feature = "entity-repr-8")]
            output8,
            #[cfg(feature = "entity-repr-16")]
            output16,
            output32,
        } = self;
        *which = None;
        #[cfg(feature = "entity-repr-8")]
        output8.reset();
        #[cfg(feature = "entity-repr-16")]
        output16.reset();
        output32.reset();
    }

    /// TODO FITZGEN
    pub fn is_reset(&self) -> bool {
        let Self {
            which,
            #[cfg(feature = "entity-repr-8")]
            output8,
            #[cfg(feature = "entity-repr-16")]
            output16,
            output32,
        } = self;

        #[cfg(feature = "entity-repr-8")]
        if !output8.is_reset() {
            return false;
        }

        #[cfg(feature = "entity-repr-16")]
        if !output16.is_reset() {
            return false;
        }

        which.is_none() && output32.is_reset()
    }

    /// TODO FITZGEN
    pub fn block_insts_and_edits(&self, func: &impl InputFunction, block: Block) -> OutputIter<'_> {
        let _ = (func, block);
        OutputIter { output: self }
    }
}

/// TODO FITZGEN
pub struct OutputIter<'a> {
    #[allow(dead_code, reason = "not consumed yet")] // TODO FITZGEN
    output: &'a Output,
    // TODO: ...
}

pub(crate) struct OutputInner<E: EntityRepr> {
    error: Option<InternalError>,
    edits: Vec<Edit<E>>,
}

impl<E: EntityRepr> OutputInner<E> {
    pub const fn new() -> Self {
        Self {
            error: None,
            edits: Vec::new(),
        }
    }

    fn reset(&mut self) {
        let Self { error, edits } = self;
        *error = None;
        edits.clear();
    }

    pub fn is_reset(&self) -> bool {
        let Self { error, edits } = self;
        error.is_none() && edits.is_empty()
    }

    pub fn construct(
        &mut self,
        context: &mut ContextInner<E>,
        func: &impl InputFunction,
    ) -> IResult<()> {
        let _timing = Timing::new("output");
        let _ = (self, context, func);
        todo!()
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

    #[test]
    fn output_is_send_sync() {
        fn assert_send<T: Send>() {}
        fn assert_sync<T: Sync>() {}
        assert_send::<Output>();
        assert_sync::<Output>();
    }
}
