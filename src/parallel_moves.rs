//! Sequentializing parallel moves.
//!
//! When we need to shuffle registers at some program point, we have a sequence
//! of source-to-destination moves. However, if move A names the source of move
//! B as its destination, then we must perform B before A, or else the value
//! that B wants to move will have been clobbered. To make things worse, we can
//! even have move cycles, where we need to swap the values in two
//! registers. Logically, all the sources need to be read at once, before any
//! write occurs, but machines don't actually behave like this.
//!
//! This module implements parallel-move solving: given a set of parallel moves,
//! find a sequential series of moves that implement the parallel-move
//! semantics.

use crate::entity::{Entity as _, EntityRepr, EntitySet, PrimaryMap, SecondaryMap, Val};
use crate::machine::{Reg, RegSet};
use crate::output::ScalarAllocation;
use crate::spill_slot_allocation::SpillSlot;
use alloc::vec::Vec;
use core::mem;

define_entities! {
    /// A move within the batch currently being solved.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct SeqMove = "seq_move";
}

define_fixed_size_entities! {
    /// One bit of one move's `State` in a `MoveStates`.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct StateBit: u32 = "state_bit";
}

impl StateBit {
    const MAX: usize = u32::MAX as usize;
}

/// One move in a parallel batch: `dst := src`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "serialize", serde(bound = ""))]
pub struct ParallelMove<E>
where
    E: EntityRepr,
{
    /// The location read.
    src: ScalarAllocation<E>,

    /// The location written.
    dst: ScalarAllocation<E>,

    /// The value being moved.
    ///
    /// `Some` for a move handed to the solver, `None` for the saves and
    /// reloads it emits around an evicted register.
    val: Option<Val<E>>,
}

impl<E> ParallelMove<E>
where
    E: EntityRepr,
{
    /// A move of `val` from `src` to `dst`.
    ///
    /// Only the solver builds a move without a value, so taking one here is
    /// what keeps a caller's move from being mistaken for a save or a reload
    /// of the solver's own.
    pub fn new(val: Val<E>, src: ScalarAllocation<E>, dst: ScalarAllocation<E>) -> Self {
        ParallelMove {
            src,
            dst,
            val: Some(val),
        }
    }

    /// The location read.
    pub fn src(self) -> ScalarAllocation<E> {
        self.src
    }

    /// The location written.
    pub fn dst(self) -> ScalarAllocation<E> {
        self.dst
    }

    /// The value being moved, absent for the spills and reloads the solver
    /// emits around an evicted register.
    pub fn val(self) -> Option<Val<E>> {
        self.val
    }

    /// Put `reg` away in `slot`.
    fn spill(reg: Reg<E>, slot: SpillSlot<E>) -> Self {
        ParallelMove {
            src: ScalarAllocation::Reg(reg),
            dst: ScalarAllocation::Stack(slot),
            val: None,
        }
    }

    /// Replace what `spill` set aside.
    fn reload(slot: SpillSlot<E>, reg: Reg<E>) -> Self {
        ParallelMove {
            src: ScalarAllocation::Stack(slot),
            dst: ScalarAllocation::Reg(reg),
            val: None,
        }
    }

    /// The same move, reading somewhere else.
    fn with_src(self, src: ScalarAllocation<E>) -> Self {
        ParallelMove { src, ..self }
    }

    /// The same move, writing somewhere else.
    fn with_dst(self, dst: ScalarAllocation<E>) -> Self {
        ParallelMove { dst, ..self }
    }

    /// What this move does to the pool of registers we can hand out as
    /// scratch.
    fn tier(self) -> Tier {
        match (self.src, self.dst) {
            (ScalarAllocation::Reg(_), ScalarAllocation::Reg(_)) => Tier::Gains,
            (ScalarAllocation::Stack(_), _) => Tier::Spares,
            (ScalarAllocation::Reg(_), ScalarAllocation::Stack(_)) => Tier::Spends,
        }
    }

    /// Whether `self` moves memory to memory, which no machine can do in one
    /// instruction.
    fn is_stack_to_stack(self) -> bool {
        matches!(
            (self.src, self.dst),
            (ScalarAllocation::Stack(_), ScalarAllocation::Stack(_))
        )
    }
}

/// Why a batch could not be sequentialized.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SolveError {
    /// The batch had more moves than `E` can index.
    EntityReprTooSmall,
}

/// Where the solver gets the scratch locations it needs.
///
/// The methods that produce a scratch are a ladder the solver climbs: a
/// register nothing wants, then a register something wants that we put back
/// afterwards, then a stack slot for a broken cycle, which needs no register.
pub trait ScratchSource<E>
where
    E: EntityRepr,
{
    /// Whether these two locations share any register unit.
    ///
    /// Overlap can be partial and is not transitive: a two-unit name can
    /// cover two one-unit names that do not cover each other.
    fn overlaps(&self, a: ScalarAllocation<E>, b: ScalarAllocation<E>) -> bool;

    /// Whether `reg` can stand in as the scratch for `mv`: whether it is in the
    /// right bank and is one that can be clobbered.
    ///
    /// Only registers the batch has already finished with are offered, and the
    /// first one approved is the one used.
    ///
    /// The batch naming `reg` is not a reason to refuse; the solver handles
    /// checking its availability.
    fn is_suitable(&mut self, mv: ParallelMove<E>, reason: ScratchReason, reg: Reg<E>) -> bool;

    /// A register the batch has no use for, to be taken as it is.
    ///
    /// It must be untouched by every move in the batch and must not overlap
    /// anything in `unavailable`, which lists the scratch locations already
    /// holding a parked value.
    fn find_free(
        &mut self,
        mv: ParallelMove<E>,
        reason: ScratchReason,
        unavailable: &[ScalarAllocation<E>],
    ) -> Option<Reg<E>>;

    /// A register freed by evicting whatever it and the registers it shares a
    /// register unit with hold.
    ///
    /// The necessary evictions are written into `evicting`. Each slot must be
    /// correctly sized for the associated register.
    ///
    /// `spent` lists the registers the solver has already finished moving
    /// values into, which should not be evicted. Evicting a spent register is
    /// worse than wasteful, since two overlapping registers cannot both be put
    /// back.
    ///
    /// The solver emits the spills and reloads itself, bracketing every use we
    /// make of the register, so nothing else can tell it was borrowed.
    ///
    /// When given `ScratchReason::CycleBreak`, the scratch is held in a wide
    /// bracket across the other moves in the cycle. When given
    /// `ScratchReason::StackToStack`, the scratch is only held in a tight
    /// bracket around just the stack-to-stack move. It must be valid to use the
    /// returned scratch for the reason's bracket.
    ///
    /// It is only valid to return `None` when given
    /// `ScratchReason::CycleBreak`, which tells the solver to try an emergency
    /// spill slot. All other situations must return a scratch register.
    fn evict(
        &mut self,
        mv: ParallelMove<E>,
        reason: ScratchReason,
        unavailable: &[ScalarAllocation<E>],
        spent: &[Reg<E>],
        evicting: &mut Vec<(Reg<E>, SpillSlot<E>)>,
    ) -> Result<Option<Reg<E>>, SolveError>;

    /// The `ScratchSource` implementation's own answer for how wide a bracket
    /// `reg` gets, so that the solver can check it against the one it assigns.
    ///
    /// The two rules have to agree exactly, because each side applies its own
    /// without asking the other, and a disagreement either strands a value or
    /// wastes a slot.
    ///
    /// Answering `None` means nothing is checked.
    #[cfg(debug_assertions)]
    fn predicted_tight(&self, _reg: Reg<E>, _unavailable: &[ScalarAllocation<E>]) -> Option<bool> {
        None
    }

    /// A stack slot for a broken cycle to park in, when the bank has no
    /// register to spare at all.
    ///
    /// A cycle running through every register in a bank leaves nothing free
    /// and nothing to evict. A cycle break needs no register of its own: all
    /// it asks is that a move can reach its scratch, which a slot can so long
    /// as the other end is a register.
    ///
    /// Only ever asked for a `ScratchReason::CycleBreak`; a move between two
    /// slots has to go through a register, so a third slot would be no help.
    /// The slot holds the parked value until the move that reads it back, so
    /// the batch must never name it and no scratch still in use may have taken
    /// it, hence `unavailable`.
    ///
    /// This must not fail, modulo entity representations being too small.
    fn emergency_slot(
        &mut self,
        mv: ParallelMove<E>,
        reason: ScratchReason,
        unavailable: &[ScalarAllocation<E>],
    ) -> Result<SpillSlot<E>, SolveError>;
}

/// How far along a move is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum State {
    /// Not emitted yet.
    Todo,

    /// On the path of the search for a move that sits on a cycle.
    ///
    /// Reaching a `Pending` move again means the search has gone all the way
    /// around a cycle. Only set while that search runs, and cleared again as
    /// soon as it finishes.
    Pending,

    /// Emitted.
    Done,
}

/// The `State` of every move in a batch, packed into two bits per move.
struct MoveStates {
    /// Bit `2 * i` is set once move `i` has been visited, and bit `2 * i + 1`
    /// once it has been placed. Neither is set for `Todo`, so a fresh batch
    /// needs no initialization.
    bits: EntitySet<StateBit>,
}

impl MoveStates {
    const fn new() -> Self {
        MoveStates {
            bits: EntitySet::new(),
        }
    }

    fn reset(&mut self) {
        let Self { bits } = self;
        bits.reset();
    }

    fn is_reset(&self) -> bool {
        let Self { bits } = self;
        bits.is_reset()
    }

    /// Get the `(visited, placed)` bits for `mv`, or `None` when they are too
    /// large to represent.
    fn try_bits<E>(mv: SeqMove<E>) -> Option<(StateBit, StateBit)>
    where
        E: EntityRepr,
    {
        let visited = mv.index().checked_mul(2)?;
        let placed = visited.checked_add(1)?;
        Some((StateBit::try_new(visited)?, StateBit::try_new(placed)?))
    }

    fn bits<E>(m: SeqMove<E>) -> (StateBit, StateBit)
    where
        E: EntityRepr,
    {
        Self::try_bits(m).unwrap()
    }

    /// Get the state of the given move.
    fn get<E>(&self, m: SeqMove<E>) -> State
    where
        E: EntityRepr,
    {
        let (visited, placed) = Self::bits(m);
        if self.bits.contains(placed) {
            State::Done
        } else if self.bits.contains(visited) {
            State::Pending
        } else {
            State::Todo
        }
    }

    /// Set the given move's state.
    fn set<E>(&mut self, m: SeqMove<E>, state: State)
    where
        E: EntityRepr,
    {
        let (visited, placed) = Self::bits(m);
        match state {
            State::Todo => {
                self.bits.remove(visited);
                self.bits.remove(placed);
            }
            State::Pending => {
                self.bits.insert(visited);
                self.bits.remove(placed);
            }
            State::Done => {
                self.bits.insert(visited);
                self.bits.insert(placed);
            }
        }
    }
}

/// How many moves still stand in the way of each move in a batch.
struct MoveBlockers<E>
where
    E: EntityRepr,
{
    /// How many moves that have not been emitted yet still need to write the
    /// location each move reads.
    ///
    /// A move can only be emitted once this reaches zero.
    ///
    /// We emit in reverse program order, so a move is free to go as soon as
    /// everything that clobbers its source is out: those moves all run after
    /// this one, so the source still holds the value we want at the point
    /// this move lands.
    ///
    /// A count rather than a single blocker, because `overlaps` is not
    /// transitive. Say `r0` and `r1` are in the same bank, covering one unit
    /// each, and `r2` is in a different bank, covering both units (similar to
    /// aarch64's `d0`, `d1`, and `s0` registers):
    ///
    /// ```text
    /// +---------+
    /// |    r2   |
    /// +---------+
    /// | r0 | r1 |
    /// +---------+
    /// ```
    ///
    /// Here `r0` overlaps `r2` and `r2` overlaps `r1`, but `r0` does not
    /// overlap `r1`. So even though a batch names a destination at most once,
    /// its units can belong to several destinations, and a single source can
    /// be clobbered by more than one of the batch's writes.
    counts: SecondaryMap<SeqMove<E>, u32>,

    /// Where each move's last search for a blocker left off.
    ///
    /// This keeps `find` running in `O(n)` over `n` calls for a particular
    /// move, rather than `O(n)` each call and `O(n^2)` across `n` calls.
    ///
    /// Only ever touched while breaking a cycle, so this only grows its storage
    /// for the batches that actually need it.
    cursor: SecondaryMap<SeqMove<E>, u32>,
}

impl<E> MoveBlockers<E>
where
    E: EntityRepr,
{
    const fn new() -> Self {
        MoveBlockers {
            counts: SecondaryMap::new(0),
            cursor: SecondaryMap::new(0),
        }
    }

    fn reset(&mut self) {
        let Self { counts, cursor } = self;
        counts.reset();
        cursor.reset();
    }

    fn is_reset(&self) -> bool {
        let Self { counts, cursor } = self;
        counts.is_reset() && cursor.is_reset()
    }

    /// How many moves still have to write what `m` reads.
    fn get(&self, m: SeqMove<E>) -> u32 {
        self.counts[m]
    }

    /// Record that one of the writes `m` was waiting on is out.
    fn retire(&mut self, m: SeqMove<E>) {
        self.counts[m] -= 1;
    }

    /// Count, for each move, how many moves write the location it reads.
    fn count(
        &mut self,
        moves: &PrimaryMap<SeqMove<E>, ParallelMove<E>>,
        source: &impl ScratchSource<E>,
    ) {
        for (m, mv) in moves.iter() {
            let mut blockers = 0;
            for (other, other_mv) in moves.iter() {
                if other == m {
                    continue;
                }
                debug_assert!(
                    !(other > m && source.overlaps(mv.dst, other_mv.dst)),
                    "each location in a parallel move batch must be written by at most one \
                     move, but {mv:?} and {other_mv:?} both write it",
                );
                if source.overlaps(other_mv.dst, mv.src) {
                    blockers += 1;
                }
            }
            self.counts[m] = blockers;
        }
    }

    /// Find a move that has not yet been emitted and still needs to write what
    /// `m` reads.
    fn find(
        &mut self,
        m: SeqMove<E>,
        moves: &PrimaryMap<SeqMove<E>, ParallelMove<E>>,
        state: &MoveStates,
        source: &impl ScratchSource<E>,
    ) -> Option<SeqMove<E>> {
        let src = moves[m].src;

        let i = self.cursor[m];
        let mut i = usize::try_from(i).unwrap();

        let found = loop {
            if i == moves.len() {
                break None;
            }

            let other = SeqMove::try_new(i).unwrap();
            if other != m
                && state.get(other) != State::Done
                && source.overlaps(moves[other].dst, src)
            {
                break Some(other);
            }

            i += 1;
        };

        // Stop at the blocker, not past it: it is still a blocker until it
        // retires.
        self.cursor[m] = u32::try_from(i).unwrap();

        found
    }
}

/// The scratch locations the walk has available, and the bookkeeping necessary
/// to reload any evictions that we spilled to get them.
struct ScratchPool<E>
where
    E: EntityRepr,
{
    /// The scratch locations currently holding a value, which nothing else may
    /// take until the move that fills them in is emitted.
    unavailable: Vec<ScalarAllocation<E>>,

    /// Registers the batch is already finished with, which we can hand out as
    /// scratch without consulting the caller.
    available: Vec<Reg<E>>,

    /// The same registers as `available`, as a set, so we can test membership
    /// with a bit instead of a scan. `available` keeps the order, which decides
    /// what `allocate` hands out.
    available_set: RegSet,

    /// The registers we evicted under a wide bracket, and where we put what
    /// they were holding.
    ///
    /// Each entry needs a spill at the start and a reload at the end of a
    /// batch.
    wide_evictions: Vec<(Reg<E>, SpillSlot<E>)>,

    /// The slots a value has sat in only temporarily during this batch: a
    /// tight-bracket eviction, or a value parked for cycle breaking.
    ///
    /// This is in contrast to the slots for wide-bracket evictions, which hold
    /// values across the whole batch.
    tight_or_parked_slots: Vec<SpillSlot<E>>,

    /// Where `ScratchSource::evict` writes what it had to evict, and where a
    /// tight bracket's spills wait until the moves they wrap are emitted.
    evicting: Vec<(Reg<E>, SpillSlot<E>)>,

    /// The registers the batch is done with, as handed to
    /// `ScratchSource::evict`.
    spent: Vec<Reg<E>>,

    /// The destinations of every move still waiting to be emitted.
    ///
    /// This is sorted, so that `is_spent` can ask about one endpoint without
    /// rescanning the batch.
    filled_later: Vec<ScalarAllocation<E>>,
}

impl<E> ScratchPool<E>
where
    E: EntityRepr,
{
    const fn new() -> Self {
        ScratchPool {
            unavailable: Vec::new(),
            available: Vec::new(),
            available_set: RegSet::new(),
            wide_evictions: Vec::new(),
            tight_or_parked_slots: Vec::new(),
            evicting: Vec::new(),
            spent: Vec::new(),
            filled_later: Vec::new(),
        }
    }

    fn reset(&mut self) {
        let Self {
            unavailable,
            available,
            available_set,
            wide_evictions,
            tight_or_parked_slots,
            evicting,
            spent,
            filled_later,
        } = self;
        unavailable.clear();
        available.clear();
        available_set.reset();
        wide_evictions.clear();
        tight_or_parked_slots.clear();
        evicting.clear();
        spent.clear();
        filled_later.clear();
    }

    fn is_reset(&self) -> bool {
        let Self {
            unavailable,
            available,
            available_set,
            wide_evictions,
            tight_or_parked_slots,
            evicting,
            spent,
            filled_later,
        } = self;
        unavailable.is_empty()
            && available.is_empty()
            && available_set.is_empty()
            && wide_evictions.is_empty()
            && tight_or_parked_slots.is_empty()
            && evicting.is_empty()
            && spent.is_empty()
            && filled_later.is_empty()
    }

    /// Hand out a register from the pool to stand in for `mv`, if one there
    /// will do.
    ///
    /// A pooled register is ours for free, while asking the client for a new
    /// scratch may cost an eviction, so this goes first.
    ///
    /// `touched_by_unemitted` reports whether any move still waiting to be
    /// emitted reads or writes a location.
    fn allocate<S>(
        &self,
        mv: ParallelMove<E>,
        reason: ScratchReason,
        source: &mut S,
        touched_by_unemitted: impl Fn(ScalarAllocation<E>, &S) -> bool,
    ) -> Option<Reg<E>>
    where
        S: ScratchSource<E>,
    {
        self.available.iter().copied().find(|&reg| {
            let scratch = ScalarAllocation::Reg(reg);

            // Somewhere a broken cycle's value is already sitting.
            if self
                .unavailable
                .iter()
                .any(|&s| source.overlaps(scratch, s))
            {
                return false;
            }

            // An end of the very move we are standing in for. The park
            // `src -> t` and the staging pair `src -> t; t -> dst` are
            // ordinary moves, and no machine can copy between two locations
            // that partially overlap, while a copy between locations that
            // overlap exactly does nothing at all.
            if source.overlaps(scratch, mv.src) || source.overlaps(scratch, mv.dst) {
                return false;
            }

            // A cycle break holds its scratch across the moves we have yet to
            // emit. That nothing writes the register is not enough: a move
            // merely reading it would read the parked value instead of its
            // own. A staged pair runs nothing in between.
            if reason == ScratchReason::CycleBreak && touched_by_unemitted(scratch, &*source) {
                return false;
            }

            source.is_suitable(mv, reason, reg)
        })
    }

    /// Record that `scratch` is holding a value, so that nothing else takes it
    /// until `deallocate` hands it back.
    fn hold(&mut self, scratch: ScalarAllocation<E>) {
        self.unavailable.push(scratch);
    }

    /// Hand back a scratch taken by `hold`, its value having been read out.
    fn deallocate(&mut self, scratch: ScalarAllocation<E>) {
        self.unavailable.retain(|&s| s != scratch);
    }

    /// Fold one emitted move into the pool: its destination enters, its source
    /// leaves.
    ///
    /// Both halves fall out of emitting in reverse: everything still to be
    /// emitted runs earlier than `mv`, so `mv` overwrites its destination
    /// after all of them, and reads its source after all of them.
    ///
    /// A location that left the pool can come back, which is correct rather
    /// than a leak: coming back takes a move that writes it, emitted later and
    /// so running earlier, and that write shields every use past it.
    fn note_emitted(&mut self, mv: ParallelMove<E>, source: &impl ScratchSource<E>) {
        match mv.src {
            ScalarAllocation::Reg(_) => {
                self.available.retain(|&reg| {
                    let remove = source.overlaps(reg.into(), mv.src);
                    if remove {
                        self.available_set.remove(reg.with_repr32());
                    }
                    !remove
                });
            }

            ScalarAllocation::Stack(_) => debug_assert!(
                self.available
                    .iter()
                    .all(|&reg| !source.overlaps(reg.into(), mv.src)),
                "a register overlaps a stack slot, so skipping the scan for a \
                 stack source leaves a register pooled that should have left",
            ),
        }

        if let ScalarAllocation::Reg(reg) = mv.dst {
            if self.available_set.insert(reg.with_repr32()) {
                self.available.push(reg);
            }
        }
    }

    /// Whether `loc` is holding a value `deallocate` has yet to hand back.
    fn is_held(&self, loc: ScalarAllocation<E>) -> bool {
        self.unavailable.contains(&loc)
    }

    /// The registers held for the whole batch, and the slots they are in.
    fn wide_evictions(&self) -> impl Iterator<Item = (Reg<E>, SpillSlot<E>)> {
        self.wide_evictions.iter().copied()
    }

    /// Record that `slot` holds a value for part of the batch, so that a wide
    /// eviction, which is open across all of it, does not also take the slot.
    fn note_temporary_slot(&mut self, slot: SpillSlot<E>) {
        // Only the debug assertions read this, so only they pay for it.
        if cfg!(debug_assertions) {
            self.tight_or_parked_slots.push(slot);
        }
    }

    /// Note every destination a move still waiting to be emitted will fill in,
    /// so that `is_spent` can ask about one endpoint without rescanning the
    /// batch.
    fn note_pending_destinations(&mut self, dsts: impl Iterator<Item = ScalarAllocation<E>>) {
        debug_assert!(self.filled_later.is_empty());
        self.filled_later.extend(dsts);
        self.filled_later.sort_unstable();
    }

    /// Whether a move we have yet to emit delivers a value into `loc`.
    fn is_filled_later(&self, loc: ScalarAllocation<E>) -> bool {
        self.filled_later.binary_search(&loc).is_ok()
    }

    /// Forget what `note_pending_destinations` recorded.
    fn forget_pending_destinations(&mut self) {
        self.filled_later.clear();
    }

    /// Drop what only lives for the length of the emission walk.
    ///
    /// The wide evictions stay: `ParallelMoveSolver::solve` still owes each of
    /// them a reload, and those go out after the walk is over.
    fn end_walk(&mut self) {
        self.unavailable.clear();
        self.available.clear();
        self.available_set.reset();
        self.evicting.clear();
    }

    /// Take the wide tail of the evictions into `wide_evictions`, leaving the
    /// tight ones behind for the caller to close its bracket around.
    fn hold_wide_evictions(&mut self, tight: usize) {
        self.wide_evictions
            .extend_from_slice(&self.evicting[tight..]);
        self.evicting.truncate(tight);
    }
}

/// Sequentializes batches of parallel moves.
pub struct ParallelMoveSolver<E>
where
    E: EntityRepr,
{
    /// The batch being solved, with self-moves already dropped.
    moves: PrimaryMap<SeqMove<E>, ParallelMove<E>>,

    /// How far along each move is.
    state: MoveStates,

    /// What each move is still waiting on.
    blockers: MoveBlockers<E>,

    /// Scratch space for the search for a move that sits on a cycle.
    stack: Vec<SeqMove<E>>,

    /// The scratch location holding the source of each move that a cycle break
    /// has parked and that has not read it back out yet.
    parked: SecondaryMap<SeqMove<E>, Option<ScalarAllocation<E>>>,

    /// The destinations of the moves a cycle break has rewritten.
    ///
    /// Breaking a cycle points its member at a scratch instead, so `moves` no
    /// longer names where the value really goes. That destination has already
    /// been written by the half we emitted, and everything still to come runs
    /// ahead of it, so a reload placed after the whole batch would land right
    /// on top of it. We remember it and never widen a bracket around it.
    rewritten_destinations: Vec<ScalarAllocation<E>>,

    /// The scratch locations we can hand out, and what we owe for the ones we
    /// took.
    pool: ScratchPool<E>,
}

impl<E> Default for ParallelMoveSolver<E>
where
    E: EntityRepr,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<E> ParallelMoveSolver<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        ParallelMoveSolver {
            moves: PrimaryMap::new(),
            state: MoveStates::new(),
            blockers: MoveBlockers::new(),
            stack: Vec::new(),
            parked: SecondaryMap::new(None),
            rewritten_destinations: Vec::new(),
            pool: ScratchPool::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            moves,
            state,
            blockers,
            stack,
            parked,
            rewritten_destinations,
            pool,
        } = self;
        moves.reset();
        state.reset();
        blockers.reset();
        stack.clear();
        parked.reset();
        rewritten_destinations.clear();
        pool.reset();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            moves,
            state,
            blockers,
            stack,
            parked,
            rewritten_destinations,
            pool,
        } = self;
        moves.is_reset()
            && state.is_reset()
            && blockers.is_reset()
            && stack.is_empty()
            && parked.is_reset()
            && rewritten_destinations.is_empty()
            && pool.is_reset()
    }

    /// Sequentialize `moves`, appending them to `out` in emission order.
    ///
    /// Leaves whatever `out` already contained in place, only appends.
    ///
    /// Internally we solve back to front, since a move is free to go once
    /// everything that clobbers its source has been emitted, and flip the
    /// result at the end. `out` is always in program order on return.
    ///
    /// `source` is where scratch locations come from, and is the only thing
    /// here that knows anything about the machine; see `ScratchSource`.
    pub fn solve<S>(
        &mut self,
        moves: impl IntoIterator<Item = ParallelMove<E>>,
        source: &mut S,
        out: &mut Vec<ParallelMove<E>>,
    ) -> Result<(), SolveError>
    where
        S: ScratchSource<E>,
    {
        // We solve back to front, so `out` comes out of `solve_inner` in
        // reverse program order. Flip just the range we appended; whatever the
        // caller already had in there stays put.
        let base = out.len();

        let result = self.solve_inner(moves, source, out);
        match result {
            // Reset `out` so that we don't confuse callers by leaving
            // half-finished solutions behind.
            Err(_) => out.truncate(base),

            Ok(()) => {
                out[base..].reverse();

                // The reloads for everything evicted for the whole duration of
                // the batch.
                for (reg, slot) in self.pool.wide_evictions() {
                    out.push(ParallelMove::reload(slot, reg));
                }
            }
        }

        self.reset();
        result
    }

    fn solve_inner<S>(
        &mut self,
        moves: impl IntoIterator<Item = ParallelMove<E>>,
        source: &mut S,
        out: &mut Vec<ParallelMove<E>>,
    ) -> Result<(), SolveError>
    where
        S: ScratchSource<E>,
    {
        debug_assert!(self.is_reset());

        for m in moves {
            // Ignore self-moves.
            //
            // Under partial overlap, "overlaps" is weaker than "is the same
            // location". But a value belongs to a single bank, so we never
            // move between banks, and registers within a bank never partially
            // overlap. So this check suffices.
            if source.overlaps(m.src, m.dst) {
                continue;
            }

            // The move needs both an index and a pair of state bits.
            let representable = match SeqMove::<E>::try_new(self.moves.len()) {
                Some(m) => MoveStates::try_bits(m).is_some(),
                None => false,
            };
            if !representable {
                return Err(SolveError::EntityReprTooSmall);
            }
            self.moves.push_unwrap(m);
        }

        self.blockers.count(&self.moves, source);
        self.emit_moves(source, out)
    }

    /// Record that `writer` is finished.
    ///
    /// Because we emit in reverse, everything emitted from here on runs before
    /// `writer` does, so `dst` will never be clobbered ahead of them again:
    /// every move waiting to read it is one blocker closer to being free to do
    /// so.
    fn retire_write(
        &mut self,
        writer: SeqMove<E>,
        dst: ScalarAllocation<E>,
        source: &impl ScratchSource<E>,
    ) {
        for mv in self.moves.keys() {
            if mv == writer || self.state.get(mv) == State::Done {
                continue;
            }
            if source.overlaps(dst, self.moves[mv].src) {
                self.blockers.retire(mv);
            }
        }
    }

    /// Append `mv` to the output, routing it through a scratch register when
    /// it moves memory to memory, which no machine can do in one instruction.
    fn push_move<S>(
        &mut self,
        mv: ParallelMove<E>,
        emit: &mut Emit<'_, E, S>,
    ) -> Result<(), SolveError>
    where
        S: ScratchSource<E>,
    {
        if !mv.is_stack_to_stack() {
            emit.push(mv);
            return Ok(());
        }

        let (via, is_tight_bracketed) = self.take_scratch(mv, ScratchReason::StackToStack, emit)?;
        debug_assert!(matches!(via, ScalarAllocation::Reg(_)));

        emit.push(mv.with_src(via));
        emit.push(mv.with_dst(via));

        // Emit the spills for anything that was evicted to free up `via` for us.
        if is_tight_bracketed {
            emit.close_tight_brackets();
        }

        Ok(())
    }

    /// Does any move we have yet to emit read or write `loc`?
    fn touched_by_unemitted<S>(&self, loc: ScalarAllocation<E>, source: &S) -> bool
    where
        S: ScratchSource<E>,
    {
        self.moves.iter().any(|(m, mv)| {
            self.state.get(m) != State::Done
                && (source.overlaps(loc, mv.src) || source.overlaps(loc, mv.dst))
        })
    }

    /// Is `loc` holding nothing of its own from here on out? I.e. nothing
    /// anyone still reads, and no payload from a move that runs earlier?
    fn is_spent<S>(&self, loc: ScalarAllocation<E>, emit: &mut Emit<'_, E, S>) -> bool
    where
        S: ScratchSource<E>,
    {
        // A move we have yet to emit executes before this point in the batch,
        // so it already delivered its value into `loc` by this execution point,
        // and overwriting `loc` now would throw that value away.
        if emit.pool.is_filled_later(loc) {
            return false;
        }

        // Walking what we have emitted back to front walks forward through
        // the program from the point we are at. A write of `loc` shields
        // everything past it, so we can stop there; a read we reach before
        // any such write is a value we would be destroying.
        for mv in emit.out[emit.base..].iter().rev() {
            // Identity, not overlap, because this method asks whether this
            // `loc` itself is still in use or not.
            if mv.src == loc {
                return false;
            }
            if mv.dst == loc {
                break;
            }
        }

        !emit.pool.is_held(loc)
    }

    /// Collect the registers the batch is finished with, for
    /// `ScratchSource::evict`'s `spent` argument.
    fn collect_spent<S>(&self, spent: &mut Vec<Reg<E>>, emit: &mut Emit<'_, E, S>)
    where
        S: ScratchSource<E>,
    {
        debug_assert!(spent.is_empty());
        spent.extend_from_slice(&emit.pool.available);

        emit.pool.note_pending_destinations(
            self.moves
                .iter()
                .filter(|&(m, _)| self.state.get(m) != State::Done)
                .map(|(_, mv)| mv.dst),
        );

        for i in 0..self.moves.len() {
            let m = SeqMove::try_new(i).unwrap();
            for loc in [self.moves[m].src, self.moves[m].dst] {
                let ScalarAllocation::Reg(reg) = loc else {
                    continue;
                };
                if !spent.contains(&reg) && self.is_spent(loc, emit) {
                    spent.push(reg);
                }
            }
        }

        emit.pool.forget_pending_destinations();
    }

    /// Get a scratch location for `mv`, climbing the ladder of
    /// `ScratchSource` until something answers.
    ///
    /// If any values were evicted to free up the returned scratch, they are
    /// recorded in `emit.pool.evicting`.
    ///
    /// The `bool` member of the result tuple is whether there are any
    /// tight-bracketed evictions for this scratch or not. Callers are
    /// responsible for emitting spills of tight-bracketed evictions. Spills for
    /// wide-bracketed evictions are emitted at the end of the solving the whole
    /// batch.
    fn take_scratch<S>(
        &self,
        mv: ParallelMove<E>,
        reason: ScratchReason,
        emit: &mut Emit<'_, E, S>,
    ) -> Result<(ScalarAllocation<E>, bool), SolveError>
    where
        S: ScratchSource<E>,
    {
        emit.pool.evicting.clear();

        // First, try to find a scratch register we can use for free.
        if let Some(reg) = self.find_free_scratch(mv, reason, emit) {
            let scratch = ScalarAllocation::Reg(reg);
            self.debug_assert_untaken_scratch_is_sound(scratch, mv, reason, emit);
            return Ok((scratch, false));
        }

        // Second, see whether we can temporarily evict a value to free up its
        // register as a scratch.
        if let Some(reg) = self.make_scratch_via_eviction(mv, reason, emit)? {
            self.debug_assert_scratch_fits_move(reg.into(), mv, emit);
            self.debug_assert_held_scratch_is_free(reg.into(), reason, emit);

            let num_tight = self.partition_evictions(emit);
            self.debug_assert_eviction_is_sound(reg, reason, num_tight, emit);
            self.record_evictions(num_tight, emit);
            return Ok((reg.into(), num_tight > 0));
        };

        // As a last resort, spill to an emergency slot.
        let scratch = self.make_scratch_via_emergency_spill(mv, reason, emit)?;
        self.debug_assert_untaken_scratch_is_sound(scratch, mv, reason, emit);
        Ok((scratch, false))
    }

    /// Find a scratch register we can use for free, without evicting anything.
    fn find_free_scratch<S>(
        &self,
        mv: ParallelMove<E>,
        reason: ScratchReason,
        emit: &mut Emit<'_, E, S>,
    ) -> Option<Reg<E>>
    where
        S: ScratchSource<E>,
    {
        // Try to reuse a register from this batch...
        emit.pool
            .allocate(mv, reason, emit.source, |loc, source| {
                self.touched_by_unemitted(loc, source)
            })
            // ... or, failing that, ask the client if they have a free register
            // we can use as a scratch.
            .or_else(|| emit.source.find_free(mv, reason, &emit.pool.unavailable))
    }

    /// Try to free up a scratch register by evicting whatever value(s) are
    /// currently stored in its register units.
    ///
    /// The evictions are left in `emit.pool.evicting`.
    fn make_scratch_via_eviction<S>(
        &self,
        mv: ParallelMove<E>,
        reason: ScratchReason,
        emit: &mut Emit<'_, E, S>,
    ) -> Result<Option<Reg<E>>, SolveError>
    where
        S: ScratchSource<E>,
    {
        let mut spent = mem::take(&mut emit.pool.spent);
        self.collect_spent(&mut spent, emit);

        let victim = emit.source.evict(
            mv,
            reason,
            &mut emit.pool.unavailable,
            &spent,
            &mut emit.pool.evicting,
        );

        spent.clear();
        emit.pool.spent = spent;
        victim
    }

    /// Create a new emergency spill slot for use as a scratch location.
    ///
    /// This is only used when breaking a whole-bank cycle: we can't get a
    /// scratch register via eviction, since every register must be live across
    /// the whole cycle.
    ///
    /// And this can't be used to break a stack-to-stack move, because it
    /// returns another stack location. That is fine, however, because we can
    /// always evict for stack-to-stack moves, as the evictions are
    /// tight-bracketed around just the stack-to-register and register-to-stack
    /// moves that stack-to-stack moves get broken up into.
    fn make_scratch_via_emergency_spill<S>(
        &self,
        mv: ParallelMove<E>,
        reason: ScratchReason,
        emit: &mut Emit<'_, E, S>,
    ) -> Result<ScalarAllocation<E>, SolveError>
    where
        S: ScratchSource<E>,
    {
        debug_assert_eq!(
            reason,
            ScratchReason::CycleBreak,
            "staging a move from one slot to another always has a register to take, \
             busy or not, but no register came back for {mv:?}",
        );
        debug_assert!(
            emit.pool.evicting.is_empty(),
            "declining to evict evicts nothing, but {:?} came back with it",
            emit.pool.evicting,
        );

        let slot = emit
            .source
            .emergency_slot(mv, reason, &emit.pool.unavailable)?;
        emit.pool.note_temporary_slot(slot);

        Ok(ScalarAllocation::Stack(slot))
    }

    /// Sort the evictions so that the ones needing a tight bracket come
    /// first, and report how many that is.
    fn partition_evictions<S>(&self, emit: &mut Emit<'_, E, S>) -> usize
    where
        S: ScratchSource<E>,
    {
        let mut num_tight = 0;
        for i in 0..emit.pool.evicting.len() {
            let loc = ScalarAllocation::Reg(emit.pool.evicting[i].0);

            // A location that is a source or destination (or overlaps a
            // destination) in this batch must be tight-bracketed, or else we
            // might spill before the location has its final value.
            let is_in_batch = self
                .moves
                .values()
                .any(|&mv| mv.src == loc || mv.dst == loc || emit.source.overlaps(loc, mv.dst));

            // Same for rewritten move-cycle destinations.
            let is_rewritten = self
                .rewritten_destinations
                .iter()
                .any(|&dst| emit.source.overlaps(loc, dst));

            // An unavailable location is currently holding a value for this
            // batch, so we must tight-bracket its eviction, so that the rest of
            // the batch still sees its value.
            let is_unavailable = emit.pool.unavailable.contains(&loc);

            if is_in_batch || is_rewritten || is_unavailable {
                emit.pool.evicting.swap(num_tight, i);
                num_tight += 1;
            }
        }

        num_tight
    }

    /// Record information about the evictions we made when freeing up a scratch
    /// register.
    ///
    /// Emits the reloads for tight-bracketed evictions, and notes the
    /// wide-bracketed evictions for later.
    fn record_evictions<S>(&self, num_tight: usize, emit: &mut Emit<'_, E, S>)
    where
        S: ScratchSource<E>,
    {
        // Tight-bracketed evictions get their reloads emitted now, right after
        // the moves they wrap.
        //
        // No two tight-brackted evictions' registers overlap, so order doesn't
        // matter.
        for i in 0..num_tight {
            let (other, slot) = emit.pool.evicting[i];
            emit.push(ParallelMove::reload(slot, other));
            emit.pool.note_temporary_slot(slot);
        }

        // Wide-bracketed evictions are deferred until after processing the
        // whole batch.
        emit.pool.hold_wide_evictions(num_tight);
    }

    /// Lend the pool to an `Emit` for the length of the walk, and run it.
    fn emit_moves<S>(
        &mut self,
        source: &mut S,
        out: &mut Vec<ParallelMove<E>>,
    ) -> Result<(), SolveError>
    where
        S: ScratchSource<E>,
    {
        let mut pool = mem::replace(&mut self.pool, ScratchPool::new());

        let mut emit = Emit {
            base: out.len(),
            out,
            pool: &mut pool,
            source,
        };

        let result = emit.emit_all(self);

        pool.end_walk();
        self.pool = pool;
        result
    }

    /// Break a cycle among the moves that have not been emitted yet.
    ///
    /// Splits one cycle member in two around a scratch location. Because we
    /// emit in reverse, the half that reads the scratch is the one we can emit
    /// right now: it writes the member's destination, which frees whichever
    /// move was waiting to read what that clobbers, and so unsticks the cycle.
    /// The member itself stays in the batch, rewritten to write the scratch
    /// instead, and is emitted ahead of the half we just pushed, once
    /// everything that clobbers its source is out.
    ///
    /// Its blocker count carries over untouched, since it still reads the same
    /// source, and no other move's count changes either, because its new
    /// destination is a scratch nothing in the batch touches.
    fn break_cycle<S>(&mut self, emit: &mut Emit<'_, E, S>) -> Result<(), SolveError>
    where
        S: ScratchSource<E>,
    {
        let cur = self.find_cycle(emit);
        let break_at = self.choose_break_point(cur);

        let mv = self.moves[break_at];
        let (scratch, is_tight_bracketed) =
            self.take_scratch(mv, ScratchReason::CycleBreak, emit)?;
        debug_assert!(
            !is_tight_bracketed,
            "a cycle break holds its scratch across other moves, so it can never take \
             one that is already in use",
        );

        // The scratch holds a value from here until the park move fills it in,
        // so nothing else may take it in the meantime, including the scratch
        // `push_move` is about to ask for.
        emit.pool.hold(scratch);

        self.split_move(break_at, mv, scratch, emit)
    }

    /// Walk from a stuck move until the walk meets itself, and report where.
    ///
    /// Leaves the path through the cycle on `self.stack`, marked `Pending`.
    fn find_cycle<S>(&mut self, emit: &mut Emit<'_, E, S>) -> SeqMove<E>
    where
        S: ScratchSource<E>,
    {
        let stuck = self
            .moves
            .keys()
            .find(|&m| self.state.get(m) != State::Done)
            .expect("only called while moves are left to emit");

        let mut cur = self
            .blockers
            .find(stuck, &self.moves, &self.state, emit.source)
            .expect("a move that is waiting has something to wait for");

        // We walk to the back edge, rather than stopping at the first cycle
        // member we see, to maximize the tail of moves that breaking unblocks.
        debug_assert!(self.stack.is_empty());
        while self.state.get(cur) != State::Pending {
            self.state.set(cur, State::Pending);
            self.stack.push(cur);
            cur = self
                .blockers
                .find(cur, &self.moves, &self.state, emit.source)
                .expect("every move in a batch that is stuck has a blocker");
        }

        cur
    }

    /// Pick which member of the cycle `find_cycle` left on the stack to break
    /// at, and clear the stack.
    fn choose_break_point(&mut self, cur: SeqMove<E>) -> SeqMove<E> {
        let mut break_at = cur;

        // Prefer a member whose source is already in a register. Either way the
        // breaking the cycle costs two moves, but this way only one of the two
        // touches memory.
        //
        // `cur` unblocks the longest tail, so we keep it if we can, and iterate
        // in reverse to continue maximizing the tail of moves we unblock, while
        // avoiding extra stack moves.
        if !matches!(self.moves[cur].src, ScalarAllocation::Reg(_)) {
            for m in self.stack.iter().rev().copied() {
                if matches!(self.moves[m].src, ScalarAllocation::Reg(_)) {
                    break_at = m;
                    break;
                }
                if m == cur {
                    // Past the cycle and into the tail that leads to it, whose
                    // moves are not on it and so cannot break it.
                    break;
                }
            }
        }

        for m in self.stack.drain(..) {
            self.state.set(m, State::Todo);
        }

        break_at
    }

    /// Split `mv` in two around `scratch`.
    fn split_move<S>(
        &mut self,
        break_at: SeqMove<E>,
        mv: ParallelMove<E>,
        scratch: ScalarAllocation<E>,
        emit: &mut Emit<'_, E, S>,
    ) -> Result<(), SolveError>
    where
        S: ScratchSource<E>,
    {
        // Push the half that reads back out from the scratch and writes it to
        // the destination now, because we emit in reverse.
        self.push_move(mv.with_src(scratch), emit)?;

        // And with that, we're now done writing to the destination, so we can
        // free up anything waiting on it.
        self.retire_write(break_at, mv.dst, emit.source);

        // Rewrite the first half that reads from the original source to write
        // into the scratch location, and let it be emitted as any other move
        // otherwise would be.
        self.rewritten_destinations.push(mv.dst);
        self.moves[break_at].dst = scratch;
        self.parked[break_at] = Some(scratch);

        Ok(())
    }

    /// Debug assert that taking a register that is already in use is sound.
    fn debug_assert_tight_eviction_is_sound<S>(
        &self,
        reg: Reg<E>,
        reason: ScratchReason,
        num_tight: usize,
        emit: &mut Emit<'_, E, S>,
    ) where
        S: ScratchSource<E>,
    {
        if !cfg!(debug_assertions) {
            return;
        }

        debug_assert_eq!(
            reason,
            ScratchReason::StackToStack,
            "only a staged memory-to-memory move may take a register we are already \
             using, because only its two halves are adjacent enough to bracket, but \
             {reg:?} came back for a cycle break",
        );

        let tight_evictions = &emit.pool.evicting[..num_tight];

        self.debug_assert_evictions_are_disjoint(tight_evictions, &*emit.source);

        for &(_, slot) in tight_evictions.iter() {
            let slot = ScalarAllocation::Stack(slot);

            for &mv in self.moves.values() {
                debug_assert!(
                    !emit.source.overlaps(slot, mv.src) && !emit.source.overlaps(slot, mv.dst),
                    "the slot an evicted register sits in must not be one the batch names, \
                     but {slot:?} overlaps {mv:?}",
                );
            }

            for &(_, other) in emit.pool.wide_evictions.iter() {
                let other = ScalarAllocation::Stack(other);
                debug_assert!(
                    !emit.source.overlaps(slot, other),
                    "each outstanding eviction needs a slot of its own, but {slot:?} \
                     overlaps {other:?}",
                );
            }

            // The mirror of the `tight_or_parked_slots` check the wide bracket
            // makes. A park is holding a value from before this bracket opens
            // until after it closes, so however short this stay is, it is a
            // stay inside the park's, and saving here writes over what the
            // park is keeping for a move still to come.
            for &other in emit.pool.unavailable.iter() {
                debug_assert!(
                    !emit.source.overlaps(slot, other),
                    "the slot an evicted register sits in must not be one a broken cycle \
                     is parked in, but {slot:?} overlaps {other:?}",
                );
            }
        }
    }

    /// Debug assert that no two registers we evicted share a unit.
    ///
    /// Their reloads run one after another with nothing in between, and each
    /// loses whatever was in every register it shares a unit with, so two that
    /// overlap would have the second undo the first. This holds because each
    /// of the evicted holds a value of its own across the same span, and two
    /// values live at once are never put where they tread on each other.
    fn debug_assert_evictions_are_disjoint<S>(
        &self,
        evictions: &[(Reg<E>, SpillSlot<E>)],
        source: &S,
    ) where
        S: ScratchSource<E>,
    {
        if !cfg!(debug_assertions) {
            return;
        }

        for (i, &(reg, _)) in evictions.iter().enumerate() {
            for &(other, _) in &evictions[i + 1..] {
                debug_assert!(
                    !source.overlaps(reg.into(), other.into()),
                    "two evicted registers must not share a unit, but {reg:?} \
                     overlaps {other:?}",
                );
            }
        }
    }

    /// Debug assert that a register we are taking outright, evicting
    /// nothing, really is nobody's.
    fn debug_assert_scratch_is_unnamed<S>(&self, reg: Reg<E>, emit: &mut Emit<'_, E, S>)
    where
        S: ScratchSource<E>,
    {
        if !cfg!(debug_assertions) {
            return;
        }

        let scratch = ScalarAllocation::Reg(reg);

        for &mv in self.moves.values() {
            debug_assert!(
                !emit.source.overlaps(scratch, mv.src) && !emit.source.overlaps(scratch, mv.dst),
                "an evicted scratch register must not be named by the batch, but \
                 {scratch:?} overlaps {mv:?}",
            );
        }

        for &(other, _) in &emit.pool.wide_evictions {
            debug_assert!(
                !emit.source.overlaps(scratch, other.into()),
                "two evicted scratch registers must not overlap, but {scratch:?} \
                 overlaps {other:?}",
            );
        }
    }

    /// Debug assert that our wide-bracket evictions are sound.
    ///
    /// The batch must not name one of their locations: the spill would capture
    /// whatever was there before the batch filled it in, and the reload would
    /// arrive after the batch had already read it. Merely sharing a unit with a
    /// named register is fine as long as the batch does not write there. Nor
    /// may two of the eviction locations overlap, here or against an
    /// outstanding eviction, since the later reload would undo the earlier.
    fn debug_assert_wide_eviction_is_sound<S>(&self, num_tight: usize, emit: &mut Emit<'_, E, S>)
    where
        S: ScratchSource<E>,
    {
        if !cfg!(debug_assertions) {
            return;
        }

        let wide = &emit.pool.evicting[num_tight..];

        self.debug_assert_evictions_are_disjoint(wide, &*emit.source);

        for &(reg, _) in wide.iter() {
            let scratch = ScalarAllocation::Reg(reg);

            for &mv in self.moves.values() {
                debug_assert!(
                    mv.src != scratch && mv.dst != scratch,
                    "a register evicted for the length of the batch must not be one \
                     the batch names, but {mv:?} names {scratch:?}",
                );
                debug_assert!(
                    !emit.source.overlaps(scratch, mv.dst),
                    "a register evicted for the length of the batch must not share a \
                     unit with anything the batch writes, but {scratch:?} overlaps the \
                     destination of {mv:?}",
                );
            }

            for &(other, _) in emit.pool.wide_evictions.iter() {
                debug_assert!(
                    !emit.source.overlaps(scratch, other.into()),
                    "two evicted scratch registers must not overlap, but {scratch:?} \
                     overlaps {other:?}",
                );
            }

            for &dst in &self.rewritten_destinations {
                debug_assert!(
                    !emit.source.overlaps(scratch, dst),
                    "a register evicted for the length of the batch must not share a \
                     unit with where a broken cycle has already put its value, but \
                     {scratch:?} overlaps {dst:?}",
                );
            }
        }

        // The slots have to last the whole batch as well, so nothing in the
        // batch and no other outstanding eviction may be using one.
        for &(_, slot) in wide.iter() {
            let slot = ScalarAllocation::Stack(slot);

            for &mv in self.moves.values() {
                debug_assert!(
                    !emit.source.overlaps(slot, mv.src) && !emit.source.overlaps(slot, mv.dst),
                    "the slot an evicted register sits in must not be one the batch names, \
                     but {slot:?} overlaps {mv:?}",
                );
            }

            for &(_, other) in emit.pool.wide_evictions.iter() {
                let other = ScalarAllocation::Stack(other);
                debug_assert!(
                    !emit.source.overlaps(slot, other),
                    "each outstanding eviction needs a slot of its own, but {slot:?} \
                     overlaps {other:?}",
                );
            }

            // A slot something else sat in for part of the batch is a slot
            // the batch writes, and this bracket is open across the whole
            // batch: that write lands on top of what we put here, and the
            // reload at the end takes it back out in its place.
            for &other in emit.pool.tight_or_parked_slots.iter() {
                let other = ScalarAllocation::Stack(other);
                debug_assert!(
                    !emit.source.overlaps(slot, other),
                    "a slot evicted for the length of the batch must be one nothing \
                     else in the batch puts anything in, but {slot:?} overlaps {other:?}, \
                     which a bracket closing inside the batch or a parked cycle has \
                     already used",
                );
            }
        }
    }

    /// Debug assert that a scratch a cycle break will hold is nobody else's.
    ///
    /// The park writes the register and the broken move reads it back much
    /// later, so every move landing in between, which is every move we have yet
    /// to emit, has to leave it alone.
    ///
    /// A staged memory-to-memory move is exempt: its two halves are adjacent,
    /// so nothing lands in between.
    fn debug_assert_held_scratch_is_free<S>(
        &self,
        scratch: ScalarAllocation<E>,
        reason: ScratchReason,
        emit: &mut Emit<'_, E, S>,
    ) where
        S: ScratchSource<E>,
    {
        if !cfg!(debug_assertions) || reason != ScratchReason::CycleBreak {
            return;
        }

        debug_assert!(
            !self.touched_by_unemitted(scratch, emit.source),
            "a scratch held across a broken cycle must be one no move we have yet to \
             emit reads or writes, but {scratch:?} is not",
        );
    }

    /// Debug assert that a scratch is somewhere this move's value can go.
    fn debug_assert_scratch_fits_move<S>(
        &self,
        scratch: ScalarAllocation<E>,
        mv: ParallelMove<E>,
        emit: &mut Emit<'_, E, S>,
    ) where
        S: ScratchSource<E>,
    {
        if !cfg!(debug_assertions) {
            return;
        }

        let source = &mut *emit.source;
        for end in [mv.src, mv.dst] {
            debug_assert!(
                !source.overlaps(scratch, end),
                "a scratch must be disjoint from both ends of the move it stands \
                 in for, but {scratch:?} overlaps {end:?} of {mv:?}",
            );
        }
    }

    /// Debug assert that a scratch we are about to use really is free.
    fn debug_assert_scratch_is_free<S>(
        &self,
        scratch: ScalarAllocation<E>,
        emit: &mut Emit<'_, E, S>,
    ) where
        S: ScratchSource<E>,
    {
        if !cfg!(debug_assertions) {
            return;
        }

        let Emit {
            out,
            base,
            pool,
            source,
        } = emit;

        // Nothing we have yet to emit may clobber the scratch. Those moves all
        // run earlier than the use we are about to make of it, so they would
        // overwrite what we are putting in it before anything reads it back.
        for (m, mv) in self.moves.iter() {
            debug_assert!(
                self.state.get(m) == State::Done || !source.overlaps(scratch, mv.dst),
                "a scratch location must not be clobbered by a move we have yet to emit \
                 -- and which therefore runs earlier -- but {scratch:?} overlaps the \
                 destination of {mv:?}",
            );
        }

        // And nothing already emitted may still need what is in it. Emission
        // order is reverse program order, so walking what we have emitted back
        // to front walks forward through the program from the point our use of
        // the scratch lands at. A write of the scratch shields everything past
        // it, so we can stop there; a read we reach before any such write is a
        // value we would be destroying.
        for mv in out[*base..].iter().rev() {
            debug_assert!(
                !source.overlaps(scratch, mv.src),
                "a scratch location must not hold a value that a move we have already \
                 emitted -- and which therefore runs later -- still has to read, but \
                 {scratch:?} overlaps the source of {mv:?}",
            );
            if source.overlaps(scratch, mv.dst) {
                break;
            }
        }

        for &other in pool.unavailable.iter() {
            debug_assert!(
                !source.overlaps(scratch, other),
                "a scratch location must not overlap one that is already holding a value, \
                 but {scratch:?} overlaps {other:?}",
            );
        }
    }

    /// Debug assert that a scratch we took without evicting anything is
    /// sound.
    ///
    /// The same three checks whether it came from the pool, from the source,
    /// or from a slot at the bottom of the ladder: nothing was moved out of
    /// the way for any of them, so all three ask only that the location was
    /// nobody's to begin with.
    fn debug_assert_untaken_scratch_is_sound<S>(
        &self,
        scratch: ScalarAllocation<E>,
        mv: ParallelMove<E>,
        reason: ScratchReason,
        emit: &mut Emit<'_, E, S>,
    ) where
        S: ScratchSource<E>,
    {
        self.debug_assert_scratch_fits_move(scratch, mv, emit);
        self.debug_assert_scratch_is_free(scratch, emit);
        self.debug_assert_held_scratch_is_free(scratch, reason, emit);
    }

    /// Debug assert that an eviction and the brackets we chose for it are
    /// sound.
    fn debug_assert_eviction_is_sound<S>(
        &self,
        reg: Reg<E>,
        reason: ScratchReason,
        num_tight: usize,
        emit: &mut Emit<'_, E, S>,
    ) where
        S: ScratchSource<E>,
    {
        if !cfg!(debug_assertions) {
            return;
        }

        for (i, &(other, _)) in emit.pool.evicting.iter().enumerate() {
            if let Some(predicted) = emit.source.predicted_tight(other, &emit.pool.unavailable) {
                debug_assert_eq!(
                    i < num_tight,
                    predicted,
                    "the bracket width we chose for {other:?} must be the one the \
                     source predicted",
                );
            }
        }

        if self.debug_only_scratch_in_use(reg, emit) || num_tight > 0 {
            self.debug_assert_tight_eviction_is_sound(reg, reason, num_tight, emit);
        } else {
            self.debug_assert_scratch_is_free(reg.into(), emit);
            self.debug_assert_scratch_is_unnamed(reg, emit);
        }
        self.debug_assert_wide_eviction_is_sound(num_tight, emit);
    }

    /// Is anything still looking at `reg`: the batch, a parked cycle, or an
    /// eviction we have yet to close?
    fn debug_only_scratch_in_use<S>(&self, reg: Reg<E>, emit: &mut Emit<'_, E, S>) -> bool
    where
        S: ScratchSource<E>,
    {
        assert!(cfg!(debug_assertions));

        let reg = ScalarAllocation::Reg(reg);

        self.moves
            .values()
            .any(|&mv| emit.source.overlaps(reg, mv.src) || emit.source.overlaps(reg, mv.dst))
            || emit
                .pool
                .unavailable
                .iter()
                .any(|&s| emit.source.overlaps(reg, s))
            || emit
                .pool
                .wide_evictions
                .iter()
                .any(|&(other, _)| emit.source.overlaps(reg, other.into()))
    }
}

/// What a move does to the pool of registers we can hand out as scratch, and
/// so the order the ready set is drained in: what gains us one, then what
/// costs us nothing, then what spends one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Tier {
    /// Both ends in registers: takes one out of the pool and puts one back.
    Gains,

    /// Reads a slot. Costs the pool nothing whatever it writes, and hands us
    /// a register when it writes one.
    Spares,

    /// Reads a register and writes a slot: the one shape that spends a
    /// register and gives nothing back.
    Spends,
}

/// Why parallel-move solving is asking for a scratch location.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
pub enum ScratchReason {
    /// To break a cycle.
    ///
    /// The scratch will park a value across other moves, so it must be
    /// untouched for the rest of the batch, and there is no way to go on
    /// without one.
    CycleBreak,

    /// To stage a move from memory to memory, which machines cannot typically
    /// do in one instruction.
    StackToStack,
}

/// The mutable side state and the callbacks that the emission walk threads
/// through everything it does.
///
/// Bundled up so the walk can hold all of it across a `&mut` borrow of the
/// solver, and so giving the walk one more thing to carry does not widen half
/// a dozen signatures.
struct Emit<'a, E, S>
where
    E: EntityRepr,
{
    /// Where the sequentialized moves go.
    ///
    /// Everything before `base` belongs to the caller. Everything from there
    /// on is this batch, in reverse program order.
    out: &'a mut Vec<ParallelMove<E>>,

    /// Where this batch's moves start in `out`.
    base: usize,

    /// The scratch locations we can hand out, and what we owe for the ones we
    /// took.
    pool: &'a mut ScratchPool<E>,

    /// Where scratch locations come from, and the only thing here that knows
    /// anything about the machine.
    source: &'a mut S,
}

impl<E, S> Emit<'_, E, S>
where
    E: EntityRepr,
    S: ScratchSource<E>,
{
    /// Emit all unblocked moves, break the next extant cycle, and repeat until
    /// all of `solver`'s moves have been emitted.
    fn emit_all(&mut self, solver: &mut ParallelMoveSolver<E>) -> Result<(), SolveError> {
        debug_assert!(solver.parked.is_reset());
        debug_assert!(self.pool.unavailable.is_empty());
        debug_assert!(self.pool.available.is_empty());
        debug_assert!(self.pool.evicting.is_empty());

        let mut remaining = solver.moves.len();
        while remaining > 0 {
            // Emit everything nothing is waiting on, and keep going while that
            // keeps working: emitting a move retires its own write, which might
            // free the move that was waiting to read what it clobbered, etc...
            let num_emitted = self.emit_unblocked(solver)?;
            if num_emitted > 0 {
                remaining -= num_emitted;
                continue;
            }

            // Nothing could be emitted, so every move still pending is part of
            // some cycle. Break it.
            solver.break_cycle(self)?;
        }

        // Spill wide-bracketed evictions. These go out last, so they execute
        // first, before the register is clobbered. The matching reloads are
        // emitted after the reversal, in `solve`. Their order among themselves
        // does not matter, since they cannot overlap by contract.
        for i in 0..self.pool.wide_evictions.len() {
            let (reg, slot) = self.pool.wide_evictions[i];
            self.push(ParallelMove::spill(reg, slot));
        }

        Ok(())
    }

    /// Emit every move that nothing is waiting on any more, and report how many
    /// that was.
    ///
    /// Register-to-register moves go first and go until exhausted: they cost
    /// nothing and hand us a register for the pool, which is what lets a move
    /// between two slots, the only kind that must have a scratch, be served
    /// for free. It is a priority within the ready set rather than a phase,
    /// since refusing stack moves outright would stall the moment one blocked
    /// a register move.
    ///
    /// A move that reads a register and gives none back is held to the end for
    /// the mirror reason: emitting it retires its source from the pool for
    /// good, while holding it back leaves the register spent the whole time.
    fn emit_unblocked(&mut self, solver: &mut ParallelMoveSolver<E>) -> Result<usize, SolveError> {
        let mut placed = 0;

        // Placing one of these can unblock another, so repeat until the supply
        // of both is exhausted.
        loop {
            let n = self.emit_unblocked_tier(solver, Tier::Gains)?
                + self.emit_unblocked_tier(solver, Tier::Spares)?;
            if n == 0 {
                break;
            }
            placed += n;
        }

        Ok(placed + self.emit_unblocked_tier(solver, Tier::Spends)?)
    }

    /// One pass over the pending moves, emitting the ready ones of one tier.
    fn emit_unblocked_tier(
        &mut self,
        solver: &mut ParallelMoveSolver<E>,
        tier: Tier,
    ) -> Result<usize, SolveError> {
        let mut num_emitted = 0;

        for m in solver.moves.keys() {
            if solver.state.get(m) == State::Done || solver.blockers.get(m) != 0 {
                continue;
            }
            if solver.moves[m].tier() != tier {
                continue;
            }

            self.emit_move(solver, m)?;
            num_emitted += 1;

            // If this was a parked move, it has just written its value into
            // the scratch, which the already-emitted move that reads the
            // scratch back out consumes. Nothing else needs it now.
            //
            // Go through `get_mut` rather than indexing, so that a batch that
            // never parks anything does not grow the map.
            if let Some(scratch) = solver.parked.get_mut(m).and_then(Option::take) {
                self.pool.deallocate(scratch);
            }
        }

        Ok(num_emitted)
    }

    /// Emit `m` and retire the write it was holding off.
    fn emit_move(
        &mut self,
        solver: &mut ParallelMoveSolver<E>,
        m: SeqMove<E>,
    ) -> Result<(), SolveError> {
        debug_assert_eq!(solver.blockers.get(m), 0);

        let mv = solver.moves[m];
        solver.state.set(m, State::Done);

        solver.push_move(mv, self)?;
        solver.retire_write(m, mv.dst, self.source);
        Ok(())
    }

    /// Emit the saves for the tight brackets the pool is holding open, which
    /// closes them.
    fn close_tight_brackets(&mut self) {
        let mut evicting = mem::take(&mut self.pool.evicting);
        for (other, slot) in evicting.drain(..) {
            self.push(ParallelMove::spill(other, slot));
        }
        self.pool.evicting = evicting;
    }

    /// Push one machine move, and fold it into the scratch pool.
    fn push(&mut self, mv: ParallelMove<E>) {
        self.out.push(mv);
        self.pool.note_emitted(mv, &*self.source);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Reg, SpillSlot,
        test::{TestLocation, TestMachineShape, TestMove, TestParallelMoves, TestScratchPolicy},
    };
    use core::{
        ops::{Range, RangeInclusive},
        sync::atomic::{AtomicUsize, Ordering},
    };
    use mutatis::{
        check::{Check, CheckResult},
        mutators as m,
    };
    use std::{format, string::String, vec, vec::Vec};

    fn reg(name: u8) -> TestLocation {
        TestLocation::Reg(name)
    }

    fn slot(index: u8) -> TestLocation {
        TestLocation::Slot(index)
    }

    fn mv(src: TestLocation, dst: TestLocation) -> TestMove {
        TestMove { src, dst }
    }

    /// A model machine with no aliasing: every name covers a unit of its own.
    fn distinct_regs() -> Vec<u8> {
        TestParallelMoves::disjoint_regs(&TestMachineShape::default())
    }

    fn batch(moves: Vec<TestMove>) -> TestParallelMoves {
        TestParallelMoves::new(distinct_regs(), moves, TestScratchPolicy::Free)
    }

    /// Solve `moves`, panicking with whatever property it violated, and
    /// report how many moves came out and whether a scratch was wanted.
    #[track_caller]
    fn solve(moves: &TestParallelMoves) -> (usize, bool) {
        match moves.check() {
            Ok(outcome) => (outcome.emitted, outcome.wanted_scratch),
            Err(e) => panic!("{e}"),
        }
    }

    /// Every move's two state bits must be its own.
    #[test]
    fn move_states_are_independent() {
        let moves: Vec<SeqMove<u32>> = (0..5).map(|i| SeqMove::try_new(i).unwrap()).collect();

        let mut states = MoveStates::new();
        for &m in &moves {
            assert_eq!(states.get(m), State::Todo);
        }

        for state in [State::Pending, State::Done, State::Todo] {
            for (i, &m) in moves.iter().enumerate() {
                states.set(m, state);
                assert_eq!(states.get(m), state);
                for (j, &other) in moves.iter().enumerate() {
                    if j != i {
                        assert_eq!(states.get(other), State::Todo, "{other:?} was clobbered");
                    }
                }
                states.set(m, State::Todo);
            }
        }

        assert!(states.is_reset());
        states.set(moves[3], State::Done);
        assert!(!states.is_reset());
        states.reset();
        assert!(states.is_reset());
        assert_eq!(states.get(moves[3]), State::Todo);
    }

    #[test]
    fn empty() {
        assert_eq!(solve(&batch(vec![])), (0, false));
    }

    /// A move that reads what it writes is already done.
    #[test]
    fn self_move() {
        assert_eq!(solve(&batch(vec![mv(reg(0), reg(0))])), (0, false));
    }

    /// And so is one that reads and writes the same location under two names.
    #[test]
    fn aliased_self_move() {
        let moves = TestParallelMoves::new(
            vec![0, 0],
            vec![mv(reg(0), reg(1))],
            TestScratchPolicy::Free,
        );
        assert_eq!(moves.moves().len(), 1, "the move survives the fixup");
        assert_eq!(solve(&moves), (0, false));
    }

    /// A chain has one order that works: writing `r1` before `r2 := r1` has
    /// read it would lose a value.
    #[test]
    fn chain() {
        let moves = batch(vec![mv(reg(0), reg(1)), mv(reg(1), reg(2))]);
        assert_eq!(solve(&moves), (2, false));
    }

    /// The same chain, already in a working order.
    #[test]
    fn chain_already_ordered() {
        let moves = batch(vec![mv(reg(1), reg(2)), mv(reg(0), reg(1))]);
        assert_eq!(solve(&moves), (2, false));
    }

    /// A swap is the smallest cycle: two moves become three.
    #[test]
    fn swap() {
        let moves = batch(vec![mv(reg(0), reg(1)), mv(reg(1), reg(0))]);
        assert_eq!(solve(&moves), (3, true));
    }

    #[test]
    fn three_cycle() {
        let moves = batch(vec![
            mv(reg(0), reg(1)),
            mv(reg(1), reg(2)),
            mv(reg(2), reg(0)),
        ]);
        assert_eq!(solve(&moves), (4, true));
    }

    /// Two cycles in one batch, which have to take turns using the scratch.
    #[test]
    fn two_disjoint_cycles() {
        let moves = batch(vec![
            mv(reg(0), reg(1)),
            mv(reg(1), reg(0)),
            mv(reg(2), reg(3)),
            mv(reg(3), reg(2)),
        ]);
        assert_eq!(solve(&moves), (6, true));
    }

    /// A chain feeding a cycle: its move must happen before the cycle is
    /// disturbed, though the walk reaches it first.
    #[test]
    fn chain_into_cycle() {
        let moves = batch(vec![
            mv(reg(0), reg(1)),
            mv(reg(1), reg(0)),
            mv(reg(0), reg(2)),
        ]);
        assert_eq!(solve(&moves), (4, true));
    }

    /// A cycle the walk descends into rather than starting on.
    #[test]
    fn cycle_reached_from_chain() {
        let moves = batch(vec![
            mv(reg(0), reg(2)),
            mv(reg(0), reg(1)),
            mv(reg(1), reg(0)),
        ]);
        assert_eq!(solve(&moves), (4, true));
    }

    /// Spills and reloads mix in like any other move, and never form a cycle,
    /// as a value has one stack home.
    #[test]
    fn spills_and_reloads() {
        let moves = batch(vec![
            mv(slot(0), reg(0)),
            mv(reg(0), reg(1)),
            mv(reg(1), slot(1)),
        ]);
        assert_eq!(solve(&moves), (3, false));
    }

    /// Names 0 and 1 are one register, so this is a swap written under three
    /// names, which is what `overlaps` is for.
    #[test]
    fn aliased_swap() {
        let moves = TestParallelMoves::new(
            vec![0, 0, 2],
            vec![mv(reg(0), reg(2)), mv(reg(2), reg(1))],
            TestScratchPolicy::Free,
        );
        assert_eq!(moves.moves().len(), 2);
        assert_eq!(solve(&moves), (3, true));
    }

    /// Two moves writing one location leave the batch undefined, so the fixup
    /// drops the second.
    #[test]
    fn fixup_drops_aliased_destination() {
        let moves = TestParallelMoves::new(
            vec![0, 0],
            vec![mv(reg(0), reg(0)), mv(reg(0), reg(1))],
            TestScratchPolicy::Free,
        );
        assert_eq!(moves.moves().len(), 1);
    }

    /// A cycle with no free register to break it still gets broken: the
    /// caller evicts one, and the solver saves and restores it around the
    /// batch.
    #[test]
    fn a_cycle_breaks_into_an_evicted_register() {
        let moves = TestParallelMoves::new(
            distinct_regs(),
            vec![mv(reg(0), reg(1)), mv(reg(1), reg(0))],
            TestScratchPolicy::Evict,
        );
        let outcome = moves.check().unwrap();
        assert!(outcome.wanted_scratch);
        assert!(outcome.evicted);
        // The swap's three moves, plus the save and the reload.
        assert_eq!(outcome.emitted, 5);
    }

    /// A batch with no cycle never asks for a scratch, so nothing is
    /// evicted.
    #[test]
    fn no_scratch_needed() {
        let moves = TestParallelMoves::new(
            distinct_regs(),
            vec![mv(reg(0), reg(1)), mv(reg(1), reg(2))],
            TestScratchPolicy::Evict,
        );
        let outcome = moves.check().unwrap();
        assert!(!outcome.wanted_scratch);
        assert!(!outcome.evicted);
        assert_eq!(outcome.emitted, 2);
    }

    fn allocation(loc: TestLocation) -> ScalarAllocation<u32> {
        match loc {
            TestLocation::Reg(name) => {
                ScalarAllocation::Reg(Reg::try_new(usize::from(name)).unwrap())
            }
            TestLocation::Slot(index) => {
                ScalarAllocation::Stack(SpillSlot::try_new(usize::from(index)).unwrap())
            }
        }
    }

    fn parallel_move(src: TestLocation, dst: TestLocation) -> ParallelMove<u32> {
        ParallelMove {
            src: allocation(src),
            dst: allocation(dst),
            val: None,
        }
    }

    /// A `ScratchSource` for the unit tests, recording everything it is
    /// offered and everything it is asked for.
    ///
    /// It never gets further down the ladder than `find_free`; eviction and
    /// parking on the stack belong to the oracle in
    /// `crate::test::parallel_moves`, which has a model machine to check them
    /// against.
    struct ModelSource {
        /// The machine's overlap model: `partially_aliasing` for the aliasing
        /// one, `|a, b| a == b` for a flat one.
        overlaps: fn(ScalarAllocation<u32>, ScalarAllocation<u32>) -> bool,

        /// Whether to approve the registers the solver offers from its own
        /// pool. Off unless a test says otherwise, so that a test sees exactly
        /// the `find_free` calls it would make with no pool to draw on. The
        /// pool has tests of its own.
        use_pool: bool,

        /// The name `find_free` answers with, given why it was asked.
        free: fn(ScratchReason) -> u8,

        /// Names for `find_free` to answer with in turn, ahead of `free`.
        free_in_turn: Vec<u8>,

        /// Every pooled register we were offered.
        offered: Vec<(ParallelMove<u32>, ScratchReason, Reg<u32>)>,

        /// Every scratch we were asked for: the move, the reason, what we
        /// answered, and what was already parked at the time.
        asked: Vec<(
            ParallelMove<u32>,
            ScratchReason,
            Reg<u32>,
            Vec<ScalarAllocation<u32>>,
        )>,
    }

    impl ModelSource {
        fn new(overlaps: fn(ScalarAllocation<u32>, ScalarAllocation<u32>) -> bool) -> Self {
            ModelSource {
                overlaps,
                use_pool: false,
                free: |_| unreachable!("this batch must not need a scratch register"),
                free_in_turn: Vec::new(),
                offered: Vec::new(),
                asked: Vec::new(),
            }
        }

        fn free(mut self, free: fn(ScratchReason) -> u8) -> Self {
            self.free = free;
            self
        }

        fn free_in_turn(mut self, names: &[u8]) -> Self {
            self.free_in_turn = names.to_vec();
            self
        }

        fn with_pool(mut self) -> Self {
            self.use_pool = true;
            self
        }
    }

    impl ScratchSource<u32> for ModelSource {
        fn overlaps(&self, a: ScalarAllocation<u32>, b: ScalarAllocation<u32>) -> bool {
            (self.overlaps)(a, b)
        }

        fn is_suitable(
            &mut self,
            mv: ParallelMove<u32>,
            reason: ScratchReason,
            reg: Reg<u32>,
        ) -> bool {
            self.offered.push((mv, reason, reg));
            self.use_pool
        }

        fn find_free(
            &mut self,
            mv: ParallelMove<u32>,
            reason: ScratchReason,
            unavailable: &[ScalarAllocation<u32>],
        ) -> Option<Reg<u32>> {
            let name = if self.free_in_turn.is_empty() {
                (self.free)(reason)
            } else {
                self.free_in_turn.remove(0)
            };
            let reg = Reg::try_new(usize::from(name)).unwrap();
            self.asked.push((mv, reason, reg, unavailable.to_vec()));
            Some(reg)
        }

        fn evict(
            &mut self,
            _: ParallelMove<u32>,
            _: ScratchReason,
            _: &[ScalarAllocation<u32>],
            _: &[Reg<u32>],
            _: &mut Vec<(Reg<u32>, SpillSlot<u32>)>,
        ) -> Result<Option<Reg<u32>>, SolveError> {
            unreachable!("`find_free` always answers, so nothing here evicts")
        }

        fn emergency_slot(
            &mut self,
            _: ParallelMove<u32>,
            _: ScratchReason,
            _: &[ScalarAllocation<u32>],
        ) -> Result<SpillSlot<u32>, SolveError> {
            unreachable!("`find_free` always answers, so nothing here parks on the stack")
        }
    }

    /// How many scratch registers `cells` leaves room for, and how many cells
    /// it lays out in all.
    const NUM_MODEL_SCRATCHES: usize = 2;
    const NUM_MODEL_CELLS: usize = 3 + NUM_MODEL_SCRATCHES * 2 + 3 * 2;

    /// Enough cells for register names `r0..=r6` in a batch that names no
    /// slot, where the names past the two scratches are free to run on past
    /// where the slots would have started.
    const NUM_MODEL_CELLS_WITHOUT_SLOTS: usize = 3 + 6 * 2;

    /// A model machine whose banks alias partially, one cell per register
    /// unit: `r0` is units `0..1`, `r1` is `1..3` and `r2` is `0..2`, so `r2`
    /// overlaps both `r0` and `r1` while those two, being in one bank, are
    /// disjoint. Registers above `r2` are scratches, and they and the spill
    /// slots sit off on their own, overlapping nothing else.
    fn cells(loc: ScalarAllocation<u32>) -> Range<usize> {
        match loc {
            ScalarAllocation::Reg(reg) => match reg.index() {
                0 => 0..1,
                1 => 1..3,
                2 => 0..2,
                n => 3 + (n - 3) * 2..5 + (n - 3) * 2,
            },
            ScalarAllocation::Stack(slot) => {
                let base = 3 + NUM_MODEL_SCRATCHES * 2 + slot.index() * 2;
                base..base + 2
            }
        }
    }

    fn partially_aliasing(a: ScalarAllocation<u32>, b: ScalarAllocation<u32>) -> bool {
        let (a, b) = (cells(a), cells(b));
        a.start < b.end && b.start < a.end
    }

    /// A source can be covered by two destinations that do not overlap each
    /// other: `r2` spans both `r0` and `r1`, so the move reading `r2` has to
    /// come before both of the writes. Nothing here is circular, so it needs
    /// no scratch to do it.
    #[test]
    fn a_source_covered_by_two_disjoint_destinations() {
        let mut out = Vec::new();
        let mut source = ModelSource::new(partially_aliasing);
        ParallelMoveSolver::new()
            .solve(
                [
                    parallel_move(reg(2), slot(0)),
                    parallel_move(slot(1), reg(0)),
                    parallel_move(slot(2), reg(1)),
                ],
                &mut source,
                &mut out,
            )
            .unwrap();

        assert!(source.asked.is_empty(), "this batch needs no scratch");

        // The two writes are independent of each other, so either order of
        // them is correct; all that matters is that the read comes first.
        let at = |mv| out.iter().position(|&o| o == mv).expect("move was emitted");
        let read = at(parallel_move(reg(2), slot(0)));
        assert_eq!(out.len(), 3, "no move should be split or duplicated");
        assert!(
            read < at(parallel_move(slot(1), reg(0))) && read < at(parallel_move(slot(2), reg(1))),
            "reading `r2` must come before both of the writes that cover it, got {out:?}",
        );
    }

    /// Partial overlap lets two cycles share a move, and then breaking one of
    /// them does not free the other: both scratch locations are holding a
    /// value at the same time, so the second must not be the first.
    ///
    /// `r2` covers `r0` and `r1`, so `slot1 := r0` and `slot0 := r2` are each
    /// half of what `r0 := slot1` and `r1 := slot0` overwrite.
    #[test]
    fn two_cycle_breaks_are_live_at_once() {
        let mut out = Vec::new();
        let mut source = ModelSource::new(partially_aliasing).free_in_turn(&[3, 4]);
        ParallelMoveSolver::new()
            .solve(
                [
                    parallel_move(reg(0), slot(1)),
                    parallel_move(slot(1), reg(1)),
                    parallel_move(reg(2), slot(0)),
                    parallel_move(slot(0), reg(0)),
                ],
                &mut source,
                &mut out,
            )
            .unwrap();

        let asked = &source.asked;
        assert_eq!(asked.len(), 2, "two cycles, two breaks");
        for &(_, _, scratch, ref parked) in asked {
            assert!(
                parked
                    .iter()
                    .all(|&a| !partially_aliasing(ScalarAllocation::Reg(scratch), a)),
                "the solver must not hand out a scratch that is already in use",
            );
        }
        assert!(
            asked[0].3.is_empty() && asked[1].3.len() == 1,
            "the first break is still parked when the second is asked for: {asked:?}",
        );

        // Run the emitted sequence on the model machine to check the order
        // really does deliver every value.
        let mut state: Vec<usize> = (0..NUM_MODEL_CELLS).collect();
        for m in &out {
            let (src, dst) = (cells(m.src), cells(m.dst));
            for (i, cell) in dst.enumerate() {
                state[cell] = state[src.start + i];
            }
        }
        for m in [
            parallel_move(reg(0), slot(1)),
            parallel_move(slot(1), reg(1)),
            parallel_move(reg(2), slot(0)),
            parallel_move(slot(0), reg(0)),
        ] {
            let (src, dst) = (cells(m.src), cells(m.dst));
            for (i, cell) in dst.enumerate() {
                assert_eq!(
                    state[cell],
                    src.start + i,
                    "{m:?} lost its value in {out:?}"
                );
            }
        }
    }

    /// A move from one slot to another comes back as a reload and a store
    /// through the scratch, in that order.
    #[test]
    fn stack_to_stack() {
        let mut out = Vec::new();
        let mut source = ModelSource::new(|a, b| a == b).free(|_| 3);
        ParallelMoveSolver::new()
            .solve([parallel_move(slot(0), slot(1))], &mut source, &mut out)
            .unwrap();

        assert_eq!(source.asked.len(), 1);
        assert_eq!(source.asked[0].0, parallel_move(slot(0), slot(1)));
        assert!(
            source.asked[0].3.is_empty(),
            "nothing else is live across this move",
        );
        assert_eq!(
            out,
            [
                parallel_move(slot(0), reg(3)),
                parallel_move(reg(3), slot(1)),
            ],
        );
    }

    /// The register a completed move wrote is dead to everything left, so the
    /// solver stages a move from one slot to another through it rather than
    /// asking for a scratch of its own.
    #[test]
    fn stack_to_stack_staged_through_the_pool() {
        let mut out = Vec::new();
        let mut source = ModelSource::new(|a, b| a == b).with_pool();
        ParallelMoveSolver::new()
            .solve(
                [
                    parallel_move(reg(0), reg(1)),
                    parallel_move(slot(0), slot(1)),
                ],
                &mut source,
                &mut out,
            )
            .unwrap();

        assert!(source.asked.is_empty(), "the pool should have covered this");
        assert_eq!(
            source.offered,
            [(
                parallel_move(slot(0), slot(1)),
                ScratchReason::StackToStack,
                Reg::try_new(1).unwrap(),
            )],
            "only `r1`, written by the move already out, is on offer",
        );

        // `r1` carries `slot0` to `slot1` first, and only then takes the value
        // it is the destination for.
        assert_eq!(
            out,
            [
                parallel_move(slot(0), reg(1)),
                parallel_move(reg(1), slot(1)),
                parallel_move(reg(0), reg(1)),
            ],
        );
    }

    /// The same for a cycle break: `r6` is finished with by the time the cycle
    /// needs somewhere to park, so the break costs the caller nothing.
    ///
    /// The cycle is between `r3` and `r4` rather than `r0` and `r1` because
    /// the model machine's low names have different widths, and a swap needs
    /// two of the same size.
    #[test]
    fn a_cycle_breaks_into_the_pool() {
        let mut out = Vec::new();
        let mut source = ModelSource::new(partially_aliasing).with_pool();
        ParallelMoveSolver::new()
            .solve(
                [
                    parallel_move(reg(3), reg(4)),
                    parallel_move(reg(4), reg(3)),
                    parallel_move(reg(5), reg(6)),
                ],
                &mut source,
                &mut out,
            )
            .unwrap();

        assert!(source.asked.is_empty(), "the pool should have covered this");
        assert!(
            source
                .offered
                .iter()
                .all(|&(_, reason, _)| reason == ScratchReason::CycleBreak),
            "the only scratch this batch wants is for the cycle: {:?}",
            source.offered,
        );
        assert_eq!(out.len(), 4, "three moves, one of them split by the break");

        // Run it on the model machine: the swap has to happen, and `r6` has to
        // come out holding `r5` and not the value it was lent for.
        let mut state: Vec<usize> = (0..NUM_MODEL_CELLS_WITHOUT_SLOTS).collect();
        for m in &out {
            let (src, dst) = (cells(m.src), cells(m.dst));
            for (i, cell) in dst.enumerate() {
                state[cell] = state[src.start + i];
            }
        }
        for m in [
            parallel_move(reg(3), reg(4)),
            parallel_move(reg(4), reg(3)),
            parallel_move(reg(5), reg(6)),
        ] {
            let (src, dst) = (cells(m.src), cells(m.dst));
            for (i, cell) in dst.enumerate() {
                assert_eq!(
                    state[cell],
                    src.start + i,
                    "{m:?} lost its value in {out:?}"
                );
            }
        }
    }

    /// Such a move inside a cycle needs a scratch of its own: the cycle is
    /// already parking a value in one.
    #[test]
    fn stack_to_stack_in_a_cycle() {
        let moves = batch(vec![
            mv(slot(0), slot(1)),
            mv(slot(1), reg(0)),
            mv(reg(0), slot(0)),
        ]);
        let outcome = moves.check().unwrap();
        assert!(outcome.routed_stack_to_stack);
        assert!(outcome.nested_scratch);
        // Three moves, one broken cycle, one expansion.
        assert_eq!(outcome.emitted, 5);
    }

    /// And with nothing free to route it through, a register is evicted
    /// for it: the move still comes back staged, never whole.
    #[test]
    fn a_stack_to_stack_move_stages_through_an_evicted_register() {
        let moves = TestParallelMoves::new(
            distinct_regs(),
            vec![mv(slot(0), slot(1))],
            TestScratchPolicy::Evict,
        );
        let outcome = moves.check().unwrap();
        assert!(outcome.routed_stack_to_stack);
        assert!(outcome.evicted);
        // The reload and the store, plus the save and reload around them.
        assert_eq!(outcome.emitted, 4);
    }

    /// A cycle whose every member reads a slot: the batch leaves the solver
    /// no register of its own to park in, so one is evicted.
    ///
    /// This is what move generation is left with when nothing is free, and it
    /// is an ordinary eviction like any other.
    #[test]
    fn a_cycle_of_stack_moves_evicts_a_register() {
        let moves = TestParallelMoves::new(
            distinct_regs(),
            vec![mv(slot(0), slot(1)), mv(slot(1), slot(0))],
            TestScratchPolicy::Evict,
        );
        let outcome = moves.check().unwrap();
        assert!(outcome.evicted);
        assert!(outcome.routed_stack_to_stack);
        // Two registers get evicted, one to park the cycle in and one to
        // stage the other member through, so the two moves come out as four,
        // wrapped in two saves and two reloads.
        assert_eq!(outcome.emitted, 8);
    }

    /// The same, for a cycle that also passes through a register.
    #[test]
    fn a_mixed_cycle_evicts_a_register() {
        let moves = TestParallelMoves::new(
            distinct_regs(),
            vec![
                mv(reg(0), slot(0)),
                mv(slot(0), slot(1)),
                mv(slot(1), reg(0)),
            ],
            TestScratchPolicy::Evict,
        );
        let outcome = moves.check().unwrap();
        assert!(outcome.evicted);
        // As above, with the cycle's third move added.
        assert_eq!(outcome.emitted, 9);
    }

    /// Given the choice, break a cycle where the source is already in a
    /// register: the half that reads the source becomes a register-to-register
    /// move, where breaking at a member that reads a slot would make it a
    /// load. Either way the cycle costs two moves; only one of them has to
    /// touch memory.
    #[test]
    fn cycle_breaks_where_the_source_is_in_a_register() {
        // reg0 -> slot0 -> slot1 -> reg0, with only one register source.
        let batch = [
            parallel_move(reg(0), slot(0)),
            parallel_move(slot(0), slot(1)),
            parallel_move(slot(1), reg(0)),
        ];
        let scratch = allocation(reg(3));

        let mut out = Vec::new();
        let mut source = ModelSource::new(|a, b| a == b).free(|reason| match reason {
            ScratchReason::CycleBreak => 3,
            ScratchReason::StackToStack => 2,
        });
        ParallelMoveSolver::new()
            .solve(batch, &mut source, &mut out)
            .unwrap();

        let broke_at: Vec<_> = source
            .asked
            .iter()
            .filter(|&&(_, reason, _, _)| reason == ScratchReason::CycleBreak)
            .map(|&(mv, ..)| mv)
            .collect();
        assert_eq!(
            broke_at,
            vec![parallel_move(reg(0), slot(0))],
            "the cycle should break at its one register source, so that reading \
             the parked value back costs no memory access",
        );
        assert_eq!(
            out[0],
            ParallelMove {
                src: allocation(reg(0)),
                dst: scratch,
                val: None,
            },
            "{out:?}",
        );
    }

    /// One solver, several batches: its scratch space must start each clean.
    #[test]
    fn solver_is_reusable() {
        let mut solver = ParallelMoveSolver::<u32>::new();
        let mut out = Vec::new();

        for _ in 0..3 {
            out.clear();
            let mut source = ModelSource::new(|a, b| a == b).free(|_| 3);
            solver
                .solve(
                    [parallel_move(reg(0), reg(1)), parallel_move(reg(1), reg(0))],
                    &mut source,
                    &mut out,
                )
                .unwrap();
            assert_eq!(out.len(), 3);
            assert!(solver.is_reset());
        }
    }

    /// Whatever is already in `out` is left alone.
    #[test]
    fn out_is_appended_to() {
        let mut solver = ParallelMoveSolver::<u32>::new();
        let already_there = parallel_move(slot(0), reg(3));
        let mut out = vec![already_there];

        let mut source = ModelSource::new(|a, b| a == b);
        solver
            .solve(
                [parallel_move(reg(0), reg(1)), parallel_move(reg(1), reg(2))],
                &mut source,
                &mut out,
            )
            .unwrap();

        assert_eq!(out.len(), 3);
        assert_eq!(out[0], already_there);
        // And our own tail is in emission order, not the reverse.
        assert_eq!(out[1], parallel_move(reg(1), reg(2)));
        assert_eq!(out[2], parallel_move(reg(0), reg(1)));
    }

    /// A batch can tie up a whole bank, and then a broken cycle has to wait on
    /// the stack rather than in a register.
    #[test]
    fn a_cycle_through_every_register_parks_on_the_stack() {
        let moves = TestParallelMoves::a_cycle_through_every_register();
        assert_eq!(moves.moves().len(), 2, "the fixup keeps both moves");

        let outcome = moves.check().unwrap();
        assert!(outcome.wanted_scratch, "a swap is a cycle to break");
        assert!(
            outcome.parked_on_the_stack,
            "with both registers in the cycle there is nowhere else to park",
        );
        assert!(
            !outcome.routed_stack_to_stack,
            "both ends of both moves are registers, so nothing is staged",
        );
    }

    /// The smallest machine can still swap its two slots.
    #[test]
    fn two_unit_machine_swaps_slots() {
        let moves = TestParallelMoves::a_two_unit_machine();
        assert_eq!(moves.moves().len(), 2, "the fixup keeps both moves");
        assert_eq!(moves.shape().num_units(), 2);
        assert_eq!(moves.shape().num_slots(), 2);

        let outcome = moves.check().unwrap();
        assert!(outcome.routed_wide_stack_to_stack);
        assert!(
            outcome.nested_scratch,
            "the second slot-to-slot move is inside the cycle the first one broke",
        );
    }

    /// Mutation resizes the model machine, and a resized machine must still
    /// hold the batch that was written for the old one: `fixup` is what
    /// brings the names, the slots and the move count back in range, and
    /// `check` is what says the result is still a batch the solver solves.
    #[test]
    fn a_mutated_machine_shape_stays_in_bounds() {
        let holds = |value: usize, range: RangeInclusive<u8>| {
            (usize::from(*range.start())..=usize::from(*range.end())).contains(&value)
        };

        let check = |moves: &TestParallelMoves, when: &str| {
            let shape = moves.shape();
            assert!(
                holds(shape.num_units(), TestMachineShape::UNITS),
                "{} register units {when}",
                shape.num_units(),
            );
            assert!(
                holds(shape.num_slots(), TestMachineShape::SLOTS),
                "{} spill slots {when}",
                shape.num_slots(),
            );
            assert!(
                holds(shape.max_moves(), TestMachineShape::MOVES),
                "a ceiling of {} moves {when}",
                shape.max_moves(),
            );

            let names = moves.regs().len();
            assert!(
                (1..=shape.max_reg_names()).contains(&names),
                "{names} register names {when}, on a machine that allows {}",
                shape.max_reg_names(),
            );
            assert!(
                moves.moves().len() <= shape.max_moves(),
                "{} moves {when}, on a machine that allows {}",
                moves.moves().len(),
                shape.max_moves(),
            );
            for m in moves.moves() {
                for loc in [m.src, m.dst] {
                    match loc {
                        TestLocation::Reg(name) => assert!(
                            usize::from(name) < names,
                            "a move names register {name} of {names} {when}",
                        ),
                        TestLocation::Slot(slot) => assert!(
                            usize::from(slot) < shape.num_slots(),
                            "a move names slot {slot} of {} {when}",
                            shape.num_slots(),
                        ),
                    }
                }
            }

            // And the batch still solves, which is what says the repaired
            // description is one the solver can be asked about at all.
            if let Err(e) = moves.check() {
                panic!("{e} ({when})");
            }
        };

        let mut moves = TestParallelMoves::a_two_unit_machine();
        check(&moves, "to begin with");

        let mut shapes = std::collections::HashSet::new();
        let mut session = mutatis::Session::new().seed(0);
        for i in 0..1_000 {
            session.mutate(&mut moves).unwrap();
            check(&moves, &format!("after mutation {i}"));
            shapes.insert(*moves.shape());
        }

        // Not a property of the solver; a check that the mutator really does
        // resize the machine, since a shape that never moved would make every
        // assertion above vacuous.
        assert!(
            shapes.len() > 1,
            "mutation never changed the shape of the machine",
        );
    }

    /// A register the batch has finished with is still no scratch for a move
    /// whose source it partially overlaps: parking that source into it would
    /// be a copy between two locations sharing some units but not all, which
    /// no machine can make in one move.
    ///
    /// `reg(1)` covers units `3..5`, which the writes to `reg(2)` (`2..4`) and
    /// `reg(7)` (`4..6`) destroy between them without touching each other, so
    /// the batch is a cycle the solver has to break. Emitting the move into
    /// `reg(7)` first returns `reg(7)` to the pool, and `reg(7)` is then the
    /// first register the break is offered, half of the very value it is being
    /// asked to park.
    #[test]
    fn a_pooled_scratch_never_overlaps_the_move_it_serves() {
        let moves = TestParallelMoves::a_scratch_that_halves_its_own_source();
        assert_eq!(moves.moves().len(), 3, "the fixup keeps all three moves");
        assert!(moves.has_a_source_covered_twice());

        let outcome = moves.check().unwrap();
        assert!(outcome.wanted_scratch, "the batch is a cycle");
    }

    /// A register the batch has finished with is no scratch for a cycle break
    /// if any move still to be emitted reads it. The pool's rule covers
    /// writes, since a move landing later in the program cannot clobber a
    /// scratch used earlier, but a break parks its value at the top of the
    /// batch and reads it back at the bottom, so everything in between must
    /// leave the register alone in both directions.
    ///
    /// `reg(3)` is the whole two-unit machine and `reg(1)` its upper half.
    /// Emitting `stack0 -> reg(1)` returns `reg(1)` to the pool, and the cycle
    /// between `reg(2)` and `stack4` is then broken into it, while
    /// `reg(3) -> stack7` is emitted afterwards and so runs between the park
    /// and the read-back, carrying the parked value out to memory.
    #[test]
    fn a_held_scratch_is_untouched_by_the_moves_around_it() {
        let moves = TestParallelMoves::a_scratch_read_out_from_under_a_cycle();
        assert_eq!(moves.moves().len(), 4, "the fixup keeps all four moves");

        let outcome = moves.check().unwrap();
        assert!(outcome.wanted_scratch, "the batch has a cycle in it");
    }

    /// The seed above really does park two values at once.
    #[test]
    fn two_cycles_break_at_once() {
        let moves = TestParallelMoves::two_concurrent_cycle_breaks();
        assert_eq!(moves.moves().len(), 3, "the fixup keeps all three moves");
        assert!(moves.has_a_source_covered_twice());

        let outcome = moves.check().unwrap();
        assert!(
            outcome.concurrent_scratches,
            "breaking the first cycle should not free the second",
        );
        // Three moves and two breaks.
        assert_eq!(outcome.emitted, 5);
    }

    /// A move between two wide slots routes through a wide scratch. Only the
    /// widths make this different from `stack_to_stack`, and they are what the
    /// interpreter's width check is there to catch.
    #[test]
    fn wide_stack_to_stack() {
        let moves = batch(vec![mv(slot(2), slot(3))]);
        assert_eq!(moves.moves().len(), 1, "both slots are two units wide");

        let outcome = moves.check().unwrap();
        assert!(outcome.routed_wide_stack_to_stack);
        assert_eq!(outcome.emitted, 2, "a store and a load through the scratch");
    }

    /// A source covered by two writes that do not cover each other has to be
    /// read before both of them. The whole batch solves with no scratch.
    #[test]
    fn a_source_covered_by_two_disjoint_writes() {
        let moves = TestParallelMoves::partially_aliasing_names();
        assert_eq!(moves.moves().len(), 3, "the fixup keeps all three moves");
        assert!(
            moves.has_a_source_covered_twice(),
            "the model machine can express partial overlap",
        );
        assert_eq!(solve(&moves), (3, false));
    }

    /// Solving a batch has the same effect as performing it all at once.
    ///
    /// `TestParallelMoves::check` is the property; this is the search for a
    /// batch that breaks it. Termination comes free: a solver that did not
    /// finish would hang here.
    #[test]
    fn parallel_move_properties() -> CheckResult<TestParallelMoves> {
        static SOLVED: AtomicUsize = AtomicUsize::new(0);
        static CYCLES: AtomicUsize = AtomicUsize::new(0);
        static EVICTED: AtomicUsize = AtomicUsize::new(0);
        static PARKED: AtomicUsize = AtomicUsize::new(0);
        static TRIVIAL: AtomicUsize = AtomicUsize::new(0);
        static STACK: AtomicUsize = AtomicUsize::new(0);
        static ROUTED: AtomicUsize = AtomicUsize::new(0);
        static NESTED: AtomicUsize = AtomicUsize::new(0);
        static PARTIAL: AtomicUsize = AtomicUsize::new(0);
        static CONCURRENT: AtomicUsize = AtomicUsize::new(0);
        static WIDE: AtomicUsize = AtomicUsize::new(0);
        static POOLED: AtomicUsize = AtomicUsize::new(0);

        let result = Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run_with(
                m::default::<TestParallelMoves>(),
                crate::test::parallel_moves_corpus(),
                |moves: &TestParallelMoves| -> Result<(), String> {
                    let outcome = moves.check()?;

                    if outcome.emitted > 0 {
                        SOLVED.fetch_add(1, Ordering::Relaxed);
                    }
                    if outcome.wanted_scratch {
                        CYCLES.fetch_add(1, Ordering::Relaxed);
                    }
                    if outcome.routed_stack_to_stack {
                        ROUTED.fetch_add(1, Ordering::Relaxed);
                    }
                    if outcome.nested_scratch {
                        NESTED.fetch_add(1, Ordering::Relaxed);
                    }
                    if outcome.routed_wide_stack_to_stack {
                        WIDE.fetch_add(1, Ordering::Relaxed);
                    }
                    if outcome.concurrent_scratches {
                        CONCURRENT.fetch_add(1, Ordering::Relaxed);
                    }
                    if outcome.used_pooled_scratch {
                        POOLED.fetch_add(1, Ordering::Relaxed);
                    }
                    if outcome.evicted {
                        EVICTED.fetch_add(1, Ordering::Relaxed);
                    }
                    if outcome.parked_on_the_stack {
                        PARKED.fetch_add(1, Ordering::Relaxed);
                    }
                    if outcome.non_trivial < moves.moves().len() {
                        TRIVIAL.fetch_add(1, Ordering::Relaxed);
                    }
                    if moves
                        .moves()
                        .iter()
                        .any(|m| matches!(m.src, TestLocation::Slot(_)))
                    {
                        STACK.fetch_add(1, Ordering::Relaxed);
                    }
                    if moves.has_a_source_covered_twice() {
                        PARTIAL.fetch_add(1, Ordering::Relaxed);
                    }

                    Ok(())
                },
            );

        // Not a property of the solver; a check that the search above was not
        // vacuous.
        for (what, count) in [
            ("batches that needed any move at all", &SOLVED),
            ("batches that wanted a scratch location", &CYCLES),
            ("batches that had to evict a register", &EVICTED),
            ("batches that had to park a cycle on the stack", &PARKED),
            ("batches holding a move that reads what it writes", &TRIVIAL),
            ("batches reloading from a spill slot", &STACK),
            ("batches moving one slot to another", &ROUTED),
            ("batches moving one slot to another inside a cycle", &NESTED),
            ("batches moving one wide slot to another", &WIDE),
            (
                "batches whose source is covered by two disjoint writes",
                &PARTIAL,
            ),
            (
                "batches breaking a second cycle while the first is parked",
                &CONCURRENT,
            ),
            (
                "batches taking a scratch from the solver's own pool",
                &POOLED,
            ),
        ] {
            assert!(
                count.load(Ordering::Relaxed) > 0,
                "the property test never saw any {what}",
            );
        }

        result
    }
}
