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

use crate::entity::{Entity as _, EntityRepr, EntitySet, PrimaryMap, SecondaryMap};
use crate::output::ScalarAllocation;
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
    pub src: ScalarAllocation<E>,

    /// The location written.
    pub dst: ScalarAllocation<E>,
}

/// Why a batch could not be sequentialized.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SolveError {
    /// A cycle had to be broken, but the caller had no scratch location to
    /// break it with.
    NoScratch,

    /// The batch had more moves than `E` can index.
    EntityReprTooSmall,
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

/// Sequentializes batches of parallel moves.
pub struct ParallelMoveSolver<E>
where
    E: EntityRepr,
{
    /// The batch being solved, with self-moves already dropped.
    moves: PrimaryMap<SeqMove<E>, ParallelMove<E>>,

    /// How far along each move is.
    state: MoveStates,

    /// How many moves that have not been emitted yet still need to read the
    /// location each move writes.
    ///
    /// A move can only be emitted once this reaches zero.
    ///
    /// We need to support multiple readers waiting, not just one, because our
    /// `overlaps` predicate is not transitive. Consider when we have `r0` and
    /// `r1` in the same bank, each covering one unit, and `r2` in a different
    /// bank, covering both units (this is similar to aarch64's `d0`, `d1`, and
    /// `s0` registers):
    ///
    /// ```text
    /// +---------+
    /// |    r2   |
    /// +---------+
    /// | r0 | r1 |
    /// +---------+
    /// ```
    ///
    /// In this case, we have `r0 overlaps r2` and `r2 overlaps r1`, but we do
    /// not have `r0 overlaps r1`.
    ///
    /// This means that, even though a whole destination is only named as a
    /// destination at most once in a move batch, its underlying units might be
    /// part of multiple destinations, and so we must perform all the moves that
    /// read those units before writing to a register that clobbers them.
    readers: SecondaryMap<SeqMove<E>, u32>,

    /// Where each move's last search for a blocker left off.
    ///
    /// This keeps `find_blocker` running in `O(n)` over `n` calls for a
    /// particular move, rather than `O(n)` each time.
    ///
    /// Only ever touched while breaking a cycle, so this only grows its
    /// storage for the batches that actually need one.
    blocker_cursor: SecondaryMap<SeqMove<E>, u32>,

    /// Scratch space for the search for a move that sits on a cycle.
    stack: Vec<SeqMove<E>>,

    /// The scratch location holding the source of each move that a cycle break
    /// has parked and that has not read it back out yet.
    parked: SecondaryMap<SeqMove<E>, Option<ScalarAllocation<E>>>,

    /// Scratch space for just the locations in `parked`, in the form the
    /// `get_scratch` callback wants them.
    scratches: Vec<ScalarAllocation<E>>,
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
            readers: SecondaryMap::new(0),
            blocker_cursor: SecondaryMap::new(0),
            stack: Vec::new(),
            parked: SecondaryMap::new(None),
            scratches: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            moves,
            state,
            readers,
            blocker_cursor,
            stack,
            parked,
            scratches,
        } = self;
        moves.reset();
        state.reset();
        readers.reset();
        blocker_cursor.reset();
        stack.clear();
        parked.reset();
        scratches.clear();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            moves,
            state,
            readers,
            blocker_cursor,
            stack,
            parked,
            scratches,
        } = self;
        moves.is_reset()
            && state.is_reset()
            && readers.is_reset()
            && blocker_cursor.is_reset()
            && stack.is_empty()
            && parked.is_reset()
            && scratches.is_empty()
    }

    /// Sequentialize `moves`, appending them to `out` in emission order.
    ///
    /// Leaves whatever `out` already contained in place, only appends.
    ///
    /// `overlaps` must return whether two locations overlap.
    ///
    /// `get_scratch` is called when we need a scratch location to break a move
    /// cycle or stack-to-stack move. It must return a location that can hold
    /// the given move's value, which is not used as a source or destination in
    /// the current batch of moves being solved, and must not create a new
    /// stack-to-stack move. Its second argument lists the scratch locations
    /// that are already holding a value for this batch; the location it
    /// returns must not overlap any of them.
    pub fn solve(
        &mut self,
        moves: impl IntoIterator<Item = ParallelMove<E>>,
        overlaps: impl FnMut(ScalarAllocation<E>, ScalarAllocation<E>) -> bool,
        get_scratch: impl FnMut(ParallelMove<E>, &[ScalarAllocation<E>]) -> Option<ScalarAllocation<E>>,
        out: &mut Vec<ParallelMove<E>>,
    ) -> Result<(), SolveError> {
        let result = self.solve_inner(moves, overlaps, get_scratch, out);
        self.reset();
        result
    }

    fn solve_inner(
        &mut self,
        moves: impl IntoIterator<Item = ParallelMove<E>>,
        mut overlaps: impl FnMut(ScalarAllocation<E>, ScalarAllocation<E>) -> bool,
        get_scratch: impl FnMut(ParallelMove<E>, &[ScalarAllocation<E>]) -> Option<ScalarAllocation<E>>,
        out: &mut Vec<ParallelMove<E>>,
    ) -> Result<(), SolveError> {
        debug_assert!(self.is_reset());

        for m in moves {
            // Ignore self-moves.
            //
            // Under partial overlap "overlaps" is weaker than "is the same
            // location". However! A value is associated with a single bank, so
            // we never move between banks, and registers within a bank never
            // partially overlap, so this check is sufficient for ignoring
            // self-moves.
            if overlaps(m.src, m.dst) {
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

        self.count_readers(&mut overlaps);
        self.emit_moves(overlaps, get_scratch, out)
    }

    /// Count, for each move, how many moves read the location it writes.
    fn count_readers(
        &mut self,
        overlaps: &mut impl FnMut(ScalarAllocation<E>, ScalarAllocation<E>) -> bool,
    ) {
        for (m, mv) in self.moves.iter() {
            let mut readers = 0;
            for (other, other_mv) in self.moves.iter() {
                if other == m {
                    continue;
                }
                debug_assert!(
                    !(other > m && overlaps(mv.dst, other_mv.dst)),
                    "each location in a parallel move batch must be written by at most one \
                     move, but {mv:?} and {other_mv:?} both write it",
                );
                if overlaps(other_mv.src, mv.dst) {
                    readers += 1;
                }
            }
            self.readers[m] = readers;
        }
    }

    /// Record that `reader` is finished.
    ///
    /// It will never read `src` again, so every move waiting to overwrite it is
    /// one reader closer to being free to do so.
    fn retire_read(
        &mut self,
        reader: SeqMove<E>,
        src: ScalarAllocation<E>,
        overlaps: &mut impl FnMut(ScalarAllocation<E>, ScalarAllocation<E>) -> bool,
    ) {
        for mv in self.moves.keys() {
            if mv == reader || self.state.get(mv) == State::Done {
                continue;
            }
            if overlaps(src, self.moves[mv].dst) {
                self.readers[mv] -= 1;
            }
        }
    }

    /// Emit `m` and retire the read it was holding.
    fn place(
        &mut self,
        m: SeqMove<E>,
        overlaps: &mut impl FnMut(ScalarAllocation<E>, ScalarAllocation<E>) -> bool,
        scratches: &[ScalarAllocation<E>],
        get_scratch: &mut impl FnMut(
            ParallelMove<E>,
            &[ScalarAllocation<E>],
        ) -> Option<ScalarAllocation<E>>,
        out: &mut Vec<ParallelMove<E>>,
    ) -> Result<(), SolveError> {
        debug_assert_eq!(self.readers[m], 0);

        let mv = self.moves[m];
        self.state.set(m, State::Done);

        if let Some(via) = push_move(mv, scratches, get_scratch, out)? {
            self.debug_assert_scratch_is_free(via, scratches, overlaps);
        }

        self.retire_read(m, mv.src, overlaps);
        Ok(())
    }

    /// Debug assert that a scratch the caller just handed us really is free.
    fn debug_assert_scratch_is_free(
        &self,
        scratch: ScalarAllocation<E>,
        scratches: &[ScalarAllocation<E>],
        overlaps: &mut impl FnMut(ScalarAllocation<E>, ScalarAllocation<E>) -> bool,
    ) {
        if !cfg!(debug_assertions) {
            return;
        }
        for (m, mv) in self.moves.iter() {
            debug_assert!(
                !overlaps(scratch, mv.dst),
                "a scratch location must not be written by the batch, but {scratch:?} \
                 overlaps the destination of {mv:?}",
            );
            debug_assert!(
                self.state.get(m) == State::Done || !overlaps(scratch, mv.src),
                "a scratch location must not hold a value the batch has yet to read, but \
                 {scratch:?} overlaps the source of {mv:?}",
            );
        }
        for &other in scratches {
            debug_assert!(
                !overlaps(scratch, other),
                "a scratch location must not overlap one that is already holding a value, \
                 but {scratch:?} overlaps {other:?}",
            );
        }
    }

    /// Find a move that has not yet been emitted and still needs to read what
    /// `m` writes.
    fn find_blocker(
        &mut self,
        m: SeqMove<E>,
        overlaps: &mut impl FnMut(ScalarAllocation<E>, ScalarAllocation<E>) -> bool,
    ) -> Option<SeqMove<E>> {
        let dst = self.moves[m].dst;

        let i = self.blocker_cursor[m];
        let mut i = usize::try_from(i).unwrap();

        let found = loop {
            if i == self.moves.len() {
                break None;
            }

            let other = SeqMove::try_new(i).unwrap();
            if other != m
                && self.state.get(other) != State::Done
                && overlaps(self.moves[other].src, dst)
            {
                break Some(other);
            }

            i += 1;
        };

        // Stop at the blocker, not past it: it is still a blocker until it
        // retires.
        self.blocker_cursor[m] = u32::try_from(i).unwrap();

        found
    }

    fn emit_moves(
        &mut self,
        overlaps: impl FnMut(ScalarAllocation<E>, ScalarAllocation<E>) -> bool,
        get_scratch: impl FnMut(ParallelMove<E>, &[ScalarAllocation<E>]) -> Option<ScalarAllocation<E>>,
        out: &mut Vec<ParallelMove<E>>,
    ) -> Result<(), SolveError> {
        let mut scratches = mem::take(&mut self.scratches);

        let result = self.emit_moves_inner(&mut scratches, overlaps, get_scratch, out);

        scratches.clear();
        self.scratches = scratches;

        result
    }

    /// Emit all unblocked moves, break the next extant cycle, and repeat until
    /// all moves have been emitted.
    fn emit_moves_inner(
        &mut self,
        scratches: &mut Vec<ScalarAllocation<E>>,
        mut overlaps: impl FnMut(ScalarAllocation<E>, ScalarAllocation<E>) -> bool,
        mut get_scratch: impl FnMut(
            ParallelMove<E>,
            &[ScalarAllocation<E>],
        ) -> Option<ScalarAllocation<E>>,
        out: &mut Vec<ParallelMove<E>>,
    ) -> Result<(), SolveError> {
        debug_assert!(self.parked.is_reset());
        debug_assert!(scratches.is_empty());

        let mut remaining = self.moves.len();
        while remaining > 0 {
            // Emit everything nothing is waiting on, and keep going while that
            // works: emitting a move retires its own read, which might free the
            // move that was waiting to overwrite what it read, etc...
            let placed = self.place_unblocked(scratches, &mut overlaps, &mut get_scratch, out)?;
            if placed > 0 {
                remaining -= placed;
                continue;
            }

            // Nothing could be emitted, so every move still pending is part of
            // some cycle.
            self.break_cycle(scratches, &mut overlaps, &mut get_scratch, out)?;
        }

        Ok(())
    }

    /// Emit every move that nothing is waiting on any more, and report how many
    /// that was.
    fn place_unblocked(
        &mut self,
        scratches: &mut Vec<ScalarAllocation<E>>,
        overlaps: &mut impl FnMut(ScalarAllocation<E>, ScalarAllocation<E>) -> bool,
        get_scratch: &mut impl FnMut(
            ParallelMove<E>,
            &[ScalarAllocation<E>],
        ) -> Option<ScalarAllocation<E>>,
        out: &mut Vec<ParallelMove<E>>,
    ) -> Result<usize, SolveError> {
        let mut placed = 0;

        for m in self.moves.keys() {
            if self.state.get(m) == State::Done || self.readers[m] != 0 {
                continue;
            }

            self.place(m, overlaps, scratches, get_scratch, out)?;
            placed += 1;

            // If this was a parked move, it has just read its value back out of
            // the scratch, which is free again.
            //
            // Go through `get_mut` rather than indexing, so that the batches
            // that never park anything never grow the map.
            if let Some(scratch) = self.parked.get_mut(m).and_then(Option::take) {
                scratches.retain(|&s| s != scratch);
            }
        }

        Ok(placed)
    }

    /// Break a cycle among the moves that have not been emitted yet.
    ///
    /// Parks one cycle member's source in a scratch location, which retires its
    /// read without emitting it, freeing the move that was waiting to overwrite
    /// the source. The parked move is emitted later, reading the scratch
    /// instead.
    fn break_cycle(
        &mut self,
        scratches: &mut Vec<ScalarAllocation<E>>,
        overlaps: &mut impl FnMut(ScalarAllocation<E>, ScalarAllocation<E>) -> bool,
        get_scratch: &mut impl FnMut(
            ParallelMove<E>,
            &[ScalarAllocation<E>],
        ) -> Option<ScalarAllocation<E>>,
        out: &mut Vec<ParallelMove<E>>,
    ) -> Result<(), SolveError> {
        // Find a stuck move that is part of a cycle.
        let stuck = self
            .moves
            .keys()
            .find(|&m| self.state.get(m) != State::Done)
            .expect("only called while moves are left to emit");

        // Walk the cycle until we hit a back edge to maximize the tail of moves
        // we are unblocking.
        let mut cur = self
            .find_blocker(stuck, overlaps)
            .expect("a move that is waiting has something to wait for");
        debug_assert!(self.stack.is_empty());
        while self.state.get(cur) != State::Pending {
            self.state.set(cur, State::Pending);
            self.stack.push(cur);
            cur = self
                .find_blocker(cur, overlaps)
                .expect("every move in a batch that is stuck has a blocker");
        }
        while let Some(m) = self.stack.pop() {
            self.state.set(m, State::Todo);
        }

        // Break the cycle at `cur`.
        let mv = self.moves[cur];
        let Some(scratch) = get_scratch(mv, scratches) else {
            return Err(SolveError::NoScratch);
        };

        self.debug_assert_scratch_is_free(scratch, scratches, overlaps);
        debug_assert!(!matches!(
            (scratch, mv.dst),
            (ScalarAllocation::Stack(_), ScalarAllocation::Stack(_))
        ));

        out.push(ParallelMove {
            src: mv.src,
            dst: scratch,
        });
        self.retire_read(cur, mv.src, overlaps);
        self.moves[cur].src = scratch;
        self.parked[cur] = Some(scratch);
        scratches.push(scratch);

        Ok(())
    }
}

/// Append `mv` to `out`, routing it through a scratch location when it moves
/// memory to memory, which no machine can do in one instruction.
///
/// `avoid` are the locations that are already holding a value, which the
/// scratch may not overlap.
///
/// Returns the scratch the move was routed through, when it needed one.
fn push_move<E>(
    mv: ParallelMove<E>,
    avoid: &[ScalarAllocation<E>],
    get_scratch: &mut impl FnMut(ParallelMove<E>, &[ScalarAllocation<E>]) -> Option<ScalarAllocation<E>>,
    out: &mut Vec<ParallelMove<E>>,
) -> Result<Option<ScalarAllocation<E>>, SolveError>
where
    E: EntityRepr,
{
    if !matches!(
        (mv.src, mv.dst),
        (ScalarAllocation::Stack(_), ScalarAllocation::Stack(_))
    ) {
        out.push(mv);
        return Ok(None);
    }

    let Some(via) = get_scratch(mv, avoid) else {
        return Err(SolveError::NoScratch);
    };

    out.push(ParallelMove {
        src: mv.src,
        dst: via,
    });
    out.push(ParallelMove {
        src: via,
        dst: mv.dst,
    });

    Ok(Some(via))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Reg, SpillSlot,
        test::{TestLocation, TestMove, TestParallelMoves},
    };
    use core::{
        ops::Range,
        sync::atomic::{AtomicUsize, Ordering},
    };
    use mutatis::{
        check::{Check, CheckResult},
        mutators as m,
    };
    use std::{string::String, vec, vec::Vec};

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
        TestParallelMoves::disjoint_regs()
    }

    fn batch(moves: Vec<TestMove>) -> TestParallelMoves {
        TestParallelMoves::new(distinct_regs(), moves, true)
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
        let moves = TestParallelMoves::new(vec![0, 0], vec![mv(reg(0), reg(1))], true);
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
    /// names — what `overlaps` is for.
    #[test]
    fn aliased_swap() {
        let moves = TestParallelMoves::new(
            vec![0, 0, 2],
            vec![mv(reg(0), reg(2)), mv(reg(2), reg(1))],
            true,
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
            true,
        );
        assert_eq!(moves.moves().len(), 1);
    }

    /// Without a scratch location a cycle cannot be broken at all.
    #[test]
    fn no_scratch_for_a_cycle() {
        let moves = TestParallelMoves::new(
            distinct_regs(),
            vec![mv(reg(0), reg(1)), mv(reg(1), reg(0))],
            false,
        );
        let outcome = moves.check().unwrap();
        assert!(outcome.refused);
        assert!(outcome.wanted_scratch);
    }

    /// A batch with no cycle never asks for one.
    #[test]
    fn no_scratch_needed() {
        let moves = TestParallelMoves::new(
            distinct_regs(),
            vec![mv(reg(0), reg(1)), mv(reg(1), reg(2))],
            false,
        );
        let outcome = moves.check().unwrap();
        assert!(!outcome.refused);
        assert!(!outcome.wanted_scratch);
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
        }
    }

    /// Solve without aliasing or a scratch, for the precondition checks.
    fn solve_raw(moves: &[ParallelMove<u32>]) -> Vec<ParallelMove<u32>> {
        let mut out = Vec::new();
        ParallelMoveSolver::new()
            .solve(moves.iter().copied(), |a, b| a == b, |_, _| None, &mut out)
            .unwrap();
        out
    }

    /// Debug-only: the precondition it violates is a `debug_assert!`, which
    /// the release profile compiles away.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic = "written by at most one move"]
    fn two_moves_writing_one_location() {
        solve_raw(&[parallel_move(reg(0), reg(2)), parallel_move(reg(1), reg(2))]);
    }

    /// How many scratch registers `cells` leaves room for, and how many cells
    /// it lays out in all.
    const NUM_MODEL_SCRATCHES: usize = 2;
    const NUM_MODEL_CELLS: usize = 3 + NUM_MODEL_SCRATCHES * 2 + 3 * 2;

    /// A model machine whose banks alias *partially*, one cell per register
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
        let mut asked = 0;
        ParallelMoveSolver::new()
            .solve(
                [
                    parallel_move(reg(2), slot(0)),
                    parallel_move(slot(1), reg(0)),
                    parallel_move(slot(2), reg(1)),
                ],
                partially_aliasing,
                |_, _| {
                    asked += 1;
                    None
                },
                &mut out,
            )
            .unwrap();

        assert_eq!(asked, 0, "this batch needs no scratch");
        assert_eq!(
            out,
            [
                parallel_move(reg(2), slot(0)),
                parallel_move(slot(1), reg(0)),
                parallel_move(slot(2), reg(1)),
            ],
            "reading `r2` must come before both of the writes that cover it",
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
        let mut scratches = vec![reg(3), reg(4)];
        let mut asked = Vec::new();
        ParallelMoveSolver::new()
            .solve(
                [
                    parallel_move(reg(0), slot(1)),
                    parallel_move(slot(1), reg(1)),
                    parallel_move(reg(2), slot(0)),
                    parallel_move(slot(0), reg(0)),
                ],
                partially_aliasing,
                |mv, avoid| {
                    asked.push((mv, avoid.to_vec()));
                    let scratch = allocation(scratches.remove(0));
                    assert!(
                        avoid.iter().all(|&a| !partially_aliasing(scratch, a)),
                        "the solver must not hand out a scratch that is already in use",
                    );
                    Some(scratch)
                },
                &mut out,
            )
            .unwrap();

        assert_eq!(asked.len(), 2, "two cycles, two breaks");
        assert!(
            asked[0].1.is_empty() && asked[1].1.len() == 1,
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
        let mut asked = 0;
        ParallelMoveSolver::new()
            .solve(
                [parallel_move(slot(0), slot(1))],
                |a, b| a == b,
                |mv, avoid| {
                    asked += 1;
                    assert_eq!(mv, parallel_move(slot(0), slot(1)));
                    assert!(avoid.is_empty(), "nothing else is live across this move");
                    Some(allocation(reg(3)))
                },
                &mut out,
            )
            .unwrap();

        assert_eq!(asked, 1);
        assert_eq!(
            out,
            [
                parallel_move(slot(0), reg(3)),
                parallel_move(reg(3), slot(1)),
            ],
        );
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

    /// And without one to route it through, the solver refuses.
    #[test]
    fn no_scratch_for_a_stack_to_stack_move() {
        let moves = TestParallelMoves::new(distinct_regs(), vec![mv(slot(0), slot(1))], false);
        let outcome = moves.check().unwrap();
        assert!(outcome.refused);
        assert!(outcome.routed_stack_to_stack);
    }

    /// One solver, several batches: its scratch space must start each clean.
    #[test]
    fn solver_is_reusable() {
        let mut solver = ParallelMoveSolver::<u32>::new();
        let mut out = Vec::new();

        for _ in 0..3 {
            out.clear();
            solver
                .solve(
                    [parallel_move(reg(0), reg(1)), parallel_move(reg(1), reg(0))],
                    |a, b| a == b,
                    |_, _| Some(allocation(reg(3))),
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

        solver
            .solve(
                [parallel_move(reg(0), reg(1)), parallel_move(reg(1), reg(2))],
                |a, b| a == b,
                |_, _| None,
                &mut out,
            )
            .unwrap();

        assert_eq!(out.len(), 3);
        assert_eq!(out[0], already_there);
        // And our own tail is in emission order, not the reverse.
        assert_eq!(out[1], parallel_move(reg(1), reg(2)));
        assert_eq!(out[2], parallel_move(reg(0), reg(1)));
    }

    /// `TestParallelMoves::two_concurrent_cycle_breaks` really does park
    /// two values at once.
    #[test]
    fn two_cycles_break_at_once() {
        let moves = TestParallelMoves::two_concurrent_cycle_breaks();
        assert_eq!(moves.moves().len(), 4, "the fixup keeps all four moves");
        assert!(moves.has_a_source_covered_twice());

        let outcome = moves.check().unwrap();
        assert!(
            outcome.concurrent_scratches,
            "breaking the first cycle should not free the second",
        );
        // Four moves and two breaks.
        assert_eq!(outcome.emitted, 6);
    }

    /// A move between two *wide* slots routes through a wide scratch. Only
    /// the widths make this different from `stack_to_stack`, and only they
    /// are what the interpreter's width check is there to catch.
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
        static REFUSED: AtomicUsize = AtomicUsize::new(0);
        static TRIVIAL: AtomicUsize = AtomicUsize::new(0);
        static STACK: AtomicUsize = AtomicUsize::new(0);
        static ROUTED: AtomicUsize = AtomicUsize::new(0);
        static NESTED: AtomicUsize = AtomicUsize::new(0);
        static PARTIAL: AtomicUsize = AtomicUsize::new(0);
        static CONCURRENT: AtomicUsize = AtomicUsize::new(0);
        static WIDE: AtomicUsize = AtomicUsize::new(0);

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
                    if outcome.refused {
                        REFUSED.fetch_add(1, Ordering::Relaxed);
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
            ("batches that had no scratch to give", &REFUSED),
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
        ] {
            assert!(
                count.load(Ordering::Relaxed) > 0,
                "the property test never saw any {what}",
            );
        }

        result
    }
}
