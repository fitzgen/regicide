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

/// How far along a move is in the depth-first walk.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum State {
    /// Not visited yet.
    Todo,

    /// On the stack: being visited, but not placed.
    ///
    /// Reaching a `Pending` move again means we have gone all the way around a
    /// cycle.
    Pending,

    /// Placed in the output.
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

    /// The move, if any, that overwrites another move's `src` and so has to
    /// happen after it.
    clobberer: SecondaryMap<SeqMove<E>, Option<SeqMove<E>>>,

    /// The depth-first stack.
    stack: Vec<SeqMove<E>>,
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
            clobberer: SecondaryMap::new(None),
            stack: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            moves,
            state,
            clobberer,
            stack,
        } = self;
        moves.reset();
        state.reset();
        clobberer.reset();
        stack.clear();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            moves,
            state,
            clobberer,
            stack,
        } = self;
        moves.is_reset() && state.is_reset() && clobberer.is_reset() && stack.is_empty()
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
    /// stack-to-stack move.
    pub fn solve(
        &mut self,
        moves: impl IntoIterator<Item = ParallelMove<E>>,
        overlaps: impl FnMut(ScalarAllocation<E>, ScalarAllocation<E>) -> bool,
        get_scratch: impl FnMut(
            ParallelMove<E>,
            Option<ScalarAllocation<E>>,
        ) -> Option<ScalarAllocation<E>>,
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
        get_scratch: impl FnMut(
            ParallelMove<E>,
            Option<ScalarAllocation<E>>,
        ) -> Option<ScalarAllocation<E>>,
        out: &mut Vec<ParallelMove<E>>,
    ) -> Result<(), SolveError> {
        debug_assert!(self.is_reset());

        for m in moves {
            // Ignore self-moves.
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

        // The walk places a move only once its clobberer is placed, so it
        // yields the batch backwards; reverse our own tail of `out` at the end.
        let start = out.len();

        self.find_clobbers(overlaps);
        self.walk(get_scratch, out)?;

        out[start..].reverse();
        Ok(())
    }

    fn find_clobbers(
        &mut self,
        mut overlaps: impl FnMut(ScalarAllocation<E>, ScalarAllocation<E>) -> bool,
    ) {
        for (src, src_mv) in self.moves.iter() {
            let mut clobberer = None;
            for (dst, dst_mv) in self.moves.iter() {
                if dst == src {
                    continue;
                }
                debug_assert!(
                    !(dst > src && overlaps(src_mv.dst, dst_mv.dst)),
                    "each location in a parallel move batch must be written by at most one \
                     move, but {src_mv:?} and {dst_mv:?} both write it",
                );
                if overlaps(dst_mv.dst, src_mv.src) {
                    debug_assert!(
                        clobberer.is_none(),
                        "each location in a parallel move batch must be written by at most one \
                         move, but more than one writes {src_mv:?}'s source",
                    );
                    clobberer = Some(dst);
                }
            }
            self.clobberer[src] = clobberer;
        }
    }

    fn walk(
        &mut self,
        mut get_scratch: impl FnMut(
            ParallelMove<E>,
            Option<ScalarAllocation<E>>,
        ) -> Option<ScalarAllocation<E>>,
        out: &mut Vec<ParallelMove<E>>,
    ) -> Result<(), SolveError> {
        for root in self.moves.keys() {
            if self.state.get(root) != State::Todo {
                continue;
            }

            self.stack.push(root);
            self.state.set(root, State::Pending);

            while let Some(top) = self.stack.last().copied() {
                // The only move that must happen after `top` is the one that
                // clobbers its source.
                let next = self.clobberer[top].filter(|&next| self.state.get(next) != State::Done);

                match next {
                    // No move needs to happen after `top`, so we can push it
                    // into `out` now.
                    None => {
                        self.stack.pop();
                        self.state.set(top, State::Done);
                        push_move(self.moves[top], None, &mut get_scratch, out)?;
                    }

                    // There is a clobberer that must come after `top` and this
                    // is our first time seeing it, so it isn't part of a cycle,
                    // yet, at least. Push the clobberer so we place it first.
                    Some(next) if self.state.get(next) == State::Todo => {
                        self.stack.push(next);
                        self.state.set(next, State::Pending);
                    }

                    // The clobberer is has already been discovered, so we have
                    // a cycle. Break the `cycle` at `top` by getting a scratch
                    // location and emitting `scratch := top.src`, then the rest
                    // of the cycle's moves, and then `top.dst = scratch`.
                    Some(next) => {
                        debug_assert_eq!(self.state.get(next), State::Pending);
                        debug_assert_ne!(next, top, "a move cannot clobber its own source");

                        let top_move = self.moves[top];
                        let Some(cycle_scratch) = get_scratch(top_move, None) else {
                            return Err(SolveError::NoScratch);
                        };

                        self.stack.pop();
                        self.state.set(top, State::Done);

                        // `top` is the move that goes through the scratch, so
                        // these two need no expansion: whichever side of it
                        // touches memory is paired with the scratch, which is
                        // not in memory when it is.
                        out.push(ParallelMove {
                            src: cycle_scratch,
                            dst: top_move.dst,
                        });

                        loop {
                            let c = self
                                .stack
                                .pop()
                                .expect("the whole cycle is on the stack below `top`");

                            self.state.set(c, State::Done);

                            // `cycle_scratch` holds `top`'s value across the
                            // whole cycle, so anything these moves go through
                            // must stay clear of it.
                            let avoid = Some(cycle_scratch);
                            push_move(self.moves[c], avoid, &mut get_scratch, out)?;

                            if c == next {
                                break;
                            }
                        }

                        out.push(ParallelMove {
                            src: top_move.src,
                            dst: cycle_scratch,
                        });
                    }
                }
            }
        }
        Ok(())
    }
}

/// Append `mv` to `out`, routing it through a scratch location when it moves
/// memory to memory, which no machine can do in one instruction.
///
/// `avoid` is a location that is already holding a value, which the scratch may
/// not overlap.
fn push_move<E>(
    mv: ParallelMove<E>,
    avoid: Option<ScalarAllocation<E>>,
    get_scratch: &mut impl FnMut(
        ParallelMove<E>,
        Option<ScalarAllocation<E>>,
    ) -> Option<ScalarAllocation<E>>,
    out: &mut Vec<ParallelMove<E>>,
) -> Result<(), SolveError>
where
    E: EntityRepr,
{
    if !matches!(
        (mv.src, mv.dst),
        (ScalarAllocation::Stack(_), ScalarAllocation::Stack(_))
    ) {
        out.push(mv);
        return Ok(());
    }

    let Some(via) = get_scratch(mv, avoid) else {
        return Err(SolveError::NoScratch);
    };

    // Push in reverse, since the walk must push in reverse, and therefore we
    // reverse the moves before returning them.
    out.push(ParallelMove {
        src: via,
        dst: mv.dst,
    });
    out.push(ParallelMove {
        src: mv.src,
        dst: via,
    });

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Reg, SpillSlot,
        test::{TestLocation, TestMove, TestParallelMoves},
    };
    use core::sync::atomic::{AtomicUsize, Ordering};
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

    /// A model machine with no aliasing: name `i` is register `i`.
    fn distinct_regs() -> Vec<u8> {
        (0..TestParallelMoves::NUM_PHYS_REGS).collect()
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
            vec![0, 0, 1],
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
                    assert!(avoid.is_none(), "nothing else is live across this move");
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

    fn seeds() -> Vec<TestParallelMoves> {
        let regs = distinct_regs();
        let with = |moves: Vec<TestMove>| TestParallelMoves::new(regs.clone(), moves, true);
        vec![
            with(vec![]),
            with(vec![mv(reg(0), reg(0))]),
            with(vec![mv(reg(0), reg(1)), mv(reg(1), reg(2))]),
            with(vec![mv(reg(0), reg(1)), mv(reg(1), reg(0))]),
            with(vec![
                mv(reg(0), reg(1)),
                mv(reg(1), reg(2)),
                mv(reg(2), reg(0)),
            ]),
            with(vec![
                mv(reg(0), reg(1)),
                mv(reg(1), reg(0)),
                mv(reg(2), reg(3)),
                mv(reg(3), reg(2)),
            ]),
            with(vec![
                mv(reg(0), reg(1)),
                mv(reg(1), reg(0)),
                mv(reg(0), reg(2)),
            ]),
            with(vec![mv(slot(0), reg(0)), mv(reg(0), slot(1))]),
            with(vec![mv(slot(0), slot(1))]),
            with(vec![
                mv(slot(0), slot(1)),
                mv(slot(1), reg(0)),
                mv(reg(0), slot(0)),
            ]),
            TestParallelMoves::new(regs.clone(), vec![mv(slot(0), slot(1))], false),
            TestParallelMoves::new(
                regs.clone(),
                vec![mv(reg(0), reg(1)), mv(reg(1), reg(0))],
                false,
            ),
            TestParallelMoves::new(
                vec![0, 0, 1],
                vec![mv(reg(0), reg(2)), mv(reg(2), reg(1))],
                true,
            ),
        ]
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

        let result = Check::new().iters(10_000).run_with(
            m::default::<TestParallelMoves>(),
            seeds(),
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
        ] {
            assert!(
                count.load(Ordering::Relaxed) > 0,
                "the property test never saw any {what}",
            );
        }

        result
    }
}
