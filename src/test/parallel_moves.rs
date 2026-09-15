//! Generated inputs for testing the parallel-move solver.

#![allow(missing_docs, reason = "internal test utilities")]

use crate::{
    Reg, ScalarAllocation, SpillSlot,
    entity::Entity as _,
    parallel_moves::{ParallelMove, ParallelMoveSolver, SolveError},
};
use alloc::{
    format,
    string::{String, ToString},
    vec,
    vec::Vec,
};
use core::ops::Range;
use mutatis::{DefaultMutate, Generate, Mutate};

/// A location a generated move can read or write.
#[derive(Clone, Copy, Debug, Hash, Mutate)]
pub enum TestLocation {
    /// A register, by *name*. Two names can alias the same physical register,
    /// so a name is not the register's identity.
    Reg(u8),

    /// A spill slot, by index.
    Slot(u8),
}

impl Default for TestLocation {
    fn default() -> Self {
        TestLocation::Reg(0)
    }
}

/// One generated move, `dst := src`.
#[derive(Clone, Copy, Debug, Default, Hash, Mutate)]
pub struct TestMove {
    pub src: TestLocation,
    pub dst: TestLocation,
}

/// A batch of parallel moves to solve, and the model machine to solve it on.
///
/// Moves name registers through `regs`, a table of names several of which may
/// cover the same register units the way `x0` and `w0` do, so that the
/// solver's `overlaps` closure does real work. Aliasing may be *partial*: a
/// two-unit name can cover two one-unit names that do not cover each other,
/// the way a wide vector register covers two narrow ones in another bank.
/// `overlaps` is then reflexive and symmetric but not transitive, which is all
/// the solver may assume of it.
#[derive(Clone, Debug, Hash)]
pub struct TestParallelMoves {
    /// For each register name, the range of register units it covers, as a
    /// width of one or two units and a start. See [`TestParallelMoves::decode`].
    regs: Vec<u8>,

    /// The moves in the batch.
    moves: Vec<TestMove>,

    /// Does the scratch callback hand out a location, or refuse?
    provide_scratch: bool,
}

/// What solving a `TestParallelMoves` did, for non-vacuity checking.
#[derive(Clone, Copy, Debug, Default)]
pub struct TestParallelMovesOutcome {
    /// How many moves the solver emitted.
    pub emitted: usize,

    /// How many moves were in the batch once ones that read what they write
    /// were dropped.
    pub non_trivial: usize,

    /// Did solving ask for a scratch location? Breaking a cycle needs one,
    /// and so does a move from one slot to another.
    pub wanted_scratch: bool,

    /// Did the solver route a move from one slot to another through a
    /// scratch?
    pub routed_stack_to_stack: bool,

    /// Did it route one that sat inside a cycle, so that the scratch it asked
    /// for had to be a different one than the cycle was already using?
    pub nested_scratch: bool,

    /// Did it route one whose two ends are *wide*, so that the scratch it
    /// asked for had to be wide too?
    pub routed_wide_stack_to_stack: bool,

    /// Did the solver break a cycle while another cycle's value was still
    /// parked, so that two scratch locations held a value at once?
    pub concurrent_scratches: bool,

    /// Did the solver give up because no scratch location was available?
    pub refused: bool,
}

impl Default for TestParallelMoves {
    fn default() -> Self {
        let mut moves = TestParallelMoves {
            regs: Vec::new(),
            moves: Vec::new(),
            provide_scratch: true,
        };
        moves.fixup();
        moves
    }
}

impl TestParallelMoves {
    /// How many register units the model machine has. Few, so that generated
    /// batches collide and cycles arise on their own.
    const NUM_UNITS: usize = 4;

    /// The widest a register name, scratch or spill slot is.
    const MAX_WIDTH: usize = 2;

    /// How many spill slots the model machine has.
    const NUM_SLOTS: u8 = 4;

    /// The ceiling on register names; more than there are register units, so
    /// that aliasing happens.
    const MAX_REG_NAMES: usize = 6;

    /// The ceiling on how many moves a batch holds.
    const MAX_MOVES: usize = 8;

    /// How many scratches of each width the model machine has, named outside
    /// the generated name table so that no generated move can reach them.
    ///
    /// A cycle break parks a value in one until its move is emitted, and
    /// partial overlap lets one batch have several parked at once, so one per
    /// move in the batch is always enough.
    const NUM_SCRATCHES: usize = Self::MAX_MOVES;

    /// Where the scratches' cells begin, after the register units that
    /// generated names cover.
    const SCRATCH_CELLS: usize = Self::NUM_UNITS;

    /// Where the spill slots' cells begin, after the scratches'.
    const SLOT_CELLS: usize =
        Self::SCRATCH_CELLS + Self::NUM_SCRATCHES * Self::MAX_WIDTH * Self::MAX_WIDTH;

    /// How many cells the model machine has in all: one per register unit,
    /// plus private cells for each scratch and each spill slot.
    const NUM_CELLS: usize = Self::SLOT_CELLS + Self::NUM_SLOTS as usize * Self::MAX_WIDTH;

    /// A batch of moves on a model machine with the given register names,
    /// repaired to satisfy the solver's preconditions.
    pub fn new(regs: Vec<u8>, moves: Vec<TestMove>, provide_scratch: bool) -> Self {
        let mut this = TestParallelMoves {
            regs,
            moves,
            provide_scratch,
        };
        this.fixup();
        this
    }

    /// Clamp the model machine's size, bring every name and index in range,
    /// and drop moves the solver's preconditions do not allow.
    fn fixup(&mut self) {
        self.regs.truncate(Self::MAX_REG_NAMES);
        if self.regs.is_empty() {
            self.regs.push(Self::encode(0, 1));
        }
        for reg in &mut self.regs {
            let (start, width) = Self::decode(*reg);
            *reg = Self::encode(start, width);
        }

        self.moves.truncate(Self::MAX_MOVES);
        let num_names = u8::try_from(self.regs.len()).unwrap();
        for m in &mut self.moves {
            for loc in [&mut m.src, &mut m.dst] {
                match loc {
                    TestLocation::Reg(name) => *name %= num_names,
                    TestLocation::Slot(slot) => *slot %= Self::NUM_SLOTS,
                }
            }
        }

        let mut kept: Vec<TestMove> = Vec::with_capacity(self.moves.len());
        for m in &self.moves {
            let src = self.cells(self.allocation(m.src));
            let dst = self.cells(self.allocation(m.dst));

            // A move carries one value, so both its ends are the same width,
            // and they either are the very same location or are disjoint: in
            // the allocator both ends are in the value's own bank, and
            // registers within one bank never partially overlap.
            if src.len() != dst.len() || (src != dst && Self::intersect(&src, &dst)) {
                continue;
            }

            // Two moves writing one location leave the batch undefined.
            let dst_written_twice = kept
                .iter()
                .any(|other| Self::intersect(&self.cells(self.allocation(other.dst)), &dst));
            if dst_written_twice {
                continue;
            }
            kept.push(*m);
        }
        self.moves = kept;
    }

    /// The unit range a `regs` entry names: a width of one or two units, and a
    /// start that keeps the whole range inside the machine.
    fn decode(byte: u8) -> (usize, usize) {
        let width = 1 + usize::from(byte & 1);
        let start = (usize::from(byte) >> 1) % (Self::NUM_UNITS - width + 1);
        (start, width)
    }

    /// The canonical `regs` entry for a unit range, so that [`Self::fixup`]
    /// leaves equal ranges spelled the same way.
    fn encode(start: usize, width: usize) -> u8 {
        u8::try_from((start << 1) | (width - 1)).unwrap()
    }

    /// A `regs` table naming every register unit once, so that no two names
    /// overlap.
    #[cfg(test)]
    pub(crate) fn disjoint_regs() -> Vec<u8> {
        (0..Self::NUM_UNITS).map(|s| Self::encode(s, 1)).collect()
    }

    fn intersect(a: &Range<usize>, b: &Range<usize>) -> bool {
        a.start < b.end && b.start < a.end
    }

    /// The moves in this batch.
    #[cfg(test)]
    pub(crate) fn moves(&self) -> &[TestMove] {
        &self.moves
    }

    /// Is some move's source covered by two destinations that do not overlap
    /// each other?
    ///
    /// That is the shape a machine whose banks alias partially produces, and
    /// the one a solver that records a single "must happen after me" successor
    /// per move cannot represent. A model in which overlap is all-or-nothing
    /// can never build it, so this is what says the search is not vacuous.
    pub fn has_a_source_covered_twice(&self) -> bool {
        self.moves.iter().any(|m| {
            let src = self.allocation(m.src);
            let covering: Vec<ScalarAllocation<u32>> = self
                .moves
                .iter()
                .map(|other| self.allocation(other.dst))
                .filter(|&dst| self.overlaps(src, dst))
                .collect();
            covering
                .iter()
                .enumerate()
                .any(|(i, &a)| covering[..i].iter().any(|&b| !self.overlaps(a, b)))
        })
    }

    /// The allocation a generated location stands for.
    fn allocation(&self, loc: TestLocation) -> ScalarAllocation<u32> {
        match loc {
            TestLocation::Reg(name) => {
                ScalarAllocation::Reg(Reg::try_new(usize::from(name)).unwrap())
            }
            TestLocation::Slot(slot) => {
                ScalarAllocation::Stack(SpillSlot::try_new(usize::from(slot)).unwrap())
            }
        }
    }

    /// The scratch locations of a given width, which no generated move names.
    fn scratches(&self, width: usize) -> impl Iterator<Item = ScalarAllocation<u32>> {
        let base = Self::MAX_REG_NAMES + (width - 1) * Self::NUM_SCRATCHES;
        (base..base + Self::NUM_SCRATCHES)
            .map(|name| ScalarAllocation::Reg(Reg::try_new(name).unwrap()))
    }

    /// How wide a spill slot is. Fixed per slot, so that a batch cannot move
    /// one value through a slot at one width and another value at another.
    ///
    /// Only the last two slots are wide, so that most slots pair with most
    /// register names and batches moving to and from memory stay easy to
    /// write, while a two-unit name still has somewhere to spill to. *Two* of
    /// them, because a move's two ends are the same width: with only one wide
    /// slot, a wide move from one slot to another could not be written at all,
    /// and the routing that such a move needs would go untested at any width
    /// but one.
    fn slot_width(slot: usize) -> usize {
        if slot + Self::MAX_WIDTH >= Self::NUM_SLOTS as usize {
            Self::MAX_WIDTH
        } else {
            1
        }
    }

    /// The model machine's cells that this allocation covers.
    ///
    /// Two allocations overlap exactly when their cells do, so overlap can be
    /// partial: a two-unit name covers two one-unit names that do not cover
    /// each other. Scratches and spill slots get cells of their own, so they
    /// overlap nothing but themselves.
    fn cells(&self, alloc: ScalarAllocation<u32>) -> Range<usize> {
        match alloc {
            ScalarAllocation::Reg(reg) => match reg.index().checked_sub(Self::MAX_REG_NAMES) {
                Some(scratch) => {
                    let base = Self::SCRATCH_CELLS + scratch * Self::MAX_WIDTH;
                    base..base + 1 + scratch / Self::NUM_SCRATCHES
                }
                None => {
                    let (start, width) = Self::decode(self.regs[reg.index()]);
                    start..start + width
                }
            },
            ScalarAllocation::Stack(slot) => {
                let base = Self::SLOT_CELLS + slot.index() * Self::MAX_WIDTH;
                base..base + Self::slot_width(slot.index())
            }
        }
    }

    /// Do these two allocations share any of the model machine's cells?
    fn overlaps(&self, a: ScalarAllocation<u32>, b: ScalarAllocation<u32>) -> bool {
        Self::intersect(&self.cells(a), &self.cells(b))
    }

    /// Solve this batch and interpret the result on the model machine: every
    /// move must deliver its source's original value to its destination, and
    /// nothing but the destinations and the scratch may change.
    pub fn check(&self) -> Result<TestParallelMovesOutcome, String> {
        let batch: Vec<ParallelMove<u32>> = self
            .moves
            .iter()
            .map(|m| ParallelMove {
                src: self.allocation(m.src),
                dst: self.allocation(m.dst),
            })
            .collect();

        let mut solver = ParallelMoveSolver::new();
        let mut out = Vec::new();

        let mut wanted_scratch = false;
        let mut routed_stack_to_stack = false;
        let mut nested_scratch = false;
        let mut routed_wide_stack_to_stack = false;
        let mut concurrent_scratches = false;
        let result = solver.solve(
            batch.iter().copied(),
            |a, b| self.overlaps(a, b),
            |mv, avoid| {
                wanted_scratch = true;
                if matches!(
                    (mv.src, mv.dst),
                    (ScalarAllocation::Stack(_), ScalarAllocation::Stack(_))
                ) {
                    routed_stack_to_stack = true;
                    nested_scratch |= !avoid.is_empty();
                    routed_wide_stack_to_stack |= self.cells(mv.dst).len() > 1;
                } else {
                    // Not a routed move, so this is a cycle break; anything
                    // already parked belongs to a cycle this one did not free.
                    concurrent_scratches |= !avoid.is_empty();
                }
                if !self.provide_scratch {
                    return None;
                }
                // Whichever scratch of the right width is not already spoken
                // for: other cycle breaks in this batch may still have values
                // parked, and a move may sit inside one of them.
                let scratch = self
                    .scratches(self.cells(mv.dst).len())
                    .find(|&s| avoid.iter().all(|&a| !self.overlaps(s, a)));
                assert!(
                    scratch.is_some(),
                    "the solver wants more scratch locations at once than the model has",
                );
                scratch
            },
            &mut out,
        );

        if !solver.is_reset() {
            return Err("the solver is not reset after solving a batch".to_string());
        }

        let refused = match result {
            Ok(()) => false,
            Err(SolveError::NoScratch) => {
                if self.provide_scratch {
                    return Err(
                        "the solver asked for a scratch location, was given one, and still \
                         reported `NoScratch`"
                            .to_string(),
                    );
                }
                if !wanted_scratch {
                    return Err(
                        "the solver reported `NoScratch` without ever asking for one".to_string(),
                    );
                }

                // Failure is only allowed for a cycle that needed breaking, so
                // the same batch must be solvable once a scratch exists.
                out.clear();
                let solvable = Self {
                    regs: self.regs.clone(),
                    moves: self.moves.clone(),
                    provide_scratch: true,
                };
                let outcome = solvable.check()?;
                if !outcome.wanted_scratch {
                    return Err(format!(
                        "the solver reported `NoScratch` for a batch it solves without one: \
                         {:?}",
                        self.moves,
                    ));
                }
                return Ok(TestParallelMovesOutcome {
                    refused: true,
                    ..outcome
                });
            }
            Err(SolveError::EntityReprTooSmall) => {
                return Err(format!(
                    "the solver ran out of move indices for a batch of {} moves",
                    self.moves.len(),
                ));
            }
        };

        // Run the sequence, starting each cell off holding its own distinct
        // value.
        let mut state: Vec<usize> = (0..Self::NUM_CELLS).collect();
        for m in &out {
            if matches!(
                (m.src, m.dst),
                (ScalarAllocation::Stack(_), ScalarAllocation::Stack(_))
            ) {
                return Err(format!("the solver emitted the stack-to-stack move {m:?}"));
            }
            let src = self.cells(m.src);
            let dst = self.cells(m.dst);
            if src.len() != dst.len() {
                return Err(format!(
                    "the solver emitted {m:?}, whose two ends are {} and {} units wide",
                    src.len(),
                    dst.len(),
                ));
            }
            for (i, cell) in dst.enumerate() {
                state[cell] = state[src.start + i];
            }
        }

        // Every move in the batch must have happened, as if all at once.
        for m in &batch {
            let src = self.cells(m.src);
            let dst = self.cells(m.dst);
            for (i, cell) in dst.enumerate() {
                if state[cell] != src.start + i {
                    return Err(format!(
                        "after solving {:?} into {out:?}, cell {cell} holds the value that \
                         started in cell {}, but the move {m:?} should have left it holding \
                         the one that started in cell {}",
                        self.moves,
                        state[cell],
                        src.start + i,
                    ));
                }
            }
        }

        // Nothing else may be disturbed, except the scratches.
        let mut written = vec![false; Self::NUM_CELLS];
        written[Self::SCRATCH_CELLS..Self::SLOT_CELLS].fill(true);
        for m in &batch {
            written[self.cells(m.dst)].fill(true);
        }
        for (cell, &written) in written.iter().enumerate() {
            if !written && state[cell] != cell {
                return Err(format!(
                    "after solving {:?} into {out:?}, cell {cell} holds the value that \
                     started in cell {}, but no move in the batch writes it",
                    self.moves, state[cell],
                ));
            }
        }

        let non_trivial = batch
            .iter()
            .filter(|m| !self.overlaps(m.src, m.dst))
            .count();

        Ok(TestParallelMovesOutcome {
            emitted: out.len(),
            non_trivial,
            wanted_scratch,
            routed_stack_to_stack,
            nested_scratch,
            routed_wide_stack_to_stack,
            concurrent_scratches,
            refused,
        })
    }
}

#[derive(Default)]
pub struct TestParallelMovesMutator {}

impl Mutate<TestParallelMoves> for TestParallelMovesMutator {
    fn mutate(
        &mut self,
        mutations: &mut mutatis::Candidates<'_>,
        moves: &mut TestParallelMoves,
    ) -> mutatis::Result<()> {
        let result = (|| -> mutatis::Result<()> {
            <Vec<u8> as DefaultMutate>::DefaultMutate::default()
                .mutate(mutations, &mut moves.regs)?;
            <Vec<TestMove> as DefaultMutate>::DefaultMutate::default()
                .mutate(mutations, &mut moves.moves)?;
            <bool as DefaultMutate>::DefaultMutate::default()
                .mutate(mutations, &mut moves.provide_scratch)?;
            Ok(())
        })();

        moves.fixup();
        result
    }
}

impl Generate<TestParallelMoves> for TestParallelMovesMutator {
    fn generate(&mut self, context: &mut mutatis::Context) -> mutatis::Result<TestParallelMoves> {
        let mut moves = TestParallelMoves {
            regs: <Vec<u8> as DefaultMutate>::DefaultMutate::default().generate(context)?,
            moves: <Vec<TestMove> as DefaultMutate>::DefaultMutate::default().generate(context)?,
            provide_scratch: <bool as DefaultMutate>::DefaultMutate::default().generate(context)?,
        };
        moves.fixup();
        Ok(moves)
    }
}

impl DefaultMutate for TestParallelMoves {
    type DefaultMutate = TestParallelMovesMutator;
}
