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
/// name one physical register the way `x0` and `w0` do, so that the solver's
/// `overlaps` closure does real work. Aliasing is all-or-nothing, never
/// partial, which is all the solver supports and all move generation hands it.
#[derive(Clone, Debug, Hash)]
pub struct TestParallelMoves {
    /// For each register name, which physical register it names.
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
    /// How many physical registers the model machine has, besides the scratch.
    /// Few, so that generated batches collide and cycles arise on their own.
    pub(crate) const NUM_PHYS_REGS: u8 = 4;

    /// How many spill slots the model machine has.
    const NUM_SLOTS: u8 = 3;

    /// The ceiling on register names; more than there are physical registers,
    /// so that aliasing happens.
    const MAX_REG_NAMES: usize = 6;

    /// The ceiling on how many moves a batch holds.
    const MAX_MOVES: usize = 8;

    /// The scratch registers' names: outside the generated name table, and
    /// naming registers no generated move can reach. Two of them, because a
    /// move from one slot to another needs somewhere to pass through even
    /// when it sits inside a cycle that is already using a scratch.
    const SCRATCH_NAMES: [usize; 2] = [Self::MAX_REG_NAMES, Self::MAX_REG_NAMES + 1];

    /// How many distinct locations the model machine has.
    const NUM_LOCATIONS: usize =
        Self::NUM_PHYS_REGS as usize + Self::SCRATCH_NAMES.len() + Self::NUM_SLOTS as usize;

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
    /// and drop moves that would leave the batch undefined: a location may be
    /// written by only one move.
    fn fixup(&mut self) {
        self.regs.truncate(Self::MAX_REG_NAMES);
        if self.regs.is_empty() {
            self.regs.push(0);
        }
        for reg in &mut self.regs {
            *reg %= Self::NUM_PHYS_REGS;
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
            let dst = self.location_index(self.allocation(m.dst));
            let dst_written_twice = kept
                .iter()
                .any(|other| self.location_index(self.allocation(other.dst)) == dst);
            if dst_written_twice {
                continue;
            }
            kept.push(*m);
        }
        self.moves = kept;
    }

    /// The moves in this batch.
    pub(crate) fn moves(&self) -> &[TestMove] {
        &self.moves
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

    /// The scratch locations, which no generated move can name.
    fn scratches(&self) -> [ScalarAllocation<u32>; 2] {
        Self::SCRATCH_NAMES.map(|name| ScalarAllocation::Reg(Reg::try_new(name).unwrap()))
    }

    /// Which of the model machine's locations is this allocation? Aliasing
    /// names answer the same index, making this the location's identity.
    fn location_index(&self, alloc: ScalarAllocation<u32>) -> usize {
        match alloc {
            ScalarAllocation::Reg(reg) => {
                let name = reg.index();
                match Self::SCRATCH_NAMES.iter().position(|&s| s == name) {
                    Some(i) => usize::from(Self::NUM_PHYS_REGS) + i,
                    None => usize::from(self.regs[name]),
                }
            }
            ScalarAllocation::Stack(slot) => {
                usize::from(Self::NUM_PHYS_REGS) + Self::SCRATCH_NAMES.len() + slot.index()
            }
        }
    }

    /// Are these two allocations the same location of the model machine?
    fn overlaps(&self, a: ScalarAllocation<u32>, b: ScalarAllocation<u32>) -> bool {
        self.location_index(a) == self.location_index(b)
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
                    nested_scratch |= avoid.is_some();
                }
                if !self.provide_scratch {
                    return None;
                }
                // Whichever scratch is not already spoken for: the move may
                // sit inside a cycle that parked a value in the other one.
                let scratch = self
                    .scratches()
                    .into_iter()
                    .find(|&s| avoid.is_none_or(|a| !self.overlaps(s, a)));
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

        // Run the sequence, starting each location off holding its own
        // distinct value.
        let mut state: Vec<usize> = (0..Self::NUM_LOCATIONS).collect();
        for m in &out {
            if matches!(
                (m.src, m.dst),
                (ScalarAllocation::Stack(_), ScalarAllocation::Stack(_))
            ) {
                return Err(format!("the solver emitted the stack-to-stack move {m:?}"));
            }
            let src = self.location_index(m.src);
            let dst = self.location_index(m.dst);
            state[dst] = state[src];
        }

        // Every move in the batch must have happened, as if all at once.
        for m in &batch {
            let src = self.location_index(m.src);
            let dst = self.location_index(m.dst);
            if state[dst] != src {
                return Err(format!(
                    "after solving {:?} into {out:?}, location {dst} holds the value that \
                     started in location {}, but the move {m:?} should have left it holding \
                     the one that started in location {src}",
                    self.moves, state[dst],
                ));
            }
        }

        // Nothing else may be disturbed, except the scratches.
        let mut written = vec![false; Self::NUM_LOCATIONS];
        for scratch in self.scratches() {
            written[self.location_index(scratch)] = true;
        }
        for m in &batch {
            written[self.location_index(m.dst)] = true;
        }
        for (loc, &written) in written.iter().enumerate() {
            if !written && state[loc] != loc {
                return Err(format!(
                    "after solving {:?} into {out:?}, location {loc} holds the value that \
                     started in location {}, but no move in the batch writes it",
                    self.moves, state[loc],
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
