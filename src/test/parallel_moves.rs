//! Generated inputs for testing the parallel-move solver.

#![allow(missing_docs, reason = "internal test utilities")]

use crate::{
    Reg, ScalarAllocation, SpillSlot, Val,
    entity::Entity as _,
    parallel_moves::{ParallelMove, ParallelMoveSolver, ScratchReason, ScratchSource, SolveError},
};
use alloc::{
    format,
    string::{String, ToString},
    vec,
    vec::Vec,
};
use core::ops::{Range, RangeInclusive};
use mutatis::{DefaultMutate, Generate, Mutate};

/// A location a generated move can read or write.
#[derive(Clone, Copy, Debug, Hash, Mutate)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
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

/// Where the scratch callback finds a register when the solver has none of
/// its own left.
///
/// None of them declines, so what this varies is where the scratch comes
/// from: a register nothing was using, a register something was using, or,
/// for a broken cycle, which is the only request a slot can serve, the stack.
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
#[derive(Clone, Copy, Debug, Hash, Mutate, PartialEq, Eq)]
pub enum TestScratchPolicy {
    /// One of the model machine's dedicated scratch registers, which no
    /// generated move can name and which is therefore always free.
    Free,

    /// A register the batch does not name, evicted into a scratch slot for
    /// the solver to put back afterwards.
    ///
    /// Falls back to a dedicated scratch when the batch leaves nothing worth
    /// evicting, which a small machine makes common.
    Evict,

    /// A scratch slot for a broken cycle to wait in, standing in for a real
    /// machine where the batch has a cycle through every register in a bank
    /// and so leaves nothing free and nothing worth evicting.
    ///
    /// A move from one slot to another cannot be served this way, needing
    /// somewhere a machine can move memory through, so those still get a
    /// dedicated scratch register.
    Park,
}

impl Default for TestScratchPolicy {
    fn default() -> Self {
        TestScratchPolicy::Free
    }
}

/// How much of the model machine there is, in a form `mutatis` can vary.
///
/// What the machine is made *of* is fixed: register names one or two units
/// wide, spill slots of those same two widths, and private cells for the
/// scratches. Only the counts move, so a mutated shape is the same machine
/// grown or shrunk rather than a different machine, which is what lets
/// `TestParallelMoves::fixup` repair a batch whose machine changed under it
/// rather than having to throw it away.
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct TestMachineShape {
    /// How many register units the machine has.
    num_units: u8,

    /// How many spill slots generated moves may name.
    num_slots: u8,

    /// The ceiling on how many moves a batch holds.
    max_moves: u8,
}

impl Default for TestMachineShape {
    fn default() -> Self {
        // The shape shrinking heads back towards.
        TestMachineShape {
            num_units: 4,
            num_slots: 4,
            max_moves: 8,
        }
    }
}

impl TestMachineShape {
    /// A model machine of the given size, with every dimension clamped into
    /// range.
    pub fn new(num_units: u8, num_slots: u8, max_moves: u8) -> Self {
        let mut shape = TestMachineShape {
            num_units,
            num_slots,
            max_moves,
        };
        shape.fixup();
        shape
    }

    /// The widest a register name, scratch or spill slot is.
    ///
    /// Fixed rather than varied: `TestMachineShape::encode` packs the width
    /// into a single bit, and "the last `MAX_WIDTH` slots are wide" is what
    /// leaves a wide move somewhere to go.
    const MAX_WIDTH: usize = 2;

    /// How many register units the machine may have.
    ///
    /// Few either way, so that generated batches collide and cycles arise on
    /// their own. The floor is `Self::MAX_WIDTH`, since the widest name has
    /// to fit in the machine.
    pub(crate) const UNITS: RangeInclusive<u8> = 2..=8;

    /// How many spill slots the machine may have.
    ///
    /// The floor is two, so that a move from one slot to another, the case
    /// that makes the solver ask for a scratch, can be written at all.
    /// Below `2 * MAX_WIDTH` every slot is wide, which is a shape worth
    /// solving too.
    pub(crate) const SLOTS: RangeInclusive<u8> = 2..=8;

    /// How many moves a batch may hold.
    ///
    /// The ceiling pays for itself twice over: the machine gives each move a
    /// scratch register and a scratch slot of its own at every width, so it
    /// is what sizes the cell space.
    pub(crate) const MOVES: RangeInclusive<u8> = 1..=12;

    /// Bring every dimension into range.
    ///
    /// Clamped rather than reduced modulo, because `x % n` is not idempotent
    /// once shifted off zero and `TestParallelMoves::fixup` has to be.
    fn fixup(&mut self) {
        let clamp =
            |value: u8, range: RangeInclusive<u8>| value.clamp(*range.start(), *range.end());
        self.num_units = clamp(self.num_units, Self::UNITS);
        self.num_slots = clamp(self.num_slots, Self::SLOTS);
        self.max_moves = clamp(self.max_moves, Self::MOVES);

        // Every name and index derived below has to be an entity this repr
        // can hold; `try_new` is what says so.
        Reg::<u32>::try_new(self.max_reg_names() + Self::MAX_WIDTH * self.num_scratches())
            .expect("the model machine's register names fit in the entity");
        SpillSlot::<u32>::try_new(self.total_slots())
            .expect("the model machine's spill slots fit in the entity");
    }

    /// How many register units the model machine has.
    pub(crate) fn num_units(&self) -> usize {
        usize::from(self.num_units)
    }

    /// How many spill slots the model machine has.
    pub(crate) fn num_slots(&self) -> usize {
        usize::from(self.num_slots)
    }

    /// The ceiling on how many moves a batch holds.
    pub(crate) fn max_moves(&self) -> usize {
        usize::from(self.max_moves)
    }

    /// The ceiling on register names: two more than there are register units,
    /// so that however small the machine is, some name must cover units
    /// another name already covers and the solver's `overlaps` closure does
    /// real work.
    pub(crate) fn max_reg_names(&self) -> usize {
        self.num_units() + 2
    }

    /// How many scratches of each width the model machine has, named outside
    /// the generated name table so that no generated move can reach them.
    ///
    /// A cycle break parks a value in one until its move is emitted, and
    /// partial overlap lets one batch have several parked at once, so one per
    /// move in the batch is always enough.
    fn num_scratches(&self) -> usize {
        self.max_moves()
    }

    /// How many spill slots of each width the scratch callback can hand out,
    /// numbered past the generated ones so that no generated move reaches
    /// them. One per move in the batch, for the same reason as
    /// `Self::num_scratches`.
    fn num_scratch_slots(&self) -> usize {
        self.max_moves()
    }

    /// Every spill slot, generated and scratch, at every width.
    fn total_slots(&self) -> usize {
        self.num_slots() + Self::MAX_WIDTH * self.num_scratch_slots()
    }

    /// Where the scratches' cells begin, after the register units that
    /// generated names cover.
    fn scratch_cells(&self) -> usize {
        self.num_units()
    }

    /// Where the spill slots' cells begin, after the scratches'.
    fn slot_cells(&self) -> usize {
        self.scratch_cells() + self.num_scratches() * Self::MAX_WIDTH * Self::MAX_WIDTH
    }

    /// Where the scratch spill slots' cells begin, after the generated ones'.
    fn scratch_slot_cells(&self) -> usize {
        self.slot_cells() + self.num_slots() * Self::MAX_WIDTH
    }

    /// How many cells the model machine has in all: one per register unit,
    /// plus private cells for each scratch and each spill slot.
    fn num_cells(&self) -> usize {
        self.slot_cells() + self.total_slots() * Self::MAX_WIDTH
    }

    /// The unit range a `regs` entry names: a width of one or two units, and a
    /// start that keeps the whole range inside the machine.
    fn decode(&self, byte: u8) -> (usize, usize) {
        let width = 1 + usize::from(byte & 1);
        let start = (usize::from(byte) >> 1) % (self.num_units() - width + 1);
        (start, width)
    }

    /// The canonical `regs` entry for a unit range, so that
    /// `TestParallelMoves::fixup` leaves equal ranges spelled the same way.
    fn encode(start: usize, width: usize) -> u8 {
        u8::try_from((start << 1) | (width - 1)).unwrap()
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
    fn slot_width(&self, slot: usize) -> usize {
        if let Some(scratch) = slot.checked_sub(self.num_slots()) {
            // A scratch slot: the first block is narrow and the second wide,
            // so that the callback has one of each width per move.
            1 + scratch / self.num_scratch_slots()
        } else if slot + Self::MAX_WIDTH >= self.num_slots() {
            Self::MAX_WIDTH
        } else {
            1
        }
    }
}

/// Pick a value for one dimension of the machine's shape, anywhere in range.
fn gen_dimension(ctx: &mut mutatis::Context, range: RangeInclusive<u8>) -> u8 {
    let span = usize::from(*range.end() - *range.start()) + 1;
    let offset = ctx.rng().gen_index(span).expect("the span is never empty");
    range.start() + u8::try_from(offset).unwrap()
}

/// Move one dimension of the machine's shape.
///
/// Shrinking picks something strictly smaller, so that a counterexample found
/// on a big machine reduces to one on a small machine, where there is less to
/// read and every name matters.
fn mutate_dimension(
    ctx: &mut mutatis::Context,
    value: &mut u8,
    range: RangeInclusive<u8>,
) -> mutatis::Result<()> {
    if !ctx.shrink() {
        *value = gen_dimension(ctx, range);
        return Ok(());
    }
    let min = *range.start();
    if *value <= min {
        return Err(mutatis::error::Error::exhausted());
    }
    *value = gen_dimension(ctx, min..=*value - 1);
    Ok(())
}

#[derive(Default)]
pub struct TestMachineShapeMutator {}

impl Mutate<TestMachineShape> for TestMachineShapeMutator {
    fn mutate(
        &mut self,
        mutations: &mut mutatis::Candidates<'_>,
        shape: &mut TestMachineShape,
    ) -> mutatis::Result<()> {
        mutations
            .mutation(|ctx| mutate_dimension(ctx, &mut shape.num_units, TestMachineShape::UNITS))?;
        mutations
            .mutation(|ctx| mutate_dimension(ctx, &mut shape.num_slots, TestMachineShape::SLOTS))?;
        mutations
            .mutation(|ctx| mutate_dimension(ctx, &mut shape.max_moves, TestMachineShape::MOVES))?;
        Ok(())
    }
}

impl Generate<TestMachineShape> for TestMachineShapeMutator {
    fn generate(&mut self, ctx: &mut mutatis::Context) -> mutatis::Result<TestMachineShape> {
        Ok(TestMachineShape {
            num_units: gen_dimension(ctx, TestMachineShape::UNITS),
            num_slots: gen_dimension(ctx, TestMachineShape::SLOTS),
            max_moves: gen_dimension(ctx, TestMachineShape::MOVES),
        })
    }
}

impl DefaultMutate for TestMachineShape {
    type DefaultMutate = TestMachineShapeMutator;
}

/// One generated move, `dst := src`.
#[derive(Clone, Copy, Debug, Default, Hash, Mutate)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
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
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
pub struct TestParallelMoves {
    /// How big the model machine is: how many register units it has, how
    /// many spill slots, and how many moves a batch may hold.
    shape: TestMachineShape,

    /// For each register name, the range of register units it covers, as a
    /// width of one or two units and a start. See `TestMachineShape::decode`.
    regs: Vec<u8>,

    /// The moves in the batch.
    moves: Vec<TestMove>,

    /// What the scratch callback hands out.
    scratch: TestScratchPolicy,
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

    /// Did the callback have to evict a register to answer, so that the
    /// solver owed a save above the batch and a reload below it?
    pub evicted: bool,

    /// Did a broken cycle have to park on the stack because the callback had
    /// no register to give it at all?
    pub parked_on_the_stack: bool,

    /// Did the solver satisfy a scratch out of its own pool, a register the
    /// batch had already finished with, rather than asking for one?
    pub used_pooled_scratch: bool,
}

impl Default for TestParallelMoves {
    fn default() -> Self {
        let mut moves = TestParallelMoves {
            shape: TestMachineShape::default(),
            regs: Vec::new(),
            moves: Vec::new(),
            scratch: TestScratchPolicy::Free,
        };
        moves.fixup();
        moves
    }
}

impl TestParallelMoves {
    /// A batch of moves on the default model machine with the given register
    /// names, repaired to satisfy the solver's preconditions.
    pub fn new(regs: Vec<u8>, moves: Vec<TestMove>, scratch: TestScratchPolicy) -> Self {
        Self::with_shape(TestMachineShape::default(), regs, moves, scratch)
    }

    /// The same, on a model machine of the given shape.
    pub fn with_shape(
        shape: TestMachineShape,
        regs: Vec<u8>,
        moves: Vec<TestMove>,
        scratch: TestScratchPolicy,
    ) -> Self {
        let mut this = TestParallelMoves {
            shape,
            regs,
            moves,
            scratch,
        };
        this.fixup();
        this
    }

    /// Clamp the model machine's size, bring every name and index in range,
    /// and drop moves the solver's preconditions do not allow.
    pub fn fixup(&mut self) {
        // The machine first: everything below is measured against it, so a
        // shape still out of range would take the rest out of range with it.
        self.shape.fixup();
        let shape = self.shape;

        self.regs.truncate(shape.max_reg_names());
        if self.regs.is_empty() {
            self.regs.push(TestMachineShape::encode(0, 1));
        }
        for reg in &mut self.regs {
            let (start, width) = shape.decode(*reg);
            *reg = TestMachineShape::encode(start, width);
        }

        self.moves.truncate(shape.max_moves());
        let num_names = u8::try_from(self.regs.len()).unwrap();
        for m in &mut self.moves {
            for loc in [&mut m.src, &mut m.dst] {
                match loc {
                    TestLocation::Reg(name) => *name %= num_names,
                    TestLocation::Slot(slot) => *slot %= shape.num_slots,
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

    /// A `regs` table naming every register unit of `shape` once, so that no
    /// two names overlap.
    pub fn disjoint_regs(shape: &TestMachineShape) -> Vec<u8> {
        (0..shape.num_units())
            .map(|s| TestMachineShape::encode(s, 1))
            .collect()
    }

    fn intersect(a: &Range<usize>, b: &Range<usize>) -> bool {
        a.start < b.end && b.start < a.end
    }

    /// The moves in this batch.
    pub fn moves(&self) -> &[TestMove] {
        &self.moves
    }

    /// The model machine this batch is on.
    #[cfg(test)]
    pub(crate) fn shape(&self) -> &TestMachineShape {
        &self.shape
    }

    /// This batch's register names, one unit range each.
    #[cfg(test)]
    pub(crate) fn regs(&self) -> &[u8] {
        &self.regs
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

    /// The scratch registers of a given width, which no generated move names.
    fn scratches(&self, width: usize) -> impl Iterator<Item = Reg<u32>> {
        let base = self.shape.max_reg_names() + (width - 1) * self.shape.num_scratches();
        (base..base + self.shape.num_scratches()).map(|name| Reg::try_new(name).unwrap())
    }

    /// The scratch spill slots of a given width, which no generated move
    /// names.
    fn scratch_slots(&self, width: usize) -> impl Iterator<Item = SpillSlot<u32>> {
        let base = self.shape.num_slots() + (width - 1) * self.shape.num_scratch_slots();
        (base..base + self.shape.num_scratch_slots()).map(|i| SpillSlot::try_new(i).unwrap())
    }

    /// The model machine's cells that this allocation covers.
    ///
    /// Two allocations overlap exactly when their cells do, so overlap can be
    /// partial: a two-unit name covers two one-unit names that do not cover
    /// each other. Scratches and spill slots get cells of their own, so they
    /// overlap nothing but themselves.
    fn cells(&self, alloc: ScalarAllocation<u32>) -> Range<usize> {
        match alloc {
            ScalarAllocation::Reg(reg) => match reg.index().checked_sub(self.shape.max_reg_names())
            {
                Some(scratch) => {
                    let base = self.shape.scratch_cells() + scratch * TestMachineShape::MAX_WIDTH;
                    base..base + 1 + scratch / self.shape.num_scratches()
                }
                None => {
                    let (start, width) = self.shape.decode(self.regs[reg.index()]);
                    start..start + width
                }
            },
            ScalarAllocation::Stack(slot) => {
                let base = self.shape.slot_cells() + slot.index() * TestMachineShape::MAX_WIDTH;
                base..base + self.shape.slot_width(slot.index())
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
            .enumerate()
            .map(|(i, m)| {
                // The solver only ever carries a value along; it never reads
                // one. Numbering them is enough to tell one move's from
                // another's as they come back out.
                ParallelMove::new(
                    Val::try_new(i).unwrap(),
                    self.allocation(m.src),
                    self.allocation(m.dst),
                )
            })
            .collect();

        let mut solver = ParallelMoveSolver::new();
        let mut out = Vec::new();

        let mut source = OracleSource {
            machine: self,
            batch: &batch,
            evicted_regs: Vec::new(),
            slots_spent: 0,
            wanted_scratch: false,
            routed_stack_to_stack: false,
            nested_scratch: false,
            routed_wide_stack_to_stack: false,
            concurrent_scratches: false,
            used_pooled_scratch: false,
            evicted: false,
            parked_on_the_stack: false,
        };
        let result = solver.solve(batch.iter().copied(), &mut source, &mut out);

        if !solver.is_reset() {
            return Err("the solver is not reset after solving a batch".to_string());
        }

        match result {
            Ok(()) => {}
            Err(SolveError::EntityReprTooSmall) => {
                return Err(format!(
                    "the solver ran out of move indices for a batch of {} moves",
                    self.moves.len(),
                ));
            }
        }

        // Run the sequence, starting each cell off holding its own distinct
        // value.
        let mut state: Vec<usize> = (0..self.shape.num_cells()).collect();
        for m in &out {
            if matches!(
                (m.src(), m.dst()),
                (ScalarAllocation::Stack(_), ScalarAllocation::Stack(_))
            ) {
                return Err(format!(
                    "the solver emitted the stack-to-stack move {m:?}, which no machine \
                     can perform in one instruction",
                ));
            }
            let src = self.cells(m.src());
            let dst = self.cells(m.dst());
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
            let src = self.cells(m.src());
            let dst = self.cells(m.dst());
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
        let mut written = vec![false; self.shape.num_cells()];
        written[self.shape.scratch_cells()..self.shape.slot_cells()].fill(true);
        written[self.shape.scratch_slot_cells()..].fill(true);
        for m in &batch {
            written[self.cells(m.dst())].fill(true);
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
            .filter(|m| !self.overlaps(m.src(), m.dst()))
            .count();

        Ok(TestParallelMovesOutcome {
            emitted: out.len(),
            non_trivial,
            wanted_scratch: source.wanted_scratch,
            routed_stack_to_stack: source.routed_stack_to_stack,
            nested_scratch: source.nested_scratch,
            routed_wide_stack_to_stack: source.routed_wide_stack_to_stack,
            concurrent_scratches: source.concurrent_scratches,
            evicted: source.evicted,
            parked_on_the_stack: source.parked_on_the_stack,
            used_pooled_scratch: source.used_pooled_scratch,
        })
    }

    /// Names that alias partially: name 0 covers unit `0..1`, name 1 covers
    /// `1..2`, and name 2 spans both, so name 2's value is destroyed by two
    /// writes that do not touch each other. Slot 2 is one of the wide ones,
    /// and so is where a two-unit value spills.
    ///
    /// A seed rather than only a test, because this is the corner the search
    /// will not stumble into on its own: every other seed's names either alias
    /// exactly or not at all, and no mutation of one of those reaches here.
    pub fn partially_aliasing_names() -> Self {
        Self::new(
            vec![0, 2, 1],
            vec![
                mv(reg(2), slot(2)),
                mv(slot(0), reg(0)),
                mv(slot(1), reg(1)),
            ],
            TestScratchPolicy::Free,
        )
    }

    /// Two cycles that share a source covered by two disjoint writes, so that
    /// breaking one of them does not free the other: the solver holds two
    /// scratches at once, the behavior `two_cycle_breaks_are_live_at_once`
    /// pins down by hand.
    ///
    /// The name table is every name the model machine has, so `reg(2)`,
    /// `reg(4)` and `reg(5)` cover units `1..2`, `2..3` and `2..4`, and
    /// `reg(3)` covers `1..3`, which the writes to `reg(2)` and `reg(5)`
    /// destroy between them without touching each other. Those two writes and
    /// the move out of `reg(3)` form a three-cycle, and the two moves through
    /// `slot(3)` form a second one inside it.
    ///
    /// A seed rather than only a test: the shape is vanishingly rare under
    /// random mutation, since essentially none of the batches the search
    /// reaches on its own breaks a second cycle while the first is still
    /// parked. Without it, the whole behavior that `parked` and a
    /// multi-element `ScratchPool::unavailable` exist for would go
    /// unsearched.
    pub fn two_concurrent_cycle_breaks() -> Self {
        Self::new(
            vec![0, 1, 2, 3, 4, 5],
            vec![mv(reg(4), reg(2)), mv(slot(3), reg(5)), mv(reg(3), slot(3))],
            TestScratchPolicy::Free,
        )
    }

    /// The smallest machine the shape allows: two register units, two spill
    /// slots and a single register name covering the whole machine.
    ///
    /// Both slots are wide, since the last `MAX_WIDTH` of them always are, so
    /// every move here is two units wide and the one name a generated move
    /// can use is the one the swap itself needs. Swapping the two slots is
    /// then the tightest corner the model has: the staging register and the
    /// register the cycle parks in both have to come from outside the batch.
    ///
    /// A seed rather than only a test, because mutation has to shrink the
    /// machine and write the wide swap at the same time to arrive here, and
    /// each is unlikely on its own.
    pub fn a_two_unit_machine() -> Self {
        Self::with_shape(
            TestMachineShape::new(2, 2, 4),
            // One name, two units wide, starting at unit zero.
            vec![1],
            vec![mv(slot(0), slot(1)), mv(slot(1), slot(0))],
            TestScratchPolicy::Free,
        )
    }

    /// A cycle running through every register the machine has, so there is no
    /// register free to break it with and none worth evicting either: the
    /// save would have to go above the very move that fills the victim. The
    /// scratch has to be a slot.
    ///
    /// A seed rather than only a test, because saturating a bank takes a batch
    /// whose moves happen to name every register at once, and the search does
    /// not stumble into that from the wider machines the other seeds use.
    pub fn a_cycle_through_every_register() -> Self {
        Self::with_shape(
            TestMachineShape::new(2, 2, 4),
            // Two names, one unit wide each, so the swap below covers the
            // machine's registers exactly.
            vec![0, 2],
            vec![mv(reg(0), reg(1)), mv(reg(1), reg(0))],
            TestScratchPolicy::Park,
        )
    }

    /// A six-unit machine where the pool offers a register covering half of a
    /// cycle break's own source. See
    /// `a_pooled_scratch_never_overlaps_the_move_it_serves`.
    pub fn a_scratch_that_halves_its_own_source() -> Self {
        Self::with_shape(
            TestMachineShape::new(6, 2, 4),
            vec![0, 7, 5, 0, 0, 4, 0, 9],
            vec![
                mv(slot(0), reg(2)),
                mv(slot(1), reg(7)),
                mv(reg(1), slot(0)),
            ],
            TestScratchPolicy::Free,
        )
    }

    /// A two-unit machine where a move emitted after a cycle break reads the
    /// register the break parked into. See
    /// `a_held_scratch_is_untouched_by_the_moves_around_it`.
    pub fn a_scratch_read_out_from_under_a_cycle() -> Self {
        Self::with_shape(
            TestMachineShape::new(2, 8, 12),
            vec![0, 2, 0, 1],
            vec![
                mv(slot(0), reg(1)),
                mv(reg(2), slot(4)),
                mv(slot(4), reg(0)),
                mv(reg(3), slot(7)),
            ],
            TestScratchPolicy::Evict,
        )
    }

    /// This batch written as the `TestParallelMoves::with_shape` call that
    /// rebuilds it.
    pub fn as_test_case(&self) -> String {
        fn render(loc: TestLocation) -> String {
            match loc {
                TestLocation::Reg(name) => format!("reg({name})"),
                TestLocation::Slot(slot) => format!("slot({slot})"),
            }
        }

        let mut s = String::from("TestParallelMoves::with_shape(\n");
        s.push_str(&format!(
            "    TestMachineShape::new({}, {}, {}),\n",
            self.shape.num_units(),
            self.shape.num_slots(),
            self.shape.max_moves(),
        ));

        s.push_str("    vec![");
        for (i, byte) in self.regs.iter().enumerate() {
            if i > 0 {
                s.push_str(", ");
            }
            s.push_str(&byte.to_string());
        }
        s.push_str("],\n");

        if self.moves.is_empty() {
            s.push_str("    vec![],\n");
        } else {
            s.push_str("    vec![\n");
            for m in &self.moves {
                s.push_str(&format!(
                    "        mv({}, {}),\n",
                    render(m.src),
                    render(m.dst)
                ));
            }
            s.push_str("    ],\n");
        }

        s.push_str(&format!("    TestScratchPolicy::{:?},\n)", self.scratch));
        s
    }
}

fn reg(name: u8) -> TestLocation {
    TestLocation::Reg(name)
}

fn slot(index: u8) -> TestLocation {
    TestLocation::Slot(index)
}

fn mv(src: TestLocation, dst: TestLocation) -> TestMove {
    TestMove { src, dst }
}

/// Everything the solver asks of the model machine, and the record of what it
/// asked for.
struct OracleSource<'a> {
    /// The model machine the batch runs on.
    machine: &'a TestParallelMoves,

    /// The batch being solved.
    batch: &'a [ParallelMove<u32>],

    /// The registers we have evicted so far, and how many scratch slots we
    /// have spent keeping their contents. Several evictions can be live at
    /// once, so each needs a slot and a victim of its own.
    evicted_regs: Vec<ScalarAllocation<u32>>,
    slots_spent: usize,

    // Which corners this batch reached; see `TestParallelMovesOutcome`, which
    // is where these end up.
    wanted_scratch: bool,
    routed_stack_to_stack: bool,
    nested_scratch: bool,
    routed_wide_stack_to_stack: bool,
    concurrent_scratches: bool,
    used_pooled_scratch: bool,
    evicted: bool,
    parked_on_the_stack: bool,
}

impl OracleSource<'_> {
    /// Note what this request says about the batch, and answer how wide a
    /// scratch it wants.
    ///
    /// Every rung of the ladder starts here rather than only the rung that
    /// ends up answering, so that what the solver *asked* for is counted even
    /// when the first rung turns it down. The flags are all idempotent, so
    /// climbing past a rung counts nothing twice.
    fn note(
        &mut self,
        mv: ParallelMove<u32>,
        reason: ScratchReason,
        unavailable: &[ScalarAllocation<u32>],
    ) -> usize {
        self.wanted_scratch = true;
        let width = self.machine.cells(mv.dst()).len();
        match reason {
            ScratchReason::StackToStack => {
                self.routed_stack_to_stack = true;
                self.nested_scratch |= !unavailable.is_empty();
                self.routed_wide_stack_to_stack |= width > 1;
            }
            ScratchReason::CycleBreak => {
                // Anything already parked belongs to a cycle this one did not
                // free.
                self.concurrent_scratches |= !unavailable.is_empty();
            }
        }
        width
    }

    /// A dedicated scratch register of `width`: whichever one is not already
    /// spoken for, since other cycle breaks in this batch may still have
    /// values parked, and a move may sit inside one of them.
    fn dedicated(&self, width: usize, unavailable: &[ScalarAllocation<u32>]) -> Reg<u32> {
        self.machine
            .scratches(width)
            .find(|&s| {
                let s = ScalarAllocation::Reg(s);
                unavailable.iter().all(|&a| !self.machine.overlaps(s, a))
            })
            .expect("the solver wants more scratch registers at once than the model has")
    }
}

impl ScratchSource<u32> for OracleSource<'_> {
    fn overlaps(&self, a: ScalarAllocation<u32>, b: ScalarAllocation<u32>) -> bool {
        self.machine.overlaps(a, b)
    }

    fn is_suitable(
        &mut self,
        mv: ParallelMove<u32>,
        _reason: ScratchReason,
        reg: Reg<u32>,
    ) -> bool {
        // The solver only offers registers the batch is finished with, and
        // takes the first one we approve. All we have to say is whether the
        // value fits in it.
        let reg = ScalarAllocation::Reg(reg);
        if self.machine.cells(reg).len() != self.machine.cells(mv.dst()).len() {
            return false;
        }
        self.used_pooled_scratch = true;
        true
    }

    fn find_free(
        &mut self,
        mv: ParallelMove<u32>,
        reason: ScratchReason,
        unavailable: &[ScalarAllocation<u32>],
    ) -> Option<Reg<u32>> {
        let width = self.note(mv, reason, unavailable);

        match self.machine.scratch {
            // Answering here is the whole of this policy.
            TestScratchPolicy::Free => {}

            // The rung below does the answering.
            TestScratchPolicy::Evict => return None,

            // A broken cycle is meant to reach the stack, so say nothing and
            // let it fall all the way through. A move from one slot to another
            // cannot park, needing somewhere a machine can route memory
            // through, which a third slot is not, so it is answered here as
            // usual.
            TestScratchPolicy::Park if reason == ScratchReason::CycleBreak => return None,
            TestScratchPolicy::Park => {}
        }

        Some(self.dedicated(width, unavailable))
    }

    fn evict(
        &mut self,
        mv: ParallelMove<u32>,
        reason: ScratchReason,
        unavailable: &[ScalarAllocation<u32>],
        _spent: &[Reg<u32>],
        evicting: &mut Vec<(Reg<u32>, SpillSlot<u32>)>,
    ) -> Result<Option<Reg<u32>>, SolveError> {
        let width = self.note(mv, reason, unavailable);

        if self.machine.scratch == TestScratchPolicy::Park {
            return Ok(None);
        }

        // A register we can evict: one of the right width that the batch
        // never names, that no earlier eviction has taken, and that nothing
        // parked overlaps. Anything the batch can see is out, because the save
        // sits above the whole batch and the reload below it.
        //
        // Picking one nothing else can see is also what keeps the evicted set
        // a single register. Writing it disturbs whatever shares its
        // cells, but sharing a cell is what `overlaps` answers, so everything
        // sharing one has just been ruled out along with the batch, the parked
        // values and the earlier evictions. Saving and restoring exactly this
        // register's cells then puts back exactly what writing them lost.
        let victim = (0..self.machine.regs.len())
            .map(|name| Reg::try_new(name).unwrap())
            .find(|&reg| {
                let reg = ScalarAllocation::Reg(reg);
                self.machine.cells(reg).len() == width
                    && self.batch.iter().all(|m| {
                        !self.machine.overlaps(reg, m.src()) && !self.machine.overlaps(reg, m.dst())
                    })
                    && self
                        .evicted_regs
                        .iter()
                        .all(|&d| !self.machine.overlaps(reg, d))
                    && unavailable.iter().all(|&a| !self.machine.overlaps(reg, a))
            });

        if let Some(reg) = victim {
            // Scratch slots are ours alone, and we never hand the same one out
            // twice, so two live evictions cannot collide.
            let slot = self
                .machine
                .scratch_slots(width)
                .nth(self.slots_spent)
                .expect("the solver wants more evictions at once than the model has slots");
            self.slots_spent += 1;
            self.evicted_regs.push(ScalarAllocation::Reg(reg));
            evicting.push((reg, slot));
            self.evicted = true;
            return Ok(Some(reg));
        }

        // Nothing was worth evicting, so fall back to a dedicated scratch,
        // which evicts nothing at all.
        Ok(Some(self.dedicated(width, unavailable)))
    }

    fn emergency_slot(
        &mut self,
        mv: ParallelMove<u32>,
        reason: ScratchReason,
        unavailable: &[ScalarAllocation<u32>],
    ) -> Result<SpillSlot<u32>, SolveError> {
        let width = self.note(mv, reason, unavailable);
        let slot = self
            .machine
            .scratch_slots(width)
            .find(|&s| {
                let s = ScalarAllocation::Stack(s);
                unavailable.iter().all(|&a| !self.machine.overlaps(s, a))
            })
            .expect("the solver wants more parking slots at once than the model has");
        self.parked_on_the_stack = true;
        Ok(slot)
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
            <TestMachineShape as DefaultMutate>::DefaultMutate::default()
                .mutate(mutations, &mut moves.shape)?;
            <Vec<u8> as DefaultMutate>::DefaultMutate::default()
                .mutate(mutations, &mut moves.regs)?;
            <Vec<TestMove> as DefaultMutate>::DefaultMutate::default()
                .mutate(mutations, &mut moves.moves)?;
            <TestScratchPolicy as DefaultMutate>::DefaultMutate::default()
                .mutate(mutations, &mut moves.scratch)?;
            Ok(())
        })();

        moves.fixup();
        result
    }
}

impl Generate<TestParallelMoves> for TestParallelMovesMutator {
    fn generate(&mut self, context: &mut mutatis::Context) -> mutatis::Result<TestParallelMoves> {
        let mut moves = TestParallelMoves {
            shape: <TestMachineShape as DefaultMutate>::DefaultMutate::default()
                .generate(context)?,
            regs: <Vec<u8> as DefaultMutate>::DefaultMutate::default().generate(context)?,
            moves: <Vec<TestMove> as DefaultMutate>::DefaultMutate::default().generate(context)?,
            scratch: <TestScratchPolicy as DefaultMutate>::DefaultMutate::default()
                .generate(context)?,
        };
        moves.fixup();
        Ok(moves)
    }
}

impl DefaultMutate for TestParallelMoves {
    type DefaultMutate = TestParallelMovesMutator;
}

/// The fixtures that `parallel_move_properties` and the `parallel_moves` fuzz
/// target both start from.
///
/// Each entry is a shape the solver has to get right: a chain, a swap, a
/// three-cycle, two disjoint cycles, a chain feeding a cycle, a move between
/// spill slots, a cycle with no scratch to break it with, etc...
pub fn parallel_moves_corpus() -> Vec<TestParallelMoves> {
    let regs = TestParallelMoves::disjoint_regs(&TestMachineShape::default());
    let with =
        |moves: Vec<TestMove>| TestParallelMoves::new(regs.clone(), moves, TestScratchPolicy::Free);
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
        TestParallelMoves::new(
            regs.clone(),
            vec![mv(slot(0), slot(1))],
            TestScratchPolicy::Evict,
        ),
        TestParallelMoves::new(
            regs.clone(),
            vec![mv(slot(0), slot(1)), mv(slot(1), slot(0))],
            TestScratchPolicy::Evict,
        ),
        TestParallelMoves::new(
            regs.clone(),
            vec![
                mv(reg(0), slot(0)),
                mv(slot(0), slot(1)),
                mv(slot(1), reg(0)),
            ],
            TestScratchPolicy::Evict,
        ),
        TestParallelMoves::new(
            regs.clone(),
            vec![mv(reg(0), reg(1)), mv(reg(1), reg(0))],
            TestScratchPolicy::Evict,
        ),
        TestParallelMoves::new(
            vec![0, 0, 2],
            vec![mv(reg(0), reg(2)), mv(reg(2), reg(1))],
            TestScratchPolicy::Free,
        ),
        TestParallelMoves::partially_aliasing_names(),
        TestParallelMoves::two_concurrent_cycle_breaks(),
        TestParallelMoves::a_two_unit_machine(),
        TestParallelMoves::a_scratch_that_halves_its_own_source(),
        TestParallelMoves::a_scratch_read_out_from_under_a_cycle(),
        TestParallelMoves::a_cycle_through_every_register(),
        with(vec![mv(slot(2), slot(3))]),
    ]
}
