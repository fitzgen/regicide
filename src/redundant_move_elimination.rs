//! Redundant move elimination.
//!
//! Move generation can, in certain cases, move a value into a location where
//! that location already contains the value. We call these *redundant
//! moves*. For example, values have a unique stack home: whenever a value is
//! spilled, it is always spilled to the same slot, and therefore that spill
//! slot will always contain the value in the range between (a) a spill of the
//! value, and (b) the value's last use (the slot may be reused for other values
//! after this one is not live anymore). Therefore, a spill that is dominated by
//! another spill of the same value is always redundant: the other spill must
//! happen first, because of dominance, and the value must still be live if it
//! is being spilled again, so the spill slot already contains the
//! value. Re-spilling, in this situation, is idempotent, so it doesn't affect
//! correctness, but removing it improves codegen and performance. There are
//! also scenarios where generated register-to-register moves and
//! stack-to-register reloads happen to be redundant.
//!
//! This pass identifies redundant moves and eliminates them. It does not
//! identify or remove dead moves (a move into a location which is then never
//! read before it is overwritten again or the program terminates).
//!
//! This pass implements the same analysis that the checker does, but with the
//! goal of optimizing the program rather than checking its correctness: a
//! flow-sensitive "must" analysis over a lattice that tracks, for each machine
//! location, the set of values a location currently contains at a given program
//! point. The meet function is set intersection. Non-allocatable registers are
//! untracked.
//!
//! Moving a value into a location that the analysis has determined already
//! contains that value identifies a redundant move. After identifying all
//! redundant moves, we remove them all in one batch.

use crate::{
    Entity as _, Input,
    context::ContextInner,
    counts::Counts,
    entity::{
        Block, EntityRange, EntityRepr, EntitySet, Inst, PrimaryMap, SecondaryMap,
        TerminatorFactsStorageIndex, Val, WrittenPartsStorageIndex,
    },
    error::IResult,
    events::EventsLog,
    input::{DefUse, InputBlock, InputFunction, InputInst, MoveEliminationLevel},
    liveness::Liveness,
    machine::{Interfere, Machine, Reg},
    move_generation::{MoveGeneration, MovePosition},
    output::{
        Allocation, CriticalEdgeEdit, EdgeEdit, Edit, InstOrEdit, Move, OutputInner, RegAllocation,
        Remat, ScalarAllocation, StackAllocation, block_iter,
    },
    rpo::Rpo,
    spill_slot_allocation::{SpillSlot, SpillSlots},
    timing::Timing,
};
use alloc::vec::Vec;
use core::{cmp::Ordering, ops::Range};

macro_rules! test_stat {
    ( $me:expr, $field:ident ) => {{
        #[cfg(test)]
        {
            $me.test_stats.$field += 1;
        }
    }};
}

/// Run the redundant-move elimination pass.
pub(crate) fn eliminate_redundant_moves<E>(
    context: &mut ContextInner<E>,
    input: &Input<'_, impl InputFunction>,
) -> IResult<()>
where
    E: EntityRepr,
{
    let level = input.options.redundant_move_elimination_level;
    if level == MoveEliminationLevel::None {
        return Ok(());
    }

    let _timing = Timing::new("eliminate redundant moves");

    {
        let mut eliminator = Eliminator {
            input,
            output: &context.output,
            move_generation: &context.move_generation,
            spill_slots: &context.spill_slots,
            rpo: &context.rpo,
            liveness: &context.liveness,
            counts: &mut context.counts,
            events: &mut context.events,
            me: &mut context.redundant_move_elimination,
        };
        eliminator.run(level);
    }

    context
        .redundant_move_elimination
        .eliminated
        .sort_unstable();
    debug_assert!(
        context
            .redundant_move_elimination
            .eliminated
            .windows(2)
            .all(|w| w[0] != w[1]),
        "must have no duplicates",
    );

    // The edits are removed by `crate::remove_eliminated_edits`, once dead-move
    // elimination has run too.
    Ok(())
}

/// One register's worth of a value.
///
/// For values that fit in a single register, this holds the whole value and
/// `index` is always zero.
///
/// For values that fit in multiple registers, as part of a `RegGroup`, this
/// holds the `index`th part of the value that fits in a register.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Part<E>
where
    E: EntityRepr,
{
    val: Val<E>,
    index: u8,
}

const _U8_INDEX_HOLDS_ALL_PARTS: () = assert!(crate::RegGroup::MAX_SIZE < (u8::MAX as usize));

/// One machine location, and one part it is known to hold.
pub(crate) type Fact<E> = (ScalarAllocation<E>, Part<E>);

/// What the machine holds: the parts each location is known to contain.
#[derive(Clone, Debug, PartialEq, Eq)]
struct State<E>
where
    E: EntityRepr,
{
    /// A sorted, deduplicated list of pairs, so a location's parts are a
    /// contiguous run that two binary searches locate.
    ///
    /// A location with no run holds bottom: nothing is known about it, not that
    /// it is empty.
    facts: Vec<Fact<E>>,
}

/// Hand-written rather than derived, so that `mem::take` does not want an
/// `E: Default` that says nothing about a representation.
impl<E> Default for State<E>
where
    E: EntityRepr,
{
    fn default() -> Self {
        Self { facts: Vec::new() }
    }
}

impl<E> State<E>
where
    E: EntityRepr,
{
    fn clear(&mut self) {
        self.facts.clear();
    }

    /// Replace everything known with `facts`, which must already be sorted and
    /// deduplicated.
    fn reset_to(&mut self, facts: &[Fact<E>]) {
        debug_assert!(facts.windows(2).all(|w| w[0] < w[1]));
        self.facts.clear();
        self.facts.extend_from_slice(facts);
    }

    /// Where `loc`'s parts sit within `facts`.
    fn range_of(&self, loc: ScalarAllocation<E>) -> Range<usize> {
        let lo = self.facts.partition_point(|&(other, _)| other < loc);

        // TODO: It is likely that `hi` is very near `lo`; we should investigate
        // using a galloping search here, instead of a second binary search, to
        // avoid cache misses.
        let hi = lo + self.facts[lo..].partition_point(|&(other, _)| other == loc);

        lo..hi
    }

    /// The facts about `loc`, which are `loc` paired with each part it holds.
    fn parts(&self, loc: ScalarAllocation<E>) -> &[Fact<E>] {
        &self.facts[self.range_of(loc)]
    }

    /// Does `loc` hold `part`?
    fn holds(&self, loc: ScalarAllocation<E>, part: Part<E>) -> bool {
        self.facts.binary_search(&(loc, part)).is_ok()
    }

    /// Does `to` already hold every part `from` holds?
    fn subsumes(&self, to: ScalarAllocation<E>, from: ScalarAllocation<E>) -> bool {
        let mut from = self.parts(from);
        if from.is_empty() {
            return false;
        }

        let mut to = self.parts(to);
        while let Some(&(_, wanted)) = from.first() {
            let Some(&(_, held)) = to.first() else {
                return false;
            };
            match held.cmp(&wanted) {
                Ordering::Less => to = &to[1..],
                Ordering::Greater => return false,
                Ordering::Equal => {
                    to = &to[1..];
                    from = &from[1..];
                }
            }
        }

        true
    }

    /// Forget the contents of every location that overlaps `loc`.
    fn clobber(&mut self, machine: &Machine, loc: ScalarAllocation<E>) {
        self.facts
            .retain(|&(other, _)| !Interfere::interfere(machine, other, loc));
    }

    /// Record that `loc` holds `part`, alongside whatever else it holds.
    fn insert(&mut self, loc: ScalarAllocation<E>, part: Part<E>) {
        if let Err(i) = self.facts.binary_search(&(loc, part)) {
            self.facts.insert(i, (loc, part));
        }
    }

    /// Record that `loc` holds exactly `parts`, which must be sorted and
    /// deduplicated.
    fn set(&mut self, loc: ScalarAllocation<E>, parts: &[Part<E>]) {
        debug_assert!(parts.windows(2).all(|w| w[0] < w[1]));
        let range = self.range_of(loc);
        self.facts
            .splice(range, parts.iter().map(|&part| (loc, part)));
    }

    /// Forget every part of `val`, wherever it is.
    fn kill(&mut self, val: Val<E>) {
        self.facts.retain(|&(_, part)| part.val != val);
    }

    /// Copy what `from` holds into `to`, as a move that really happens does.
    fn copy_into(
        &mut self,
        machine: &Machine,
        to: ScalarAllocation<E>,
        from: ScalarAllocation<E>,
        scratch: &mut Vec<Part<E>>,
    ) {
        scratch.clear();
        scratch.extend(self.parts(from).iter().map(|&(_, part)| part));
        self.clobber(machine, to);
        self.set(to, scratch);
    }

    fn debug_assert_locations_are_disjoint(&self, machine: &Machine) {
        if !cfg!(debug_assertions) {
            return;
        }

        let mut i = 0;
        while i < self.facts.len() {
            let lhs = self.facts[i].0;
            while i < self.facts.len() && self.facts[i].0 == lhs {
                i += 1;
            }
            let mut j = i;
            while j < self.facts.len() {
                let rhs = self.facts[j].0;
                debug_assert!(
                    !Interfere::interfere(machine, lhs, rhs),
                    "the state holds both {lhs:?} and {rhs:?}, which overlap",
                );
                while j < self.facts.len() && self.facts[j].0 == rhs {
                    j += 1;
                }
            }
        }
    }
}

/// Where one block's entry state sits within `entry_facts`.
///
/// The meet only shrinks, so an entry state is rewritten in place with a
/// shorter `end`, leaving a gap rather than moving anything.
#[derive(Clone, Copy, Debug)]
struct Facts {
    start: usize,
    end: usize,
}

impl Facts {
    fn range(self) -> Range<usize> {
        self.start..self.end
    }
}

/// Where in a block's walk an edit sat. Only the coverage counts care: the
/// transfer is the same wherever the edit is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Place {
    /// Atop the block, and so belonging to the one edge arriving at it.
    BlockTop,

    /// Between the block's first instruction and its terminator.
    InBlock,

    /// Just before the terminator, where `move_generation::edge_position` puts
    /// an edge's moves when the block has one way out.
    Departing,

    /// On one of the block's outgoing critical edges.
    OnEdge,
}

/// Which of the pass's two walks over the control-flow graph is running.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    /// Computing the fixpoint over block entry states.
    Analyze,

    /// Deciding which edits to drop, against the settled states.
    Rewrite,
}

/// Reusable storage for the pass.
pub(crate) struct RedundantMoveElimination<E>
where
    E: EntityRepr,
{
    /// Contiguous storage for every reached block's entry state.
    entry_facts: Vec<Fact<E>>,

    /// Where each block's entry state lives within `entry_facts`, or `None` for
    /// a block the analysis has not reached.
    entry_state: SecondaryMap<Block<E>, Option<Facts>>,

    /// Blocks whose entry state changed since their successors were computed.
    worklist: Vec<Block<E>>,

    /// The set blocks in `self.worklist`.
    on_worklist: EntitySet<Block<E>>,

    /// The state to assume on entry to the function: where its parameters
    /// arrive.
    seed: State<E>,

    /// The state used in the currrent walk.
    state: State<E>,

    /// The state an outgoing edge is walked with.
    out: State<E>,

    /// Scratch space for one location's worth of parts.
    scratch: Vec<Part<E>>,

    /// Scratch space for the renaming an edge's block arguments perform.
    renamed: Vec<Fact<E>>,

    /// The block's outgoing critical-edge edits, as `(successor, edit index)`.
    edge_edits: Vec<(usize, usize)>,

    /// Scratch space for the single locations one allocation is made of.
    scalars: Vec<ScalarAllocation<E>>,

    /// The edits to remove, sorted, by index into the edit list as move
    /// generation left it. See `crate::remove_eliminated_edits`.
    pub(crate) eliminated: Vec<usize>,

    /// What the rewrite learned along the way, for demanded-move hoisting.
    pub(crate) recorded: Recorded<E>,

    #[cfg(test)]
    test_stats: TestStats,
}

/// What the rewrite walk knew at the points demanded-move hoisting asks about,
/// recorded as it went so that hoisting need not run the analysis again.
///
/// Only filled when `Recorded::enabled` was set before the pass ran.
pub(crate) struct Recorded<E>
where
    E: EntityRepr,
{
    /// Whether to record anything at all.
    pub(crate) enabled: bool,

    /// For each edit, by index into the edit list as move generation left it,
    /// where its written parts sit within `written_parts`, or `None` for an
    /// edit the rewrite eliminated or never reached.
    written: Vec<Option<EntityRange<WrittenPartsStorageIndex>>>,

    /// Contiguous storage for every surviving edit's written parts: what its
    /// destination holds after it runs, sorted and deduplicated.
    written_parts: PrimaryMap<WrittenPartsStorageIndex, Part<E>>,

    /// For each block whose state just before its terminator was recorded,
    /// where those facts sit within `before_terminator_facts`.
    before_terminator: SecondaryMap<Block<E>, Option<EntityRange<TerminatorFactsStorageIndex>>>,

    /// Contiguous storage for those states.
    before_terminator_facts: PrimaryMap<TerminatorFactsStorageIndex, Fact<E>>,
}

impl<E> Recorded<E>
where
    E: EntityRepr,
{
    const fn new() -> Self {
        Self {
            enabled: false,
            written: Vec::new(),
            written_parts: PrimaryMap::new(),
            before_terminator: SecondaryMap::new(None),
            before_terminator_facts: PrimaryMap::new(),
        }
    }

    fn reset(&mut self) {
        let Self {
            enabled,
            written,
            written_parts,
            before_terminator,
            before_terminator_facts,
        } = self;
        *enabled = false;
        written.clear();
        written_parts.reset();
        before_terminator.reset();
        before_terminator_facts.reset();
    }

    fn is_reset(&self) -> bool {
        let Self {
            enabled,
            written,
            written_parts,
            before_terminator,
            before_terminator_facts,
        } = self;
        !*enabled
            && written.is_empty()
            && written_parts.is_reset()
            && before_terminator.is_reset()
            && before_terminator_facts.is_reset()
    }

    /// The parts the edit at `index` leaves in its destination, which may be
    /// none at all, or `None` for an edit that is not happening.
    pub(crate) fn written(&self, index: usize) -> Option<&[Part<E>]> {
        let range = (*self.written.get(index)?)?;
        Some(self.written_parts.range(range))
    }

    /// The facts holding just before `block`'s terminator, if they were
    /// recorded.
    pub(crate) fn before_terminator(&self, block: Block<E>) -> Option<&[Fact<E>]> {
        Some(
            self.before_terminator_facts
                .range(self.before_terminator[block]?),
        )
    }

    fn record_written(&mut self, index: usize, parts: impl Iterator<Item = Part<E>>) {
        let start = self.written_parts.next_key_unwrap();
        for part in parts {
            self.written_parts.push_unwrap(part);
        }
        self.written[index] = Some(self.written_parts.range_from(start));
    }
}

impl<E> RedundantMoveElimination<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        Self {
            entry_facts: Vec::new(),
            entry_state: SecondaryMap::new(None),
            worklist: Vec::new(),
            on_worklist: EntitySet::new(),
            seed: State { facts: Vec::new() },
            state: State { facts: Vec::new() },
            out: State { facts: Vec::new() },
            scratch: Vec::new(),
            renamed: Vec::new(),
            edge_edits: Vec::new(),
            scalars: Vec::new(),
            eliminated: Vec::new(),
            recorded: Recorded::new(),
            #[cfg(test)]
            test_stats: TestStats::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            entry_facts,
            entry_state,
            worklist,
            on_worklist,
            seed,
            state,
            out,
            scratch,
            renamed,
            edge_edits,
            scalars,
            eliminated,
            recorded,
            #[cfg(test)]
            test_stats,
        } = self;
        entry_facts.clear();
        entry_state.reset();
        worklist.clear();
        on_worklist.reset();
        seed.clear();
        state.clear();
        out.clear();
        scratch.clear();
        renamed.clear();
        edge_edits.clear();
        scalars.clear();
        eliminated.clear();
        recorded.reset();
        #[cfg(test)]
        {
            *test_stats = TestStats::default();
        }
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            entry_facts,
            entry_state,
            worklist,
            on_worklist,
            seed,
            state,
            out,
            scratch,
            renamed,
            edge_edits,
            scalars,
            eliminated,
            recorded,
            #[cfg(test)]
                test_stats: _,
        } = self;
        entry_facts.is_empty()
            && entry_state.is_reset()
            && worklist.is_empty()
            && on_worklist.is_reset()
            && seed.facts.is_empty()
            && state.facts.is_empty()
            && out.facts.is_empty()
            && scratch.is_empty()
            && renamed.is_empty()
            && edge_edits.is_empty()
            && scalars.is_empty()
            && eliminated.is_empty()
            && recorded.is_reset()
    }
}

/// Expand an `Allocation` into `scalars`.
pub(crate) fn scalars_of<E>(
    machine: &Machine,
    spill_slots: &SpillSlots<E>,
    alloc: Allocation,
    scalars: &mut Vec<ScalarAllocation<E>>,
) where
    E: EntityRepr,
{
    scalars.clear();
    match alloc {
        Allocation::Reg(RegAllocation::Reg(reg)) => {
            scalars.push(ScalarAllocation::Reg(
                Reg::<E>::try_new(reg.index()).unwrap(),
            ));
        }
        Allocation::Reg(RegAllocation::RegGroup(group)) => scalars.extend(
            group
                .members(machine)
                .iter()
                .map(|&reg| ScalarAllocation::Reg(Reg::<E>::try_new(reg.index()).unwrap())),
        ),
        Allocation::Stack(StackAllocation::SpillSlot(slot)) => {
            scalars.push(ScalarAllocation::Stack(
                SpillSlot::<E>::try_new(slot.index()).unwrap(),
            ));
        }
        Allocation::Stack(StackAllocation::SpillSlotGroup(group)) => {
            let group = group.with_repr::<E>().unwrap();
            scalars.extend(
                group
                    .members(spill_slots)
                    .iter()
                    .map(|&slot| ScalarAllocation::Stack(slot)),
            );
        }
    }
}

/// The edit at `index` in the list move generation left, as the transfer it
/// performs.
///
/// A critical-edge edit wraps the transfer that runs on the edge; every other
/// edit is one already. The list is the single copy of all of them, so nothing
/// here needs its own.
pub(crate) fn edge_edit_at<E>(move_generation: &MoveGeneration<E>, index: usize) -> EdgeEdit<E>
where
    E: EntityRepr,
{
    match move_generation.edits()[index].1 {
        Edit::Move(mv) => EdgeEdit::Move(mv),
        Edit::Remat(remat) => EdgeEdit::Remat(remat),
        Edit::CriticalEdge(CriticalEdgeEdit { edit, .. }) => edit,
    }
}

/// The abstract interpreter itself, and everything it reads.
struct Eliminator<'a, E, F>
where
    E: EntityRepr,
    F: InputFunction,
{
    input: &'a Input<'a, F>,
    output: &'a OutputInner<E>,
    move_generation: &'a MoveGeneration<E>,
    spill_slots: &'a SpillSlots<E>,
    rpo: &'a Rpo<E>,
    liveness: &'a Liveness<E>,
    counts: &'a mut Counts,
    events: &'a mut EventsLog<E>,
    me: &'a mut RedundantMoveElimination<E>,
}

impl<E, F> Eliminator<'_, E, F>
where
    E: EntityRepr,
    F: InputFunction,
{
    /// Find everything to eliminate at `level`, leaving it in
    /// `RedundantMoveElimination::eliminated`.
    fn run(&mut self, level: MoveEliminationLevel) {
        debug_assert_ne!(level, MoveEliminationLevel::None);

        if level == MoveEliminationLevel::Global {
            self.seed_entry();
            self.analyze();
        }
        self.rewrite(level);
    }

    /// Work out the state on entry to the function: where its parameters arrive.
    fn seed_entry(&mut self) {
        let func = self.input.func;
        let machine = self.input.machine;
        let spill_slots = self.spill_slots;
        let output = self.output;

        let mut seed = core::mem::take(&mut self.me.seed);
        let mut scalars = core::mem::take(&mut self.me.scalars);
        seed.clear();

        let entry = func.entry_block();
        let input_entry = func.block(entry);
        let allocs = output.block_param_allocs(entry);
        for (param, alloc) in input_entry.params().zip(allocs) {
            let Some(alloc) = *alloc else {
                continue;
            };
            scalars_of(machine, spill_slots, alloc, &mut scalars);
            let param = Val::<E>::try_new(param.index()).unwrap();
            for (index, &loc) in scalars.iter().enumerate() {
                seed.insert(
                    loc,
                    Part {
                        val: param,
                        index: u8::try_from(index).unwrap(),
                    },
                );
            }
        }

        self.me.seed = seed;
        self.me.scalars = scalars;
    }

    /// Run the fixpoint over block entry states.
    fn analyze(&mut self) {
        let entry = Block::<E>::try_new(self.input.func.entry_block().index()).unwrap();
        let seed = core::mem::take(&mut self.me.seed);
        self.meet_into(entry, &seed);
        self.me.seed = seed;

        while let Some(block) = self.me.worklist.pop() {
            self.me.on_worklist.remove(block);
            self.visit_block(block, Mode::Analyze);
        }
    }

    /// Walk every block once more, now deciding what to drop.
    ///
    /// `Local` never ran the fixpoint, so every block starts from the empty
    /// state: the bottom of the lattice, and so sound.
    fn rewrite(&mut self, level: MoveEliminationLevel) {
        if self.me.recorded.enabled {
            let len = self.move_generation.edits().len();
            self.me.recorded.written.resize(len, None);
        }

        for block in self.rpo.iter() {
            // Unreachable, and so with no edits to drop.
            if level == MoveEliminationLevel::Global && self.me.entry_state[block].is_none() {
                continue;
            }

            self.visit_block(block, Mode::Rewrite);
        }
    }

    /// Meet the state arriving from a predecessor into `succ`'s entry state,
    /// and queue `succ` when that changed anything.
    fn meet_into(&mut self, succ: Block<E>, out: &State<E>) {
        match self.me.entry_state[succ] {
            None => {
                let start = self.me.entry_facts.len();
                self.me.entry_facts.extend_from_slice(&out.facts);
                let end = self.me.entry_facts.len();
                self.me.entry_state[succ] = Some(Facts { start, end });
                self.enqueue(succ);
            }
            Some(facts) => {
                // Keep only the facts `out` agrees with. Both are sorted, so
                // one cursor walks `out` as the retain walks the entry state.
                let existing = &mut self.me.entry_facts[facts.range()];
                let mut cursor = 0;
                let mut kept = 0;
                for i in 0..existing.len() {
                    let fact = existing[i];
                    while cursor < out.facts.len() && out.facts[cursor] < fact {
                        cursor += 1;
                    }
                    if cursor < out.facts.len() && out.facts[cursor] == fact {
                        existing[kept] = fact;
                        kept += 1;
                    }
                }

                if kept != existing.len() {
                    // Only ever shrinks, so rewrite in place and abandon the
                    // tail of the old range.
                    self.me.entry_state[succ] = Some(Facts {
                        start: facts.start,
                        end: facts.start + kept,
                    });
                    test_stat!(self.me, shrunk_entry_states);
                    self.enqueue(succ);
                }
            }
        }
    }

    /// Queue `block` for another analysis visit, if it is not queued already.
    fn enqueue(&mut self, block: Block<E>) {
        if self.me.on_worklist.insert(block) {
            self.me.worklist.push(block);
        }
    }

    /// The edge `block` takes its arriving edits from, as a predecessor and an
    /// outgoing edge index, if it takes any.
    fn arriving_edge(&self, block: Block<E>) -> Option<(Block<E>, usize)> {
        let func = self.input.func;
        let wide = block.with_repr32();
        let input_block = func.block(wide);
        if input_block.len_predecessors() != 1 || wide == func.entry_block() {
            return None;
        }
        let pred = input_block.predecessors().next()?;
        let index = func
            .block(pred)
            .successors()
            .position(|succ| succ == wide)?;
        Some((Block::<E>::try_new(pred.index()).unwrap(), index))
    }

    /// Walk `block`: run its edits and definitions against its entry state, and
    /// hand the result to each of its successors.
    ///
    /// `checker::visit_block` with every check deleted and one decision added.
    /// The order the pieces run in is the contract move generation placed the
    /// edits under; getting it wrong is invisible at `Local` and wrong at
    /// `Global`.
    fn visit_block(&mut self, block: Block<E>, mode: Mode) {
        let func = self.input.func;
        let machine = self.input.machine;
        let move_generation = self.move_generation;
        let wide = block.with_repr32();
        let input_block = func.block(wide);

        if mode == Mode::Analyze {
            test_stat!(self.me, block_revisits);
        }

        let mut state = core::mem::take(&mut self.me.state);
        let mut out = core::mem::take(&mut self.me.out);
        let mut edge_edits = core::mem::take(&mut self.me.edge_edits);

        state.clear();
        if let Some(facts) = self.me.entry_state[block] {
            let entry = &self.me.entry_facts[facts.range()];
            state.facts.extend_from_slice(entry);
        }
        edge_edits.clear();

        #[cfg(test)]
        {
            // Sampled on entry: a block's own edits move facts between
            // locations, and only what arrives could grow without bound.
            self.me.test_stats.peak_facts = self.me.test_stats.peak_facts.max(state.facts.len());
        }

        // Edits atop a block belong to the one edge arriving at it, and so run
        // before that edge's arguments are renamed into this block's parameters.
        let mut renamed = false;

        let terminator =
            Inst::<E>::try_new(crate::liveness::block_last_inst(&input_block).index()).unwrap();
        let mut iter = block_iter(move_generation, func, wide);
        while let Some((item, index)) = iter.next_indexed() {
            let edit = match item {
                InstOrEdit::Inst(inst) => {
                    self.rename_arriving_edge(&mut state, block, &mut renamed);
                    if inst == terminator && mode == Mode::Rewrite && self.me.recorded.enabled {
                        self.record_before_terminator(&state, block);
                    }
                    self.apply_inst(&mut state, inst);
                    continue;
                }
                InstOrEdit::Edit(Edit::Move(mv)) => EdgeEdit::Move(mv),
                InstOrEdit::Edit(Edit::Remat(remat)) => EdgeEdit::Remat(remat),
                InstOrEdit::Edit(Edit::CriticalEdge(CriticalEdgeEdit { succ, .. })) => {
                    // These run on their own edge rather than here.
                    self.rename_arriving_edge(&mut state, block, &mut renamed);
                    let index = index.expect("`block_iter` numbers every edit it yields");
                    edge_edits.push((succ, index));
                    continue;
                }
            };
            let index = index.expect("`block_iter` numbers every edit it yields");
            let departing = matches!(
                move_generation.edits()[index].0.unpack(),
                MovePosition::Departure(_)
            );
            let place = if !renamed {
                Place::BlockTop
            } else if departing {
                Place::Departing
            } else {
                Place::InBlock
            };
            self.apply_edit(&mut state, edit, index, place, mode);
        }

        // Belt and braces: a block always has a terminator, so this already ran.
        self.rename_arriving_edge(&mut state, block, &mut renamed);

        state.debug_assert_locations_are_disjoint(machine);

        // Its own copy per edge, so an edge's edits are seen only on that edge
        // --- what splitting the critical edge would do for real.
        for (i, succ) in input_block.successors().enumerate() {
            out.reset_to(&state.facts);
            for &(on, index) in &edge_edits {
                if on == i {
                    let edit = edge_edit_at(move_generation, index);
                    self.apply_edit(&mut out, edit, index, Place::OnEdge, mode);
                }
            }
            let succ = Block::<E>::try_new(succ.index()).unwrap();
            if self.arriving_edge(succ).is_none() {
                self.rename_params(&mut out, block, i, succ);
            }

            // Only the analysis propagates; the rewrite must not disturb the
            // states it is deciding against.
            if mode == Mode::Analyze {
                self.meet_into(succ, &out);
            }
        }

        self.me.state = state;
        self.me.out = out;
        self.me.edge_edits = edge_edits;
    }

    /// Keep the state just before `block`'s terminator, when demanded-move
    /// hoisting may want to insert there.
    ///
    /// That is only ever a block whose every successor has it as its only
    /// predecessor; see `crate::demanded_moves`.
    fn record_before_terminator(&mut self, state: &State<E>, block: Block<E>) {
        if !crate::demanded_moves::may_hoist_into(self.input.func, block.with_repr32()) {
            return;
        }
        let recorded = &mut self.me.recorded;
        let start = recorded.before_terminator_facts.next_key_unwrap();
        for &fact in &state.facts {
            recorded.before_terminator_facts.push_unwrap(fact);
        }
        recorded.before_terminator[block] =
            Some(recorded.before_terminator_facts.range_from(start));
    }

    /// Rename what this block's one incoming edge left it, if it has one and if
    /// that has not happened yet.
    fn rename_arriving_edge(&mut self, state: &mut State<E>, block: Block<E>, renamed: &mut bool) {
        if *renamed {
            return;
        }
        *renamed = true;
        if let Some((pred, index)) = self.arriving_edge(block) {
            self.rename_params(state, pred, index, block);
        }
    }

    /// Rename the arguments `pred`'s `index`th edge passes into the parameters
    /// they define.
    fn rename_params(
        &mut self,
        state: &mut State<E>,
        pred: Block<E>,
        index: usize,
        succ: Block<E>,
    ) {
        let func = self.input.func;
        let input_pred = func.block(pred.with_repr32());
        let input_succ = func.block(succ.with_repr32());

        if input_succ.len_params() == 0 {
            return;
        }
        debug_assert_eq!(
            input_succ.len_params(),
            input_pred.len_successor_block_args(index),
            "checked by input validation",
        );

        let mut renamed = core::mem::take(&mut self.me.renamed);
        renamed.clear();

        for (param, arg) in input_succ
            .params()
            .zip(input_pred.successor_block_args(index))
        {
            let param = Val::<E>::try_new(param.index()).unwrap();
            let arg = Val::<E>::try_new(arg.index()).unwrap();
            for &(loc, part) in &state.facts {
                if part.val == arg {
                    renamed.push((
                        loc,
                        Part {
                            val: param,
                            index: part.index,
                        },
                    ));
                }
            }
        }

        // The parameters are killed only after every argument has been read,
        // because a block may pass one of its own parameters back to itself.
        for param in input_succ.params() {
            state.kill(Val::<E>::try_new(param.index()).unwrap());
        }

        // An argument the successor has no use for is forgotten here, the only
        // place the pass drops a fact it was not forced to. Renaming adds the
        // parameter's name beside the argument's and leaves the argument's
        // behind, so a chain of blocks passing a parameter along accrues one
        // useless fact per edge, forever, inside a fixpoint whose every
        // operation is at least linear in the fact count. Dropping costs only
        // precision, and a value dead on entry to `succ` has no read left to
        // serve. Before the renamed facts go in, not after, because an argument
        // may be one of `succ`'s own parameters and a kill kills every name.
        for arg in input_pred.successor_block_args(index) {
            let arg = Val::<E>::try_new(arg.index()).unwrap();
            if !succ.is_live_in(self.liveness, arg) {
                state.kill(arg);
            }
        }

        for &(loc, part) in &renamed {
            state.insert(loc, part);
        }

        self.me.renamed = renamed;
    }

    /// Run one edit, whether it sits inside a block or on an edge leaving it,
    /// against `state`, and decide whether it needs to happen at all.
    fn apply_edit(
        &mut self,
        state: &mut State<E>,
        edit: EdgeEdit<E>,
        index: usize,
        place: Place,
        mode: Mode,
    ) {
        let machine = self.input.machine;

        let (from, to) = match edit {
            EdgeEdit::Remat(Remat { val, dest }) => {
                // A remat computes its value from nothing, so the whole of it
                // lands in `dest` --- unless `dest` already holds exactly that.
                //
                // `index: 0` is the whole of the value, not its first register,
                // which is load-bearing: a group value would need one fact per
                // part. `MoveGeneration::should_remat` rejects any destination
                // that is not a single register, so none reaches here.
                let dest = ScalarAllocation::Reg(dest);
                let part = Part { val, index: 0 };
                if state.holds(dest, part) {
                    self.eliminate(index, place, mode);
                } else {
                    state.clobber(machine, dest);
                    state.insert(dest, part);
                    if mode == Mode::Rewrite && self.me.recorded.enabled {
                        self.me
                            .recorded
                            .record_written(index, core::iter::once(part));
                    }
                }
                return;
            }

            EdgeEdit::Move(mv) => match mv {
                Move::RegReg { from, to } => {
                    (ScalarAllocation::Reg(from), ScalarAllocation::Reg(to))
                }
                Move::Spill { from, to } => {
                    (ScalarAllocation::Reg(from), ScalarAllocation::Stack(to))
                }
                Move::Reload { from, to } => {
                    (ScalarAllocation::Stack(from), ScalarAllocation::Reg(to))
                }
            },
        };

        let mut scratch = core::mem::take(&mut self.me.scratch);

        if from == to {
            // The solver never emits one, but it is a no-op whatever the state
            // says.
            if mode == Mode::Rewrite {
                test_stat!(self.me, identity_moves);
            }
            self.eliminate(index, place, mode);
        } else if state.subsumes(to, from) {
            // Nothing clobbered and nothing recorded: the move is not going to
            // happen, so nothing about the machine changes.
            self.eliminate(index, place, mode);
        } else {
            if mode == Mode::Rewrite && !state.parts(from).is_empty() && !state.parts(to).is_empty()
            {
                test_stat!(self.me, near_miss);
            }
            state.copy_into(machine, to, from, &mut scratch);
            if mode == Mode::Rewrite && self.me.recorded.enabled {
                self.me
                    .recorded
                    .record_written(index, scratch.iter().copied());
            }
        }

        self.me.scratch = scratch;
    }

    /// Record that the edit at `index` is not going to happen.
    ///
    /// Only the rewrite records anything: the analysis calls this so the caller
    /// takes the eliminated transfer, but decides against unsettled states.
    fn eliminate(&mut self, index: usize, place: Place, mode: Mode) {
        if mode != Mode::Rewrite {
            return;
        }

        match place {
            Place::BlockTop => test_stat!(self.me, eliminated_at_block_top),
            Place::Departing => test_stat!(self.me, eliminated_before_terminator),
            Place::OnEdge => test_stat!(self.me, eliminated_on_critical_edge),
            Place::InBlock => {}
        }

        // Back to the edit list rather than taking the caller's copy, because
        // the event and the trace want the edit's position too, and only the
        // list has it.
        let (pos, _) = self.move_generation.edits()[index];
        let edit = edge_edit_at(self.move_generation, index);

        match edit {
            EdgeEdit::Move(Move::RegReg { .. }) => test_stat!(self.me, eliminated_reg_reg),
            EdgeEdit::Move(Move::Spill { .. }) => test_stat!(self.me, eliminated_spills),
            EdgeEdit::Move(Move::Reload { .. }) => test_stat!(self.me, eliminated_reloads),
            EdgeEdit::Remat(_) => test_stat!(self.me, eliminated_remats),
        }

        match edit {
            EdgeEdit::Move(_) => self.counts.moves_eliminated.inc(),
            EdgeEdit::Remat(_) => self.counts.remats_eliminated.inc(),
        }

        crate::trace!("dropping redundant edit {index} at {pos:?}: {edit:?}");
        event!(self.events, EditEliminated { pos, edit, index });

        self.me.eliminated.push(index);
    }

    /// Run one instruction's definitions and clobbers against `state`. Reads
    /// change nothing, and input validation makes an operand naming no value
    /// always a read.
    fn apply_inst(&mut self, state: &mut State<E>, inst: Inst<E>) {
        let func = self.input.func;
        let machine = self.input.machine;
        let spill_slots = self.spill_slots;
        let output = self.output;

        let wide = inst.with_repr32();
        let input_inst = func.inst(wide);
        let allocs = output.inst_allocs(wide);
        debug_assert_eq!(allocs.len(), input_inst.operands_len());

        let mut scalars = core::mem::take(&mut self.me.scalars);

        // A late definition overwrites an early one landing on it, not the
        // other way around, so the phases cannot be run in operand order.
        for early in [true, false] {
            for (i, op) in input_inst.operands().enumerate() {
                if op.kind() != DefUse::Def || op.pos().is_early() != early {
                    continue;
                }
                let val = Val::<E>::try_new(
                    op.val()
                        .expect("input validation rejects a definition that names no value")
                        .index(),
                )
                .unwrap();

                scalars_of(machine, spill_slots, allocs[i], &mut scalars);

                // The definition destroys whatever its locations held, and, by
                // SSA, any other claimant is from an earlier trip around a loop.
                for &loc in &scalars {
                    state.clobber(machine, loc);
                }
                state.kill(val);
                for (index, &loc) in scalars.iter().enumerate() {
                    state.insert(
                        loc,
                        Part {
                            val,
                            index: u8::try_from(index).unwrap(),
                        },
                    );
                }
            }
        }

        // A clobber destroys its register just as a definition does, only
        // without leaving a value behind to record.
        for reg in input_inst.clobbers().iter() {
            let reg = Reg::<E>::try_new(reg.index()).unwrap();
            state.clobber(machine, ScalarAllocation::Reg(reg));
        }

        self.me.scalars = scalars;
    }
}

/// What one run of the pass did, for test assertions.
#[cfg(test)]
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct TestStats {
    eliminated_reg_reg: usize,
    eliminated_spills: usize,
    eliminated_reloads: usize,
    eliminated_remats: usize,

    eliminated_on_critical_edge: usize,
    eliminated_at_block_top: usize,
    eliminated_before_terminator: usize,

    /// A move whose two ends both held something, but whose destination did not
    /// hold all of it.
    near_miss: usize,

    shrunk_entry_states: usize,
    block_revisits: usize,

    /// The most facts any one block was walked holding.
    peak_facts: usize,

    /// A move from a register to itself. Should always be zero.
    identity_moves: usize,
}

#[cfg(test)]
impl TestStats {
    const fn new() -> Self {
        Self {
            eliminated_reg_reg: 0,
            eliminated_spills: 0,
            eliminated_reloads: 0,
            eliminated_remats: 0,
            eliminated_on_critical_edge: 0,
            eliminated_at_block_top: 0,
            eliminated_before_terminator: 0,
            near_miss: 0,
            shrunk_entry_states: 0,
            block_revisits: 0,
            peak_facts: 0,
            identity_moves: 0,
        }
    }

    /// Did the pass run and find nothing at all to drop?
    fn eliminated_nothing(&self) -> bool {
        let Self {
            eliminated_reg_reg,
            eliminated_spills,
            eliminated_reloads,
            eliminated_remats,
            eliminated_on_critical_edge,
            eliminated_at_block_top,
            eliminated_before_terminator,
            near_miss: _,
            shrunk_entry_states: _,
            block_revisits: _,
            peak_facts: _,
            identity_moves: _,
        } = self;
        *eliminated_reg_reg == 0
            && *eliminated_spills == 0
            && *eliminated_reloads == 0
            && *eliminated_remats == 0
            && *eliminated_on_critical_edge == 0
            && *eliminated_at_block_top == 0
            && *eliminated_before_terminator == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        OperandConstraint, Output, Reg, RegClass,
        context::{Context, WhichContext},
        test::{TestInput, TestMachine},
    };
    use core::sync::atomic::{AtomicUsize, Ordering};
    use mutatis::{
        check::{Check, CheckResult},
        mutators as m,
    };
    use std::{format, string::String, vec::Vec};

    /// What one run of the allocator produced: the edits its results carry, in
    /// program order, and what the pass reached on the way.
    struct Run {
        edits: Vec<PlacedEdit>,
        stats: TestStats,
    }

    /// An edit, and where in the program it sits.
    ///
    /// Comparing levels by the edits alone would compare multisets of shapes,
    /// where deleting one of two identical edits and keeping the other is
    /// invisible. The point makes "only ever deletes" a claim about the list.
    /// Not refined further by counting edits within a point: that number shifts
    /// when a neighbour goes, so a legitimate deletion would read as a reorder.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct PlacedEdit {
        block: Block,
        insts_before: usize,
        edit: Edit,
    }

    /// Allocate `test_input` at `level`.
    ///
    /// Edits come back through the public results rather than `MoveGeneration`,
    /// which keeps one representation whatever `run_dispatch` picked and reads
    /// them as a client would. `Ok(None)` is the one failure a test may walk
    /// away from --- out of registers says something about the generated input,
    /// not this pass --- and everything else is an `Err`, the line
    /// `crate::test::check_allocation` also draws.
    fn run_at(test_input: &TestInput, level: MoveEliminationLevel) -> Result<Option<Run>, String> {
        let mut test_input = test_input.clone();
        test_input.options.redundant_move_elimination_level = level;

        // These tests measure *this* pass; at their default levels the others
        // would change edits of their own, and every assertion below would
        // read the sum of them.
        test_input.options.dead_move_elimination_level = MoveEliminationLevel::None;
        test_input.options.hoist_demanded_moves = false;

        let mut context = Context::new();
        let result = test_input.with_input(|input| -> Result<Option<Run>, String> {
            match crate::run_dispatch(&mut context, input) {
                Ok(()) => {}
                Err(crate::Error::TooManyLiveRegs) => return Ok(None),
                Err(e) => return Err(format!("allocation failed: {e:?}")),
            }

            let stats = match context.which.expect("`run_dispatch` chose a context") {
                #[cfg(feature = "entity-repr-8")]
                WhichContext::Context8 => context
                    .context8
                    .redundant_move_elimination
                    .test_stats
                    .clone(),
                #[cfg(feature = "entity-repr-16")]
                WhichContext::Context16 => context
                    .context16
                    .redundant_move_elimination
                    .test_stats
                    .clone(),
                WhichContext::Context32 => context
                    .context32
                    .redundant_move_elimination
                    .test_stats
                    .clone(),
            };

            let output = Output::new(&context);
            let mut edits = Vec::new();
            for (block, _) in input.func.blocks() {
                let mut insts_before = 0;
                for item in output.block_insts_and_edits(input.func, block) {
                    match item {
                        InstOrEdit::Inst(_) => insts_before += 1,
                        InstOrEdit::Edit(edit) => edits.push(PlacedEdit {
                            block,
                            insts_before,
                            edit,
                        }),
                    }
                }
            }
            Ok(Some(Run { edits, stats }))
        });

        context.reset();
        assert!(context.is_reset(), "the pass's storage should reset");
        result
    }

    /// `run_at` for a hand-built fixture, which is meant to allocate. Unlike the
    /// property tests, which take whatever the generator drew, a fixture that
    /// stopped allocating should say so rather than quietly pass.
    fn allocated(test_input: &TestInput, level: MoveEliminationLevel) -> Run {
        run_at(test_input, level)
            .expect("this fixture allocates")
            .expect("this fixture does not run out of registers")
    }

    /// Is `small` what is left of `large` after deleting some of its elements?
    ///
    /// Elimination only deletes, never reorders or rewrites, so a stronger
    /// level's edits sit inside a weaker one's in order.
    /// Which positions of `large` the greedy match of `small` into it skipped:
    /// the edits that were deleted. `None` if `small` is not a subsequence.
    fn deleted(small: &[PlacedEdit], large: &[PlacedEdit]) -> Option<Vec<usize>> {
        let mut skipped = Vec::new();
        let mut next = 0;
        for (i, edit) in large.iter().enumerate() {
            if small.get(next) == Some(edit) {
                next += 1;
            } else {
                skipped.push(i);
            }
        }
        (next == small.len()).then_some(skipped)
    }

    fn is_subsequence(small: &[PlacedEdit], large: &[PlacedEdit]) -> bool {
        let mut large = large.iter();
        small
            .iter()
            .all(|edit| large.any(|candidate| candidate == edit))
    }

    /// Nothing is eliminated at `None`, whatever the input: the durable form of
    /// "byte-identical to the behavior before this pass existed".
    #[test]
    fn none_changes_nothing() -> CheckResult<TestInput> {
        Check::new().iters(5_000).run_with(
            m::default::<TestInput>(),
            crate::test::corpus(),
            |test_input: &TestInput| -> Result<(), String> {
                let Some(none) = run_at(test_input, MoveEliminationLevel::None)? else {
                    return Ok(());
                };
                if none.stats != TestStats::default() {
                    return Err(format!("`None` reached the pass: {:?}", none.stats));
                }
                Ok(())
            },
        )
    }

    /// Every level only ever deletes from the list move generation produced.
    ///
    /// The stronger claim --- that `Global` deletes everything `Local` does ---
    /// is *not* asserted: the transfer is not monotone, so knowing more on entry
    /// to a block can cost an elimination inside it. No input has shown the two
    /// crossing, but nothing rules it out.
    #[test]
    fn the_levels_are_ordered() -> CheckResult<TestInput> {
        Check::new().iters(20_000).run_with(
            m::default::<TestInput>(),
            crate::test::corpus(),
            |test_input: &TestInput| -> Result<(), String> {
                let Some(none) = run_at(test_input, MoveEliminationLevel::None)? else {
                    return Ok(());
                };
                let level_ran = |level| -> Result<Run, String> {
                    run_at(test_input, level)
                        .map_err(|e| format!("{level:?} failed where `None` did not: {e}"))?
                        .ok_or_else(|| {
                            format!("{level:?} ran out of registers where `None` did not")
                        })
                };
                let local = level_ran(MoveEliminationLevel::Local)?;
                let global = level_ran(MoveEliminationLevel::Global)?;

                if !is_subsequence(&local.edits, &none.edits) {
                    return Err(format!(
                        "`Local` did not merely delete from `None`:\n\
                         none  = {:?}\nlocal = {:?}",
                        none.edits, local.edits,
                    ));
                }
                if !is_subsequence(&global.edits, &none.edits) {
                    return Err(format!(
                        "`Global` did not merely delete from `None`:\n\
                         none   = {:?}\nglobal = {:?}",
                        none.edits, global.edits,
                    ));
                }
                if global.edits.len() > none.edits.len() || local.edits.len() > none.edits.len() {
                    return Err(String::from("a level above `None` grew the edit list"));
                }

                // The containment the union transfer buys: `Local` starts
                // every block from the empty state, which sits below whatever
                // the fixpoint settles on, so a monotone transfer leaves
                // `Global` seeing at least as much everywhere.
                let expect = |edits| deleted(edits, &none.edits).expect("just checked");
                let by_global = expect(&global.edits);
                if let Some(i) = expect(&local.edits).iter().find(|i| !by_global.contains(i)) {
                    return Err(format!(
                        "`Local` eliminated edit {i}, which `Global` kept:\n\
                         none   = {:?}\nlocal  = {:?}\nglobal = {:?}",
                        none.edits, local.edits, global.edits,
                    ));
                }
                Ok(())
            },
        )
    }

    /// Allocating the same input twice with one context gives the same answer.
    ///
    /// Entry states live in an arena that a shrinking state rewrites in place,
    /// leaving a gap --- exactly what a `reset` forgets to clear.
    #[test]
    fn a_reused_context_gives_the_same_answer() -> CheckResult<TestInput> {
        Check::new().iters(2_000).run_with(
            m::default::<TestInput>(),
            crate::test::corpus(),
            |test_input: &TestInput| -> Result<(), String> {
                let mut context = Context::new();
                let mut allocate = || {
                    test_input.with_input(|input| {
                        let ok = crate::run_dispatch(&mut context, input).is_ok();
                        let edits = ok.then(|| {
                            let output = Output::new(&context);
                            input
                                .func
                                .blocks()
                                .flat_map(|(block, _)| {
                                    output
                                        .block_insts_and_edits(input.func, block)
                                        .filter_map(|item| match item {
                                            InstOrEdit::Edit(edit) => Some(edit),
                                            InstOrEdit::Inst(_) => None,
                                        })
                                        .collect::<Vec<_>>()
                                })
                                .collect::<Vec<_>>()
                        });
                        context.reset();
                        edits
                    })
                };

                let first = allocate();
                let second = allocate();
                if first != second {
                    return Err(format!(
                        "a reused context gave a different answer:\n\
                         first  = {first:?}\nsecond = {second:?}",
                    ));
                }
                Ok(())
            },
        )
    }

    /// Every shape the pass can reach is reached by some input.
    ///
    /// A pass that quietly stopped eliminating would still pass every test
    /// above, since they only say it did not eliminate too much. This one says
    /// it eliminated something, shape by shape.
    #[test]
    fn every_shape_is_reached() -> CheckResult<TestInput> {
        /// How many of the inputs tried may be ones the allocator gave up on
        /// before the pass ran at all. A ceiling rather than a floor, for the
        /// reason `checker::tests::checker_properties` gives.
        const SKIP_CEILING_PERCENT: usize = 60;

        /// The seed this check searches from.
        ///
        /// The only pinned test here, because it is the only one asserting a
        /// search *found* something --- a claim about one search. Unseeded, it
        /// would turn on which other tests drew from the generator first, and
        /// the rarer shapes are rare enough to fall off an unlucky one.
        const COVERAGE_SEED: u64 = 1;

        macro_rules! counters {
            ($($name:ident : $field:ident = $what:expr,)*) => {
                $(static $name: AtomicUsize = AtomicUsize::new(0);)*
                $($name.store(0, Ordering::Relaxed);)*

                static ITERS: AtomicUsize = AtomicUsize::new(0);
                static SKIPPED: AtomicUsize = AtomicUsize::new(0);
                ITERS.store(0, Ordering::Relaxed);
                SKIPPED.store(0, Ordering::Relaxed);

                let result = Check::new().iters(20_000).seed(COVERAGE_SEED).run_with(
                    m::default::<TestInput>(),
                    crate::test::corpus(),
                    |test_input: &TestInput| -> Result<(), String> {
                        ITERS.fetch_add(1, Ordering::Relaxed);
                        let Some(run) = run_at(test_input, MoveEliminationLevel::Global)? else {
                            SKIPPED.fetch_add(1, Ordering::Relaxed);
                            return Ok(());
                        };
                        $($name.fetch_add(run.stats.$field, Ordering::Relaxed);)*
                        if run.stats.identity_moves > 0 {
                            return Err(format!(
                                "the solver emitted {} move(s) from a location to itself",
                                run.stats.identity_moves,
                            ));
                        }
                        Ok(())
                    },
                );

                if result.is_ok() {
                    $(assert!(
                        $name.load(Ordering::Relaxed) > 0,
                        "no input produced {}, so this pass's tests are that much more vacuous",
                        $what,
                    );)*

                    let iters = ITERS.load(Ordering::Relaxed);
                    let skipped = SKIPPED.load(Ordering::Relaxed);
                    assert!(
                        skipped * 100 <= iters * SKIP_CEILING_PERCENT,
                        "the allocator ran out of registers on {skipped} of {iters} inputs, \
                         over the {SKIP_CEILING_PERCENT}% this check tolerates: almost \
                         nothing was actually eliminated",
                    );
                }

                result
            };
        }

        counters! {
            REG_REG: eliminated_reg_reg = "a redundant register-to-register move",
            SPILLS: eliminated_spills = "a redundant spill",
            RELOADS: eliminated_reloads = "a redundant reload",
            REMATS: eliminated_remats = "a redundant rematerialization",
            ON_EDGES: eliminated_on_critical_edge = "a redundant edit on a critical edge",
            AT_TOP: eliminated_at_block_top =
                "a redundant edit atop a block, which belongs to the edge arriving at it",
            DEPARTING: eliminated_before_terminator =
                "a redundant edit just before a block's terminator",
            NEAR_MISS: near_miss =
                "a move whose two ends both held something, but whose destination \
                 did not hold all of it",
            SHRUNK: shrunk_entry_states = "a block whose entry state the meet shrank",
            REVISITS: block_revisits = "a block the fixpoint visited",
        }
    }

    /// How many of `edits` are the kind `want` accepts. A critical-edge edit is
    /// unwrapped first: these tests ask what an edit does, not where it is.
    fn count(edits: &[PlacedEdit], want: fn(EdgeEdit) -> bool) -> usize {
        edits
            .iter()
            .filter(|&&PlacedEdit { edit, .. }| {
                want(match edit {
                    Edit::Move(mv) => EdgeEdit::Move(mv),
                    Edit::Remat(remat) => EdgeEdit::Remat(remat),
                    Edit::CriticalEdge(CriticalEdgeEdit { edit, .. }) => edit,
                })
            })
            .count()
    }

    fn is_spill(edit: EdgeEdit) -> bool {
        matches!(edit, EdgeEdit::Move(Move::Spill { .. }))
    }

    fn is_reload(edit: EdgeEdit) -> bool {
        matches!(edit, EdgeEdit::Move(Move::Reload { .. }))
    }

    /// A value spilled for a stack-constrained read, then read in a register
    /// again: the reload is redundant, since nothing wanted the register
    /// meanwhile. All in one block, so `Local` sees it. This is the redundancy
    /// `spill_placement` leaves behind on purpose.
    #[test]
    fn a_reload_into_the_register_a_value_never_left_goes() {
        let test_input = TestInput::with_values_in_two_banks_spilled_and_reloaded();
        let none = allocated(&test_input, MoveEliminationLevel::None);
        let local = allocated(&test_input, MoveEliminationLevel::Local);
        let global = allocated(&test_input, MoveEliminationLevel::Global);

        // One spill and one reload per value; the reloads are what should go.
        assert_eq!(count(&none.edits, is_spill), 2);
        assert_eq!(count(&none.edits, is_reload), 2);

        assert_eq!(count(&local.edits, is_reload), 0);
        assert_eq!(count(&local.edits, is_spill), 2);
        assert_eq!(local.stats.eliminated_reloads, 2);

        // Nothing here needs the fixpoint.
        assert_eq!(global.edits, local.edits);
    }

    /// Two reloads into the register a value never left, with a clobber of that
    /// register between them. Only the first is redundant: the clobber destroys
    /// what the second refills, so eliminating it would miscompile.
    #[test]
    fn a_clobber_keeps_the_reload_that_follows_it() {
        let test_input = TestInput::with_a_reload_clobbered_before_its_next_read();
        let none = allocated(&test_input, MoveEliminationLevel::None);
        let local = allocated(&test_input, MoveEliminationLevel::Local);
        let global = allocated(&test_input, MoveEliminationLevel::Global);

        assert_eq!(count(&none.edits, is_spill), 1);
        assert_eq!(count(&none.edits, is_reload), 2);

        assert_eq!(count(&local.edits, is_reload), 1);
        assert_eq!(local.stats.eliminated_reloads, 1);
        // The survivor is the one the clobber made necessary, so it is the
        // later of the two.
        assert_eq!(deleted(&local.edits, &none.edits).unwrap(), [1]);

        // Nothing here needs the fixpoint.
        assert_eq!(global.edits, local.edits);
    }

    /// The same shape for a register-group value: both members are reloaded and
    /// both reloads go. Each is matched against its own [`Part`] index, so this
    /// also says the parts line up with the group's registers.
    #[test]
    fn a_group_value_is_reloaded_member_by_member() {
        let group_class = RegClass::try_new(usize::from(TestMachine::GROUP_CLASS)).unwrap();
        let test_input = TestInput::with_group_use_constraints(&[
            OperandConstraint::Stack,
            OperandConstraint::Reg(group_class),
        ]);
        let none = allocated(&test_input, MoveEliminationLevel::None);
        let local = allocated(&test_input, MoveEliminationLevel::Local);

        assert_eq!(count(&none.edits, is_reload), 2);
        assert_eq!(count(&local.edits, is_reload), 0);
        assert_eq!(local.stats.eliminated_reloads, 2);
    }

    /// The test the two levels exist to be told apart by. A value spilled in the
    /// entry block and reloaded past a diamond: `Local` enters each arm knowing
    /// nothing and keeps both reloads, `Global` carries the entry block's answer
    /// down both arms and drops them.
    #[test]
    fn only_a_fixpoint_sees_past_a_diamond() {
        let test_input = TestInput::with_a_value_reloaded_past_a_diamond();
        let none = allocated(&test_input, MoveEliminationLevel::None);
        let local = allocated(&test_input, MoveEliminationLevel::Local);
        let global = allocated(&test_input, MoveEliminationLevel::Global);

        // One store, and one reload down each arm.
        assert_eq!(count(&none.edits, is_spill), 1);
        assert_eq!(count(&none.edits, is_reload), 2);

        assert_eq!(local.edits, none.edits, "`Local` cannot see past a block");
        assert!(local.stats.eliminated_nothing());

        assert_eq!(count(&global.edits, is_reload), 0);
        assert_eq!(count(&global.edits, is_spill), 1);
        assert_eq!(global.stats.eliminated_reloads, 2);

        // Atop an arm, where the edge out of the entry block puts them.
        assert_eq!(global.stats.eliminated_at_block_top, 2);
    }

    /// The same separation around a back edge, where the redundant reload lands
    /// just before its block's terminator. Worth pinning beside the diamond: a
    /// loop means visiting a block whose entry state came from a non-final
    /// answer, which is the case the meet exists to make safe.
    #[test]
    fn only_a_fixpoint_sees_around_a_loop() {
        let test_input = TestInput::with_a_value_spilled_inside_a_loop();
        let local = allocated(&test_input, MoveEliminationLevel::Local);
        let global = allocated(&test_input, MoveEliminationLevel::Global);

        assert_eq!(count(&local.edits, is_reload), 1);
        assert!(local.stats.eliminated_nothing());

        assert_eq!(count(&global.edits, is_reload), 0);
        assert_eq!(global.stats.eliminated_reloads, 1);
        assert_eq!(global.stats.eliminated_before_terminator, 1);
        assert!(global.stats.block_revisits > 0, "a loop is walked twice");
    }

    /// A store into the slot a value is already in goes --- the redundancy
    /// `src/spill_placement.rs` declines to remove and points here for.
    #[test]
    fn a_dominated_spill_goes() {
        let test_input = TestInput::with_a_spilled_self_looping_entry_param();
        let local = allocated(&test_input, MoveEliminationLevel::Local);
        let global = allocated(&test_input, MoveEliminationLevel::Global);

        assert_eq!(count(&local.edits, is_spill), 1);
        assert!(local.stats.eliminated_nothing());

        assert_eq!(count(&global.edits, is_spill), 0);
        assert_eq!(global.stats.eliminated_spills, 1);
    }

    /// A move out of a location the analysis knows nothing about is never
    /// redundant, however much it knows about the destination. The empty set is
    /// contained in everything, so the rule turns this case away before asking
    /// rather than by asking; backwards, it would drop a move that must happen.
    #[test]
    fn an_unknown_source_is_never_redundant() {
        let val = Val::try_new(0).unwrap();
        let (r0, r1) = (Reg::try_new(0).unwrap(), Reg::try_new(1).unwrap());
        let (r0, r1) = (ScalarAllocation::Reg(r0), ScalarAllocation::Reg(r1));

        let mut state = State::<u32>::default();
        state.insert(r0, Part { val, index: 0 });

        assert!(!state.subsumes(r0, r1), "the source holds nothing");
        assert!(
            !state.subsumes(r1, r0),
            "and a destination holding nothing subsumes nothing either",
        );
        assert!(
            !state.subsumes(r1, r1),
            "nor does an unknown location itself"
        );

        // The other half: a move that really happens out of an unknown source
        // leaves the destination unknown rather than unchanged.
        TestInput::default().with_input(|input| {
            let mut scratch = Vec::new();
            state.copy_into(input.machine, r0, r1, &mut scratch);
        });
        assert!(state.parts(r0).is_empty());
    }

    /// Two registers holding different parts of one group value hold different
    /// things, so a move between them is not redundant. The case that would
    /// break, silently, if [`Part`] were a bare [`Val`].
    #[test]
    fn two_parts_of_one_value_are_not_each_other() {
        let val = Val::try_new(0).unwrap();
        let (r0, r1) = (Reg::try_new(0).unwrap(), Reg::try_new(1).unwrap());
        let (r0, r1) = (ScalarAllocation::Reg(r0), ScalarAllocation::Reg(r1));

        let mut state = State::<u32>::default();
        state.insert(r0, Part { val, index: 0 });
        state.insert(r1, Part { val, index: 1 });

        assert!(!state.subsumes(r0, r1));
        assert!(!state.subsumes(r1, r0));
        assert!(!state.holds(r0, Part { val, index: 1 }));
        assert!(state.holds(r0, Part { val, index: 0 }));
    }

    /// The point of running the pass under `E`: everything it stores is facts,
    /// and a fact is a location and a part, both of which shrink with the
    /// representation. Four bytes under `u8` against sixteen under `u32` is the
    /// whole saving, and it is only there because a `NonZero` gives each half a
    /// niche for its discriminant to sit in.
    #[test]
    fn a_narrow_fact_is_narrow() {
        use core::mem::size_of;

        assert_eq!(size_of::<ScalarAllocation<u8>>(), 2);
        assert_eq!(size_of::<Part<u8>>(), 2);
        assert_eq!(size_of::<Fact<u8>>(), 4);

        assert_eq!(size_of::<Fact<u16>>(), 8);
        assert_eq!(size_of::<Fact<u32>>(), 16);
    }

    /// The arithmetic `Event::MoveEmitted`'s doc describes really does take a
    /// move's event to its edit in the list a client is handed.
    ///
    /// Both event kinds number the list move generation left, which nothing
    /// public hands out any more: a client has to subtract the eliminated
    /// indices below its own, and know that an eliminated index addresses no
    /// edit at all. The least this side can do is prove the sum comes out.
    #[cfg(feature = "visualizer")]
    #[test]
    fn a_move_event_still_finds_its_edit() -> CheckResult<TestInput> {
        use crate::{entity::EntityRepr, events::Event as LoggedEvent};

        /// How many runs had something to eliminate, so that a pass that
        /// stopped eliminating could not make this one vacuous.
        static ELIMINATED: AtomicUsize = AtomicUsize::new(0);
        ELIMINATED.store(0, Ordering::Relaxed);

        fn check<E>(ctx: &ContextInner<E>) -> Result<(), String>
        where
            E: EntityRepr,
        {
            let edits = ctx.move_generation.edits();

            // The indices that are gone, in the numbering both events use.
            let mut removed = Vec::new();
            for (_, event) in ctx.events.iter() {
                if let LoggedEvent::EditEliminated { index, .. } = *event {
                    removed.push(index);
                }
            }
            removed.sort_unstable();
            ELIMINATED.fetch_add(removed.len(), Ordering::Relaxed);

            for (_, event) in ctx.events.iter() {
                let LoggedEvent::MoveEmitted { pos, move_, index } = *event else {
                    continue;
                };
                let below = removed.partition_point(|&r| r < index);
                if removed.get(below) == Some(&index) {
                    // Eliminated, so there is no edit for it to address.
                    continue;
                }

                let folded = index - below;
                let (edit_pos, edit) = *edits.get(folded).ok_or_else(|| {
                    format!(
                        "{move_:?} was emitted as edit {index}, which folds to {folded}, \
                         past the end of a list of {} edits",
                        edits.len(),
                    )
                })?;
                let emitted = match edit {
                    Edit::Move(mv) => mv,
                    Edit::CriticalEdge(CriticalEdgeEdit {
                        edit: EdgeEdit::Move(mv),
                        ..
                    }) => mv,
                    _ => return Err(format!("edit {index} folds to {edit:?}, not a move")),
                };
                if (edit_pos, emitted) != (pos, move_) {
                    return Err(format!(
                        "{move_:?} at {pos:?} was emitted as edit {index}, which folds to \
                         {folded}: {emitted:?} at {edit_pos:?}",
                    ));
                }
            }
            Ok(())
        }

        let result = Check::new().iters(5_000).run_with(
            m::default::<TestInput>(),
            crate::test::corpus(),
            |test_input: &TestInput| -> Result<(), String> {
                // `removed` reads `EditEliminated` alone, so this has to be the
                // only pass changing the edits.
                let mut test_input = test_input.clone();
                test_input.options.dead_move_elimination_level = MoveEliminationLevel::None;
                test_input.options.hoist_demanded_moves = false;

                let mut context = Context::new();
                let result = test_input.with_input(|input| -> Result<(), String> {
                    match crate::run_dispatch(&mut context, input) {
                        Ok(()) => {}
                        Err(crate::Error::TooManyLiveRegs) => return Ok(()),
                        Err(e) => return Err(format!("allocation failed: {e:?}")),
                    }
                    match context.which.expect("`run_dispatch` chose a context") {
                        #[cfg(feature = "entity-repr-8")]
                        WhichContext::Context8 => check(&context.context8),
                        #[cfg(feature = "entity-repr-16")]
                        WhichContext::Context16 => check(&context.context16),
                        WhichContext::Context32 => check(&context.context32),
                    }
                });
                context.reset();
                result
            },
        );

        if result.is_ok() {
            assert!(
                ELIMINATED.load(Ordering::Relaxed) > 0,
                "nothing was eliminated anywhere, so the fold was never exercised",
            );
        }
        result
    }

    /// A chain of blocks passing a parameter along does not accumulate a fact
    /// per link.
    ///
    /// Renaming is the one transfer that adds a name without retiring one: `r0`
    /// holds the argument, and now the parameter it became. Both are true, and
    /// if nothing drops the first the state grows on every edge. The *answer* is
    /// the same either way, so no other test here can see it.
    #[test]
    fn a_parameter_chain_does_not_grow_the_state() {
        // Differing by 32 links and nothing else.
        let short = allocated(
            &TestInput::with_a_parameter_chain(2),
            MoveEliminationLevel::Global,
        );
        let long = allocated(
            &TestInput::with_a_parameter_chain(34),
            MoveEliminationLevel::Global,
        );

        assert!(
            short.stats.peak_facts > 0,
            "the chain should put the value somewhere",
        );
        assert_eq!(
            short.stats.peak_facts, long.stats.peak_facts,
            "the state grew with the length of the chain: a link's argument is \
             dead the moment the edge below it is taken, and is not being \
             forgotten",
        );
    }

    /// Sharing a part proves two locations hold the same bits, and is still not
    /// enough to drop the move between them.
    ///
    /// The shape a fuzz soak found, cut down to the state it turns on. `r0` and
    /// `r1` both hold `b`, so the move is a physical no-op --- but the move is
    /// also the only thing a reader of the surviving edits would see making `r0`
    /// hold `c`, so dropping it breaks a later read of `c` from `r0`.
    #[test]
    fn sharing_a_part_is_not_enough() {
        let a = Val::try_new(0).unwrap();
        let b = Val::try_new(1).unwrap();
        let c = Val::try_new(2).unwrap();
        let (r0, r1) = (Reg::try_new(0).unwrap(), Reg::try_new(1).unwrap());
        let (r0, r1) = (ScalarAllocation::Reg(r0), ScalarAllocation::Reg(r1));
        let part = |val| Part { val, index: 0 };

        let mut state = State::<u32>::default();
        for p in [part(a), part(b)] {
            state.insert(r0, p);
        }
        for p in [part(b), part(c)] {
            state.insert(r1, p);
        }

        assert!(!state.subsumes(r0, r1), "`r0` is not already holding `c`");
        assert!(!state.subsumes(r1, r0), "nor `r1` already `a`");

        // Containment does go, and a strictly larger destination is fine.
        state.set(r1, &[part(a)]);
        assert!(state.subsumes(r0, r1), "`r0` holds all of `{{a}}` and more");
        assert!(!state.subsumes(r1, r0), "but not the other way around");
    }
}
