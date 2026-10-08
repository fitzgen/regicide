//! Dead move elimination.
//!
//! A move is *dead* when nothing ever reads its destination again. Move
//! generation emits these for the same reason it can emit redundant ones: it
//! places edits based on local information.
//!
//! Redundant-move elimination elides any move that puts a value into a location
//! where it already resides; this pass asks whether anything reads a value from
//! the move's destination again, backwards over locations, in what is basically
//! another variation of a liveness analysis:
//!
//! ```text
//! live_out(block) = union(live_in(s) for s in successors(block))
//!                   -- plus each edge's critical-edge edits, applied per edge
//!
//! live_in(block) = live_out(block) - defs(block) + uses(block)
//!                  + block_param_allocs(block)
//! ```
//!
//! The meet is union, so the conservative assumption is that everything is
//! live.
//!
//! Only block live-out sets are cached. One reused set walks a block backwards
//! and, at its top, is unioned into each predecessor's live-out, enqueueing
//! those that grew. A final backwards pass then drops the edits writing to a
//! location that nothing ever reads.

use crate::{
    Entity as _, Input,
    context::ContextInner,
    counts::Counts,
    entity::{Block, EntityRepr, EntitySet, Inst, Val},
    error::IResult,
    events::EventsLog,
    hash_set::FxHashSet,
    input::{DefUse, InputBlock, InputFunction, InputInst, MoveEliminationLevel, Position},
    machine::{Reg, RegUnit, RegUnitSet},
    move_generation::MoveGeneration,
    output::{
        CriticalEdgeEdit, EdgeEdit, Edit, InstOrEdit, Move, OutputInner, ScalarAllocation,
        block_iter,
    },
    redundant_move_elimination::scalars_of,
    rpo::Rpo,
    spill_slot_allocation::{SpillSlot, SpillSlots},
    timing::Timing,
};
use alloc::{collections::BinaryHeap, vec::Vec};

macro_rules! test_stat {
    ( $me:expr, $field:ident ) => {{
        #[cfg(test)]
        {
            $me.test_stats.$field += 1;
        }
    }};
}

/// Run the dead-move elimination pass.
pub(crate) fn eliminate_dead_moves<E>(
    context: &mut ContextInner<E>,
    input: &Input<'_, impl InputFunction>,
) -> IResult<()>
where
    E: EntityRepr,
{
    let level = input.options.dead_move_elimination_level;
    if level == MoveEliminationLevel::None {
        return Ok(());
    }

    let _timing = Timing::new("eliminate dead moves");

    let already_eliminated = &mut context.dead_move_elimination.already_eliminated;
    already_eliminated.clear();
    already_eliminated.reserve(context.redundant_move_elimination.eliminated.len());
    already_eliminated.extend(
        context
            .redundant_move_elimination
            .eliminated
            .iter()
            .copied()
            .map(|index| u32::try_from(index).unwrap()),
    );

    {
        let mut eliminator = Eliminator {
            input,
            output: &context.output,
            move_generation: &context.move_generation,
            spill_slots: &context.spill_slots,
            rpo: &context.rpo,
            counts: &mut context.counts,
            events: &mut context.events,
            me: &mut context.dead_move_elimination,
        };
        eliminator.run(level);
    }

    context.dead_move_elimination.eliminated.sort_unstable();
    debug_assert!(
        context
            .dead_move_elimination
            .eliminated
            .windows(2)
            .all(|w| w[0] != w[1]),
        "must have no duplicates",
    );

    // The edits are removed by `crate::remove_eliminated_edits`, once both
    // move-elimination passes have run.
    Ok(())
}

/// The locations that may be read from some program point onwards.
///
/// The polarity depends on `DeadMoveElimination::saturated`:
///
/// * Not saturated: a location is in this set when it is live. A cached block
///   live-out is always read this way.
///
/// * Saturated: everything is live *except* the locations in this set, which
///   have been killed since the block's bottom. This is the top of the lattice,
///   "everything may be read", without a bitset holding every register unit and
///   spill slot.
///
/// `MoveEliminationLevel::Local` seeds each block saturated. It is fixed when a
/// block is seeded, and only `Eliminator::is_live_unit`, `is_live_slot`,
/// `mark_live` and `mark_dead` read it, so the transfer function above them is
/// written once. A saturated set is never propagated, and so never has to be
/// turned into bits for a meet.
struct LiveSet<E>
where
    E: EntityRepr,
{
    units: RegUnitSet,
    slots: EntitySet<SpillSlot<E>>,
}

impl<E> Default for LiveSet<E>
where
    E: EntityRepr,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<E> LiveSet<E>
where
    E: EntityRepr,
{
    const fn new() -> Self {
        Self {
            units: RegUnitSet::new(),
            slots: EntitySet::new(),
        }
    }

    fn clear(&mut self) {
        self.units.reset();
        self.slots.reset();
    }

    fn is_empty(&self) -> bool {
        self.units.is_empty() && self.slots.is_empty()
    }

    fn copy_from(&mut self, other: &Self) {
        self.units.copy_from(&other.units);
        self.slots.copy_from(&other.slots);
    }

    /// Add everything in `rhs`, returning whether that added anything new.
    fn union_with(&mut self, rhs: &Self) -> bool {
        // Both unions must run, so not `||`.
        let units = self.units.union_with(&rhs.units);
        let slots = self.slots.union_with(&rhs.slots);
        units || slots
    }
}

/// Where a block's backwards walk starts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Seed {
    /// Every location may be read: the top of the lattice, and all a `Local`
    /// walk can assume. See `LiveSet`.
    All,

    /// This block's cached live-out, as the fixpoint left it.
    LiveOut,
}

/// Which of the pass's two walks over the control-flow graph is running.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    /// Computing the fixpoint over block live-out sets.
    Analyze,

    /// Deciding which edits to drop, against the settled sets.
    Rewrite,
}

/// Reusable storage for the pass.
pub(crate) struct DeadMoveElimination<E>
where
    E: EntityRepr,
{
    /// Each reachable block's cached live-out set, indexed by its
    /// `Rpo::index_of` rather than by block.
    ///
    /// Not a `SecondaryMap`: its `IndexMut` requires `V: Clone` and clones the
    /// default to grow, and it would carry unreachable blocks too.
    live_out: Vec<LiveSet<E>>,

    /// The live set at the program point the walk has reached.
    live: LiveSet<E>,

    /// Whether `live` is saturated; see `LiveSet`.
    saturated: bool,

    /// One incoming edge's worth of `live`, so that an edge's edits are seen
    /// only on that edge.
    edge: LiveSet<E>,

    /// Blocks to visit again, by reverse-post-order index: a max-heap pops in
    /// post-order, which is what a backwards analysis converges fastest in.
    worklist: BinaryHeap<u32>,

    /// Which blocks are already on `worklist`, so that one is never queued
    /// twice.
    on_worklist: EntitySet<Block<E>>,

    /// The block's instructions and edits, collected forwards so that the walk
    /// can take them in reverse.
    items: Vec<(InstOrEdit<E>, Option<usize>)>,

    /// This block's incoming edges, as `(predecessor, outgoing edge index)`.
    preds: Vec<(Block<E>, usize)>,

    /// Scratch space for the single locations one allocation is made of.
    scalars: Vec<ScalarAllocation<E>>,

    /// The indices redundant-move elimination took, which this pass treats as
    /// not happening. They are still in the edit list.
    already_eliminated: FxHashSet<u32>,

    /// The edits to remove, sorted, by index into the edit list as move
    /// generation left it. See `crate::remove_eliminated_edits`.
    pub(crate) eliminated: Vec<usize>,

    /// Scratch space for `crate::remove_eliminated_edits`'s merge of the two
    /// passes' lists. It lives here so the context owns the allocation.
    pub(crate) to_remove: Vec<usize>,

    #[cfg(test)]
    test_stats: TestStats,
}

impl<E> DeadMoveElimination<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        Self {
            live_out: Vec::new(),
            live: LiveSet::new(),
            saturated: false,
            edge: LiveSet::new(),
            worklist: BinaryHeap::new(),
            on_worklist: EntitySet::new(),
            items: Vec::new(),
            preds: Vec::new(),
            scalars: Vec::new(),
            already_eliminated: FxHashSet::with_hasher(rustc_hash::FxBuildHasher),
            eliminated: Vec::new(),
            to_remove: Vec::new(),
            #[cfg(test)]
            test_stats: TestStats::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            live_out,
            live,
            saturated,
            edge,
            worklist,
            on_worklist,
            items,
            preds,
            scalars,
            already_eliminated,
            eliminated,
            to_remove,
            #[cfg(test)]
            test_stats,
        } = self;
        live_out.clear();
        live.clear();
        *saturated = false;
        edge.clear();
        worklist.clear();
        on_worklist.reset();
        items.clear();
        preds.clear();
        scalars.clear();
        already_eliminated.clear();
        eliminated.clear();
        to_remove.clear();
        #[cfg(test)]
        {
            *test_stats = TestStats::default();
        }
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            live_out,
            live,
            saturated,
            edge,
            worklist,
            on_worklist,
            items,
            preds,
            scalars,
            already_eliminated,
            eliminated,
            to_remove,
            #[cfg(test)]
                test_stats: _,
        } = self;
        live_out.is_empty()
            && live.is_empty()
            && !*saturated
            && edge.is_empty()
            && worklist.is_empty()
            && on_worklist.is_reset()
            && items.is_empty()
            && preds.is_empty()
            && scalars.is_empty()
            && already_eliminated.is_empty()
            && eliminated.is_empty()
            && to_remove.is_empty()
    }
}

impl<E> DeadMoveElimination<E>
where
    E: EntityRepr,
{
    /// Is any unit of `reg` possibly read after `block`'s bottom, per the
    /// fixpoint?
    ///
    /// Only meaningful after a `Global` run that tracked registers. `None` for a
    /// block the pass never numbered: an unreachable one, or any after a run
    /// that kept no live-out sets.
    pub(crate) fn reg_may_be_live_out(
        &self,
        machine: &crate::machine::Machine,
        rpo: &Rpo<E>,
        block: Block<E>,
        reg: Reg<E>,
    ) -> Option<bool> {
        let live_out = self.live_out_of(rpo, block)?;
        Some(
            reg.iter_units(machine)
                .any(|unit| live_out.units.contains(unit)),
        )
    }

    /// Is `slot` possibly read after `block`'s bottom, per the fixpoint?
    ///
    /// Only meaningful after a `Global` run. `None` for a block the pass never
    /// numbered; see `reg_may_be_live_out`.
    pub(crate) fn slot_may_be_live_out(
        &self,
        rpo: &Rpo<E>,
        block: Block<E>,
        slot: SpillSlot<E>,
    ) -> Option<bool> {
        let live_out = self.live_out_of(rpo, block)?;
        Some(live_out.slots.contains(slot))
    }

    /// `block`'s cached live-out set, if the pass numbered it.
    fn live_out_of(&self, rpo: &Rpo<E>, block: Block<E>) -> Option<&LiveSet<E>> {
        if !rpo.is_reachable(block) {
            return None;
        }
        self.live_out.get(rpo.index_of(block) as usize)
    }
}

impl<E> Default for DeadMoveElimination<E>
where
    E: EntityRepr,
{
    fn default() -> Self {
        Self::new()
    }
}

/// The analysis itself, and everything it reads.
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

    counts: &'a mut Counts,
    events: &'a mut EventsLog<E>,
    me: &'a mut DeadMoveElimination<E>,
}

impl<E, F> Eliminator<'_, E, F>
where
    E: EntityRepr,
    F: InputFunction,
{
    /// Find everything to eliminate at `level`, leaving it in
    /// `DeadMoveElimination::eliminated`.
    fn run(&mut self, level: MoveEliminationLevel) {
        debug_assert_ne!(level, MoveEliminationLevel::None);

        self.index_blocks();

        if level == MoveEliminationLevel::Global {
            self.analyze();
        }
        self.rewrite(level);
    }

    /// Give each reachable block an empty cached live-out, at its
    /// `Rpo::index_of`.
    ///
    /// Empty is the bottom of the lattice, which is sound even for a block with
    /// no successors: a returned value is a `Use` on the terminator, spill slots
    /// are frame-local, and an emergency slot is written and read back within
    /// one parallel-move sequence.
    fn index_blocks(&mut self) {
        let len = self.rpo.iter().len();
        self.me.live_out.resize_with(len, LiveSet::new);
    }

    /// Run the fixpoint over block live-out sets.
    fn analyze(&mut self) {
        for block in self.rpo.iter() {
            self.enqueue(block);
        }

        while let Some(i) = self.me.worklist.pop() {
            let block = self.rpo.at(i);
            self.me.on_worklist.remove(block);
            self.counts.dead_move_elimination_iterations.inc();
            test_stat!(self.me, block_visits);
            self.visit_block(block, Seed::LiveOut, Mode::Analyze);
        }
    }

    /// Walk every reachable block once more, now deciding what to drop.
    ///
    /// This does not propagate, so the order is free; post-order matches the
    /// analysis. A block decides the edits on the edges *into* it, so each is
    /// decided exactly once. An edit out of an unreachable predecessor is never
    /// decided, and so never eliminated.
    fn rewrite(&mut self, level: MoveEliminationLevel) {
        let seed = match level {
            MoveEliminationLevel::Global => Seed::LiveOut,
            // A local walk has no live-out sets to start from.
            MoveEliminationLevel::Local => Seed::All,
            MoveEliminationLevel::None => unreachable!("the pass returned early"),
        };

        for block in self.rpo.iter().rev() {
            self.visit_block(block, seed, Mode::Rewrite);
        }
    }

    /// Queue `block` for another analysis visit, if it is not queued already.
    fn enqueue(&mut self, block: Block<E>) {
        if self.me.on_worklist.insert(block) {
            self.me.worklist.push(self.rpo.index_of(block));
        }
    }

    /// Is `unit` live at the point the walk has reached?
    fn is_live_unit(&self, unit: RegUnit) -> bool {
        // Saturated holds what has been *killed*, so membership reads inverted.
        self.me.live.units.contains(unit) != self.me.saturated
    }

    fn is_live_slot(&self, slot: SpillSlot<E>) -> bool {
        self.me.live.slots.contains(slot) != self.me.saturated
    }

    /// The transfer function's GEN: everything `loc` covers is read from here
    /// on. Spelled out because `gen` is a reserved word.
    fn mark_live(&mut self, loc: ScalarAllocation<E>) {
        let machine = self.input.machine;
        match loc {
            ScalarAllocation::Reg(reg) => {
                if !self.tracking_regs() {
                    return;
                }
                for unit in reg.iter_units(machine) {
                    if self.me.saturated {
                        self.me.live.units.remove(unit);
                    } else {
                        self.me.live.units.insert(unit);
                    }
                }
            }
            ScalarAllocation::Stack(slot) => {
                if self.me.saturated {
                    self.me.live.slots.remove(slot);
                } else {
                    self.me.live.slots.insert(slot);
                }
            }
        }
    }

    /// The transfer function's KILL: everything `loc` covers is overwritten
    /// here.
    fn mark_dead(&mut self, loc: ScalarAllocation<E>) {
        let machine = self.input.machine;
        match loc {
            ScalarAllocation::Reg(reg) => {
                if !self.tracking_regs() {
                    return;
                }
                for unit in reg.iter_units(machine) {
                    if self.me.saturated {
                        self.me.live.units.insert(unit);
                    } else {
                        self.me.live.units.remove(unit);
                    }
                }
            }
            ScalarAllocation::Stack(slot) => {
                if self.me.saturated {
                    self.me.live.slots.insert(slot);
                } else {
                    self.me.live.slots.remove(slot);
                }
            }
        }
    }

    /// Does this run track register units at all, or only spill slots?
    fn tracking_regs(&self) -> bool {
        self.input.options.eliminate_dead_register_moves
    }

    /// Walk `block` backwards, and hand its live-in set to each predecessor.
    ///
    /// `output::block_iter`'s interleaving rule is subtle enough that
    /// duplicating it backwards invites drift, so the items are collected
    /// forwards and iterated in reverse.
    fn visit_block(&mut self, block: Block<E>, seed: Seed, mode: Mode) {
        let func = self.input.func;
        let move_generation = self.move_generation;
        let wide = block.with_repr32();

        // Seed the walk from the block's bottom.
        match seed {
            Seed::All => {
                self.me.live.clear();
                self.me.saturated = true;
                test_stat!(self.me, saturated_blocks);
            }
            Seed::LiveOut => {
                let i = self.rpo.index_of(block);
                self.me.live.copy_from(&self.me.live_out[i as usize]);
                self.me.saturated = false;
            }
        }

        let mut items = core::mem::take(&mut self.me.items);
        items.clear();
        let mut iter = block_iter(move_generation, func, wide);
        while let Some(item) = iter.next_indexed() {
            items.push(item);
        }

        // The edits above the block's first instruction run *before* its
        // parameters have arrived: `Checker::visit_block` drains this leading
        // run and only then checks each parameter's location. So backwards, the
        // parameters are GEN'd between the run and the rest of the block.
        let arriving = items
            .iter()
            .take_while(|(item, _)| matches!(item, InstOrEdit::Edit(_)))
            .count();

        let apply = |this: &mut Self, items: &[(InstOrEdit<E>, Option<usize>)]| {
            for &(item, index) in items.iter().rev() {
                match item {
                    InstOrEdit::Inst(inst) => this.apply_inst(inst),
                    InstOrEdit::Edit(Edit::CriticalEdge(_)) => {
                        // Decided from the successor's side. Against a live-out
                        // unioned over every successor, one edge's kill could
                        // erase a read only another edge performs.
                    }
                    InstOrEdit::Edit(edit) => {
                        let index = index.expect("`block_iter` numbers every edit it yields");
                        let edit = match edit {
                            Edit::Move(mv) => EdgeEdit::Move(mv),
                            Edit::Remat(remat) => EdgeEdit::Remat(remat),
                            Edit::CriticalEdge(_) => unreachable!("handled above"),
                        };
                        this.apply_edit(edit, index, mode);
                    }
                }
            }
        };

        apply(self, &items[arriving..]);
        self.gen_block_params(block);
        apply(self, &items[..arriving]);

        // And again above that run. A block whose terminator is its only
        // instruction both receives its parameters and departs from that one
        // gap, and the checker then pins the arrival against the state the block
        // was *entered* in (`Checker::departs_from_its_first_gap`). So the
        // arrival must be live on both sides, or the edit delivering it looks
        // dead.
        self.gen_block_params(block);

        self.me.items = items;

        #[cfg(test)]
        {
            self.me.test_stats.peak_live = self
                .me
                .test_stats
                .peak_live
                .max(self.me.live.units.len() + self.me.live.slots.len());
        }

        // `live` is now this block's live-in set.
        self.visit_incoming_edges(block, mode);
    }

    /// Mark where `block`'s parameters arrive as read.
    ///
    /// Nothing else keeps those locations live, and `Output::block_param_allocs`
    /// is a public contract the checker enforces with
    /// `CheckerError::MisplacedBlockParam`. A parameter copied elsewhere before
    /// its only use, with nothing else reading the arrival, would otherwise see
    /// that location called dead and the edit delivering it dropped.
    ///
    /// The checker pins this only in one mode and only for a `Some` arrival, but
    /// the output is documented for clients regardless, so keep them all live.
    fn gen_block_params(&mut self, block: Block<E>) {
        let machine = self.input.machine;
        let spill_slots = self.spill_slots;
        let wide = block.with_repr32();

        let mut scalars = core::mem::take(&mut self.me.scalars);
        for i in 0..self.output.block_param_allocs(wide).len() {
            let Some(alloc) = self.output.block_param_allocs(wide)[i] else {
                continue;
            };
            scalars_of(machine, spill_slots, alloc, &mut scalars);
            for &loc in &scalars {
                self.mark_live(loc);
            }
        }
        self.me.scalars = scalars;
    }

    /// Apply each incoming edge's critical-edge edits to a copy of `live`, and,
    /// when analyzing, union the result into that predecessor's live-out set.
    ///
    /// Each critical edge belongs to one `(predecessor, outgoing edge index)`
    /// pair, since a block may branch to one target twice, so each edge edit is
    /// decided exactly once.
    fn visit_incoming_edges(&mut self, block: Block<E>, mode: Mode) {
        let func = self.input.func;
        let wide = block.with_repr32();

        let mut preds = core::mem::take(&mut self.me.preds);
        preds.clear();
        for pred in func.block(wide).predecessors() {
            let narrow = Block::<E>::try_new(pred.index()).unwrap();
            if !self.rpo.is_reachable(narrow) {
                continue;
            }
            for (i, succ) in func.block(pred).successors().enumerate() {
                if succ == wide {
                    preds.push((narrow, i));
                }
            }
        }
        // `predecessors` has one entry per edge, and the successor scan finds
        // every edge from each, so dedupe the repeats.
        preds.sort_unstable();
        preds.dedup();

        for &(pred, succ) in &preds {
            self.me.edge.copy_from(&self.me.live);
            core::mem::swap(&mut self.me.edge, &mut self.me.live);

            // One contiguous run, ordered by outgoing edge index, because
            // `PackedMovePosition` packs the two into a single key.
            let range = self.move_generation.block_edge_edit_range(pred);
            for index in range.rev() {
                let (_, edit) = self.move_generation.edits()[index];
                let Edit::CriticalEdge(CriticalEdgeEdit { succ: on, edit, .. }) = edit else {
                    unreachable!("`block_edge_edit_range` yields only critical-edge edits");
                };
                if on == succ {
                    self.apply_edit(edit, index, mode);
                }
            }

            // The rewrite must not disturb the sets it decides against.
            if mode == Mode::Analyze {
                debug_assert!(
                    !self.me.saturated,
                    "a saturated set is never propagated, so it never has to be \
                     turned into bits for a meet",
                );
                let i = self.rpo.index_of(pred);
                let mut live_out = core::mem::take(&mut self.me.live_out[i as usize]);
                let grew = live_out.union_with(&self.me.live);
                self.me.live_out[i as usize] = live_out;
                if grew {
                    self.enqueue(pred);
                }
            }

            // The next edge starts from the same live-in set.
            core::mem::swap(&mut self.me.edge, &mut self.me.live);
        }

        self.me.preds = preds;
    }

    /// Run one instruction backwards: definitions kill, reads revive.
    fn apply_inst(&mut self, inst: Inst<E>) {
        let func = self.input.func;
        let machine = self.input.machine;
        let spill_slots = self.spill_slots;
        let output = self.output;

        let wide = inst.with_repr32();
        let input_inst = func.inst(wide);
        let allocs = output.inst_allocs(wide);
        debug_assert_eq!(allocs.len(), input_inst.operands_len());

        let mut scalars = core::mem::take(&mut self.me.scalars);

        // Late then early is backwards program order within the instruction.
        for pos in [Position::Late, Position::Early] {
            // Kill before gen within a position: a `Reuse` constraint puts a
            // late def and an early use in the same register, and gen-first
            // would let the def erase the use's read.
            for kind in [DefUse::Def, DefUse::Use] {
                for (i, op) in input_inst.operands().enumerate() {
                    if op.pos() != pos || op.kind() != kind {
                        continue;
                    }

                    // A def naming no value is rejected by validation, and a
                    // read naming none has no allocation to read.
                    if op.val().is_none() {
                        continue;
                    }
                    debug_assert!(
                        Val::<E>::try_new(op.val().unwrap().index()).is_some(),
                        "every value of the function fits in `E`",
                    );

                    scalars_of(machine, spill_slots, allocs[i], &mut scalars);
                    for &loc in &scalars {
                        match kind {
                            DefUse::Def => self.mark_dead(loc),
                            DefUse::Use => self.mark_live(loc),
                        }
                    }
                }
            }
        }

        self.me.scalars = scalars;
    }

    /// Run one edit backwards, dropping it when nothing reads its destination.
    fn apply_edit(&mut self, edit: EdgeEdit<E>, index: usize, mode: Mode) {
        if self
            .me
            .already_eliminated
            .contains(&u32::try_from(index).unwrap())
        {
            return;
        }

        if self.dest_is_dead(edit) {
            // A dead edit does not happen, so it must not keep its source
            // alive. Leaving the live set untouched is what lets a chain of dead
            // spills collapse in one pass, and it is still monotone.
            if mode == Mode::Rewrite {
                self.eliminate(edit, index);
            }
            return;
        }

        // Kill before gen: the two may share units.
        match edit {
            EdgeEdit::Move(Move::RegReg { from, to }) => {
                self.mark_dead(ScalarAllocation::Reg(to));
                self.mark_live(ScalarAllocation::Reg(from));
            }
            EdgeEdit::Move(Move::Spill { from, to }) => {
                self.mark_dead(ScalarAllocation::Stack(to));
                self.mark_live(ScalarAllocation::Reg(from));
            }
            EdgeEdit::Move(Move::Reload { from, to }) => {
                self.mark_dead(ScalarAllocation::Reg(to));
                self.mark_live(ScalarAllocation::Stack(from));
            }
            // A remat recomputes its value, so it reads no location.
            EdgeEdit::Remat(remat) => self.mark_dead(ScalarAllocation::Reg(remat.dest)),
        }
    }

    /// Will anything read where this edit writes?
    fn dest_is_dead(&self, edit: EdgeEdit<E>) -> bool {
        match edit {
            EdgeEdit::Move(Move::Spill { to, .. }) => !self.is_live_slot(to),
            EdgeEdit::Move(Move::RegReg { to, .. }) | EdgeEdit::Move(Move::Reload { to, .. }) => {
                self.reg_is_dead(to)
            }
            EdgeEdit::Remat(remat) => self.reg_is_dead(remat.dest),
        }
    }

    /// Is every unit of `reg` dead?
    fn reg_is_dead(&self, reg: Reg<E>) -> bool {
        // With registers untracked, nothing is ever known to be dead in one.
        if !self.tracking_regs() {
            return false;
        }

        let machine = self.input.machine;

        // A non-allocatable register covers an *empty* unit range, so "every
        // unit is dead" would be vacuously true. Move generation writes these on
        // purpose, to feed an operand pinned to one.
        reg.is_allocatable(machine) && reg.iter_units(machine).all(|unit| !self.is_live_unit(unit))
    }

    /// Record that the edit at `index` is not happening.
    fn eliminate(&mut self, edit: EdgeEdit<E>, index: usize) {
        match edit {
            EdgeEdit::Move(Move::RegReg { .. }) => test_stat!(self.me, eliminated_reg_reg),
            EdgeEdit::Move(Move::Spill { .. }) => test_stat!(self.me, eliminated_spills),
            EdgeEdit::Move(Move::Reload { .. }) => test_stat!(self.me, eliminated_reloads),
            EdgeEdit::Remat(_) => test_stat!(self.me, eliminated_remats),
        }

        match edit {
            EdgeEdit::Move(_) => self.counts.dead_moves_eliminated.inc(),
            EdgeEdit::Remat(_) => self.counts.dead_remats_eliminated.inc(),
        }

        // Back to the edit list rather than the caller's copy: only the list
        // carries the position the event and trace want.
        let (pos, whole) = self.move_generation.edits()[index];
        if matches!(whole, Edit::CriticalEdge(_)) {
            test_stat!(self.me, eliminated_on_critical_edge);
        }

        crate::trace!("dropping dead edit {index} at {pos:?}: {edit:?}");
        event!(self.events, DeadEditEliminated { pos, edit, index });

        self.me.eliminated.push(index);
    }
}

/// Counters the tests read, to check a fixture reached the shape it was written
/// for.
#[cfg(test)]
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct TestStats {
    eliminated_spills: usize,
    eliminated_reloads: usize,
    eliminated_reg_reg: usize,
    eliminated_remats: usize,

    /// How many of the dropped edits sat on a critical edge.
    eliminated_on_critical_edge: usize,

    /// How many times the analysis visited a block.
    block_visits: usize,

    /// How many blocks were walked from a saturated seed.
    saturated_blocks: usize,

    /// The largest live set the walk held, sampled at each block's top.
    peak_live: usize,
}

#[cfg(test)]
impl TestStats {
    const fn new() -> Self {
        Self {
            eliminated_spills: 0,
            eliminated_reloads: 0,
            eliminated_reg_reg: 0,
            eliminated_remats: 0,
            eliminated_on_critical_edge: 0,
            block_visits: 0,
            saturated_blocks: 0,
            peak_live: 0,
        }
    }

    /// Did the pass find nothing to drop?
    fn eliminated_nothing(&self) -> bool {
        let Self {
            eliminated_spills,
            eliminated_reloads,
            eliminated_reg_reg,
            eliminated_remats,
            eliminated_on_critical_edge,
            block_visits: _,
            saturated_blocks: _,
            peak_live: _,
        } = self;
        *eliminated_spills == 0
            && *eliminated_reloads == 0
            && *eliminated_reg_reg == 0
            && *eliminated_remats == 0
            && *eliminated_on_critical_edge == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Allocation, Output, RegAllocation, StackAllocation,
        context::{Context, WhichContext},
        machine::Machine,
        test::TestInput,
    };
    use alloc::collections::{BTreeMap, BTreeSet};
    use core::sync::atomic::{AtomicUsize, Ordering};
    use mutatis::{
        check::{Check, CheckResult},
        mutators as m,
    };
    use std::{format, string::String, vec::Vec};

    /// The edits one run's results carry, in program order, and what the pass
    /// reached on the way.
    struct Run {
        edits: Vec<PlacedEdit>,
        stats: TestStats,
    }

    /// An edit, and where in the program it sits.
    ///
    /// The position is what makes "only ever deletes" a claim about the list
    /// rather than a multiset of shapes, where dropping one of two identical
    /// edits would be invisible.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct PlacedEdit {
        block: Block,
        insts_before: usize,
        edit: Edit,
    }

    /// Every edit in `output`, in the order a client walking the blocks sees.
    fn placed_edits<F>(input: &Input<'_, F>, output: &Output<'_>) -> Vec<PlacedEdit>
    where
        F: InputFunction,
    {
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
        edits
    }

    /// Allocate `test_input` with dead-move elimination at `level`.
    ///
    /// Edits come back through the public results rather than `MoveGeneration`,
    /// which reads them as a client would whatever representation
    /// `run_dispatch` picked. `Ok(None)` is the one failure a test may walk away
    /// from, since out of registers says something about the generated input
    /// rather than this pass.
    fn run_at(test_input: &TestInput, level: MoveEliminationLevel) -> Result<Option<Run>, String> {
        let mut test_input = test_input.clone();
        test_input.options.dead_move_elimination_level = level;

        // These tests measure *this* pass; at their default levels the others
        // would change edits of their own, and every assertion below would
        // read the sum of them.
        test_input.options.redundant_move_elimination_level = MoveEliminationLevel::None;
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
                WhichContext::Context8 => context.context8.dead_move_elimination.test_stats.clone(),
                #[cfg(feature = "entity-repr-16")]
                WhichContext::Context16 => {
                    context.context16.dead_move_elimination.test_stats.clone()
                }
                WhichContext::Context32 => {
                    context.context32.dead_move_elimination.test_stats.clone()
                }
            };

            let edits = placed_edits(input, &Output::new(&context));
            Ok(Some(Run { edits, stats }))
        });

        context.reset();
        assert!(context.is_reset(), "the pass's storage should reset");
        result
    }

    /// `run_at` for a hand-built fixture, which is meant to allocate: one that
    /// stopped should say so rather than quietly pass.
    fn allocated(test_input: &TestInput, level: MoveEliminationLevel) -> Run {
        run_at(test_input, level)
            .expect("this fixture allocates")
            .expect("this fixture does not run out of registers")
    }

    /// Is `small` what is left of `large` after deleting some of its elements?
    fn is_subsequence(small: &[PlacedEdit], large: &[PlacedEdit]) -> bool {
        let mut large = large.iter();
        small
            .iter()
            .all(|edit| large.any(|candidate| candidate == edit))
    }

    /// Which positions of `large` the greedy match of `small` into it skipped,
    /// or `None` if `small` is not a subsequence.
    ///
    /// When `large` holds equal edits, which of them this calls deleted is an
    /// artifact of matching at the leftmost one: deleting either of two equal
    /// edits with nothing surviving between them leaves the same list, and
    /// there is no fact of the matter about which survived. Compare the lists
    /// themselves, with `surviving`, to ask a question that does not depend on
    /// the choice.
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

    /// What is left of `edits` once the positions in `drop` are removed.
    fn surviving(edits: &[PlacedEdit], drop: &BTreeSet<usize>) -> Vec<PlacedEdit> {
        edits
            .iter()
            .enumerate()
            .filter(|(i, _)| !drop.contains(i))
            .map(|(_, &edit)| edit)
            .collect()
    }

    /// Deleting either of two equal edits with nothing surviving between them
    /// leaves the same list, so `deleted` cannot tell the two choices apart but
    /// `surviving` reports them as the same answer.
    ///
    /// Equal edits are legitimate: two reloads of one slot into one register on
    /// the same edge is what move generation emits for a value wanted along
    /// more than one path.
    #[test]
    fn equal_edits_are_compared_by_what_survives() {
        let block = Block::try_new(0).unwrap();
        let edit = |i: usize, slot: usize| PlacedEdit {
            block,
            insts_before: i,
            edit: Edit::Move(Move::Reload {
                from: SpillSlot::try_new(slot).unwrap(),
                to: Reg::try_new(0).unwrap(),
            }),
        };

        // `[1]` and `[2]` are equal, and nothing survives between them.
        let none = Vec::from([edit(0, 0), edit(1, 1), edit(1, 1), edit(2, 2)]);
        let kept = Vec::from([edit(0, 0), edit(1, 1), edit(2, 2)]);

        // Dropping either one leaves `kept`, so the lists agree ...
        for drop in [1, 2] {
            let drop = BTreeSet::from([drop]);
            assert_eq!(surviving(&none, &drop), kept);
        }

        // ... while `deleted` can only name the rightmost of them.
        assert_eq!(deleted(&kept, &none), Some(Vec::from([2])));

        // With an edit surviving between them, the choice is visible in the
        // list and both comparisons see it.
        let none = Vec::from([edit(1, 1), edit(9, 9), edit(1, 1)]);
        assert_eq!(
            surviving(&none, &BTreeSet::from([0])),
            Vec::from([edit(9, 9), edit(1, 1)]),
        );
        assert_eq!(
            surviving(&none, &BTreeSet::from([2])),
            Vec::from([edit(1, 1), edit(9, 9)]),
        );
        assert_eq!(
            deleted(&[edit(9, 9), edit(1, 1)], &none),
            Some(Vec::from([0]))
        );
        assert_eq!(
            deleted(&[edit(1, 1), edit(9, 9)], &none),
            Some(Vec::from([2]))
        );
    }

    /// How many of `edits` are the kind `want` accepts, unwrapping a
    /// critical-edge edit: these tests ask what an edit does, not where it is.
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

    fn is_reg_reg(edit: EdgeEdit) -> bool {
        matches!(edit, EdgeEdit::Move(Move::RegReg { .. }))
    }

    fn is_remat(edit: EdgeEdit) -> bool {
        matches!(edit, EdgeEdit::Remat(_))
    }

    /// Nothing is eliminated at `None`: the durable form of "byte-identical to
    /// the behavior before this pass existed".
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

    /// Every level only deletes from the list move generation produced, and
    /// `Global` deletes everything `Local` does.
    ///
    /// Unlike redundant-move elimination, that containment holds here: `Local`
    /// seeds every block at the top of the lattice, above whatever the fixpoint
    /// settles on, and the transfer is monotone.
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
    /// This pass caches by reverse-post-order position rather than by block, so
    /// a stale entry a `reset` left behind would read as a real live-out set.
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
                        let edits = ok.then(|| placed_edits(input, &Output::new(&context)));
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

    /// Turning registers off only narrows what the pass drops: tracking spill
    /// slots alone, the only destination it can call dead is a slot, so no
    /// reload, register-to-register move, or remat may go.
    #[test]
    fn the_option_only_narrows() -> CheckResult<TestInput> {
        /// How many spills the narrowed pass dropped, so a pass that stopped
        /// eliminating could not make this vacuous.
        static SPILLS: AtomicUsize = AtomicUsize::new(0);
        SPILLS.store(0, Ordering::Relaxed);

        let result = Check::new().iters(5_000).run_with(
            m::default::<TestInput>(),
            crate::test::corpus(),
            |test_input: &TestInput| -> Result<(), String> {
                let mut narrowed = test_input.clone();
                narrowed.options.eliminate_dead_register_moves = false;

                let (Some(wide), Some(narrow)) = (
                    run_at(test_input, MoveEliminationLevel::Global)?,
                    run_at(&narrowed, MoveEliminationLevel::Global)?,
                ) else {
                    return Ok(());
                };
                let Some(none) = run_at(test_input, MoveEliminationLevel::None)? else {
                    return Ok(());
                };

                if narrow.stats.eliminated_reloads != 0
                    || narrow.stats.eliminated_reg_reg != 0
                    || narrow.stats.eliminated_remats != 0
                {
                    return Err(format!(
                        "with registers untracked, something other than a spill \
                         was eliminated: {:?}",
                        narrow.stats,
                    ));
                }
                SPILLS.fetch_add(narrow.stats.eliminated_spills, Ordering::Relaxed);

                let (Some(by_narrow), Some(by_wide)) = (
                    deleted(&narrow.edits, &none.edits),
                    deleted(&wide.edits, &none.edits),
                ) else {
                    return Err(String::from("a level above `None` did more than delete"));
                };
                if let Some(i) = by_narrow.iter().find(|i| !by_wide.contains(i)) {
                    return Err(format!(
                        "untracked registers eliminated edit {i}, which tracking them kept:\n\
                         none   = {:?}\nnarrow = {:?}\nwide   = {:?}",
                        none.edits, narrow.edits, wide.edits,
                    ));
                }
                Ok(())
            },
        );

        if result.is_ok() {
            assert!(
                SPILLS.load(Ordering::Relaxed) > 0,
                "no dead spill was ever found with registers untracked, so this \
                 check says nothing about the option",
            );
        }
        result
    }

    /// Every shape the pass can reach is reached by some input.
    ///
    /// Every test above only says the pass did not eliminate too much, so a pass
    /// that quietly stopped eliminating would pass them all. This one says it
    /// eliminated something, shape by shape.
    #[test]
    fn every_shape_is_reached() -> CheckResult<TestInput> {
        /// How many of the inputs tried may be ones the allocator gave up on
        /// before the pass ran at all. A ceiling rather than a floor, for the
        /// reason `checker::tests::checker_properties` gives.
        const SKIP_CEILING_PERCENT: usize = 60;

        /// The seed this check searches from.
        ///
        /// The only pinned seed here, because this is the only check asserting a
        /// search *found* something. Unseeded, it would turn on which other
        /// tests drew from the generator first, and the rarer shapes are rare
        /// enough to fall off an unlucky draw.
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
            SPILLS: eliminated_spills = "a dead spill",
            RELOADS: eliminated_reloads = "a dead reload",
            REG_REG: eliminated_reg_reg = "a dead register-to-register move",
            REMATS: eliminated_remats = "a dead rematerialization",
            ON_EDGES: eliminated_on_critical_edge = "a dead edit on a critical edge",
            VISITS: block_visits = "a block the fixpoint visited",
            PEAK: peak_live = "a block walked holding anything live at its top",
        }
    }

    /// A register-to-register move whose destination is overwritten before
    /// anything reads it goes.
    ///
    /// The overwrite is in a later block, so only `Global` sees it. The
    /// visualizer's `dead-edits` fixture is built from the same input.
    #[test]
    fn a_move_into_a_register_nothing_reads_goes() {
        let test_input = TestInput::with_a_register_move_overwritten_in_a_later_block();
        let none = allocated(&test_input, MoveEliminationLevel::None);
        let local = allocated(&test_input, MoveEliminationLevel::Local);
        let global = allocated(&test_input, MoveEliminationLevel::Global);

        assert_eq!(count(&none.edits, is_reg_reg), 1);
        assert_eq!(local.edits, none.edits, "`Local` cannot see past a block");
        assert!(local.stats.eliminated_nothing());

        assert_eq!(count(&global.edits, is_reg_reg), 0);
        assert_eq!(global.stats.eliminated_reg_reg, 1);

        // The slot traffic is what the read actually needs, and stays.
        assert_eq!(count(&global.edits, is_spill), count(&none.edits, is_spill));
        assert_eq!(
            count(&global.edits, is_reload),
            count(&none.edits, is_reload)
        );
    }

    /// A reload into a register nothing reads goes: two values are pinned to
    /// the same register at the top of a loop body, so one is reloaded into it
    /// and immediately displaced by the other's definition.
    #[test]
    fn a_reload_nothing_reads_goes() {
        let test_input = TestInput::with_a_fixed_def_spilled_beside_a_fixed_read();
        let none = allocated(&test_input, MoveEliminationLevel::None);
        let local = allocated(&test_input, MoveEliminationLevel::Local);
        let global = allocated(&test_input, MoveEliminationLevel::Global);

        assert_eq!(count(&none.edits, is_reload), 2);
        assert_eq!(local.edits, none.edits);
        assert!(local.stats.eliminated_nothing());

        assert_eq!(count(&global.edits, is_reload), 1);
        assert_eq!(global.stats.eliminated_reloads, 1);
    }

    /// A store into a slot nothing reloads goes: the shape regalloc3's
    /// `dead_spill_elimination` is entirely about.
    ///
    /// The value crosses a crowded block, but its remat cost means every read
    /// past that block recomputes it instead of reloading.
    #[test]
    fn a_spill_into_a_slot_nothing_reloads_goes() {
        let mut test_input = TestInput::with_a_value_carried_past_a_crowded_block(true);
        test_input.set_remat_costs(Some(crate::input::RematCost::CheaperThanReload));
        let none = allocated(&test_input, MoveEliminationLevel::None);
        let local = allocated(&test_input, MoveEliminationLevel::Local);
        let global = allocated(&test_input, MoveEliminationLevel::Global);

        assert_eq!(count(&none.edits, is_spill), 1);
        assert_eq!(count(&none.edits, is_reload), 0, "the reads remat instead");
        assert_eq!(local.edits, none.edits);
        assert!(local.stats.eliminated_nothing());

        assert_eq!(count(&global.edits, is_spill), 0);
        assert_eq!(global.stats.eliminated_spills, 1);

        // A dead *slot* says nothing about the register the remat writes.
        assert_eq!(count(&global.edits, is_remat), 1);
    }

    /// `Local` reaches every block from a saturated seed, and `Global` reaches
    /// none of them from one. Nothing else here would notice a level reaching
    /// for the wrong seed.
    #[test]
    fn only_local_saturates() -> CheckResult<TestInput> {
        Check::new().iters(2_000).run_with(
            m::default::<TestInput>(),
            crate::test::corpus(),
            |test_input: &TestInput| -> Result<(), String> {
                let Some(local) = run_at(test_input, MoveEliminationLevel::Local)? else {
                    return Ok(());
                };
                let Some(global) = run_at(test_input, MoveEliminationLevel::Global)? else {
                    return Ok(());
                };
                if local.stats.saturated_blocks == 0 {
                    return Err(String::from(
                        "`Local` walked no block from a saturated seed",
                    ));
                }
                if local.stats.block_visits != 0 {
                    return Err(String::from("`Local` ran the fixpoint"));
                }
                if global.stats.saturated_blocks != 0 {
                    return Err(String::from(
                        "`Global` walked a block from a saturated seed",
                    ));
                }
                Ok(())
            },
        )
    }

    /// The arithmetic `Event::MoveEmitted`'s doc describes takes a move's event
    /// to its edit even when this pass is the one deleting.
    ///
    /// The mirror of redundant-move elimination's test of the same name, reading
    /// `DeadEditEliminated` and pinning the *other* pass off, so the fold is
    /// over one pass's deletions either way.
    #[cfg(feature = "visualizer")]
    #[test]
    fn a_move_event_still_finds_its_edit() -> CheckResult<TestInput> {
        use crate::events::Event as LoggedEvent;

        /// How many runs had something to eliminate, so a pass that stopped
        /// eliminating could not make this vacuous.
        static ELIMINATED: AtomicUsize = AtomicUsize::new(0);
        ELIMINATED.store(0, Ordering::Relaxed);

        fn check<E>(ctx: &ContextInner<E>) -> Result<(), String>
        where
            E: EntityRepr,
        {
            let edits = ctx.move_generation.edits();

            // The gone indices, in the numbering both events use.
            let mut removed = Vec::new();
            for (_, event) in ctx.events.iter() {
                if let LoggedEvent::DeadEditEliminated { index, .. } = *event {
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
                    // No edit left for it to address.
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
                // `removed` reads `DeadEditEliminated` alone, so this has to be
                // the only pass dropping edits.
                let mut test_input = test_input.clone();
                test_input.options.redundant_move_elimination_level = MoveEliminationLevel::None;
                test_input.options.dead_move_elimination_level = MoveEliminationLevel::Global;

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

    /// One tracked location, as a plain index rather than the pass's entities,
    /// so the oracle cannot inherit a bug from what it checks.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
    enum Loc {
        Unit(usize),
        Slot(usize),
    }

    /// One thing the oracle walks over inside a block.
    #[derive(Clone, Copy, Debug)]
    enum Item {
        Inst(Inst),

        /// An edit, and its position in the flat edit numbering.
        Edit(usize, EdgeEdit),
    }

    /// A block, cut into the pieces the oracle's transfer needs.
    #[derive(Default)]
    struct OracleBlock {
        /// The edits above the block's first instruction, in program order.
        /// They run *before* the block's parameters arrive, so backwards they
        /// come after the parameters are marked read.
        arriving: Vec<Item>,

        /// Everything from the first instruction onwards, in program order,
        /// minus the critical-edge edits.
        rest: Vec<Item>,

        /// This block's outgoing critical-edge edits, as `(which outgoing edge,
        /// flat index, edit)`, in program order. Each belongs to one edge, not
        /// to the union over all of them.
        edges: Vec<(usize, usize, EdgeEdit)>,
    }

    /// Where `alloc` lives, as a list of single locations. A fresh `Vec` every
    /// call, where the pass hands one around: being slow is the point.
    fn locs_of(
        machine: &Machine,
        output: &Output<'_>,
        track_regs: bool,
        alloc: Allocation,
    ) -> Vec<Loc> {
        match alloc {
            Allocation::Reg(RegAllocation::Reg(r)) => reg_locs(machine, track_regs, r),
            Allocation::Reg(RegAllocation::RegGroup(group)) => group
                .members(machine)
                .iter()
                .flat_map(|&r| reg_locs(machine, track_regs, r))
                .collect(),
            Allocation::Stack(StackAllocation::SpillSlot(slot)) => {
                Vec::from([Loc::Slot(slot.index())])
            }
            Allocation::Stack(StackAllocation::SpillSlotGroup(group)) => output
                .spill_slot_group_members(group)
                .map(|slot| Loc::Slot(slot.index()))
                .collect(),
        }
    }

    /// The locations a register covers.
    ///
    /// Empty when registers are untracked, and empty when the register covers no
    /// units and so may never be allocated: two reasons to have nothing to say
    /// about it, which come to the same thing.
    fn reg_locs(machine: &Machine, track_regs: bool, reg: Reg) -> Vec<Loc> {
        if !track_regs {
            return Vec::new();
        }
        let units = reg.units(machine);
        (units.start.index()..units.end.index())
            .map(Loc::Unit)
            .collect()
    }

    /// Run one edit backwards over `live`, recording it in `dead` when nothing
    /// reads its destination.
    fn oracle_edit(
        machine: &Machine,
        track_regs: bool,
        live: &mut BTreeSet<Loc>,
        flat: usize,
        edit: EdgeEdit,
        dead: &mut BTreeSet<usize>,
    ) {
        let reg_locs = |reg| reg_locs(machine, track_regs, reg);
        let (written, read) = match edit {
            EdgeEdit::Move(Move::RegReg { from, to }) => (reg_locs(to), reg_locs(from)),
            EdgeEdit::Move(Move::Spill { from, to }) => {
                (Vec::from([Loc::Slot(to.index())]), reg_locs(from))
            }
            EdgeEdit::Move(Move::Reload { from, to }) => {
                (reg_locs(to), Vec::from([Loc::Slot(from.index())]))
            }
            // A remat recomputes its value, so it reads nothing.
            EdgeEdit::Remat(remat) => (reg_locs(remat.dest), Vec::new()),
        };

        // An untracked destination is not a destination nothing reads: with
        // registers off, or for a register covering no units, there is nothing
        // to say. Move generation writes those on purpose, to feed an operand
        // pinned to one.
        if !written.is_empty() && written.iter().all(|loc| !live.contains(loc)) {
            // Dead, so it does not happen, and so does not read either.
            dead.insert(flat);
            return;
        }

        for loc in written {
            live.remove(&loc);
        }
        for loc in read {
            live.insert(loc);
        }
    }

    /// A deliberately naive backwards liveness over locations, and the edits it
    /// finds dead.
    ///
    /// Everything the pass does for speed is absent: the live set is a
    /// `BTreeSet` of plain indices, only the `Global` answer is modelled so
    /// saturation is never needed, the fixpoint sweeps every block in input
    /// order until nothing moves, and every block's live-in is kept.
    ///
    /// The flat numbering is `placed_edits`'s: blocks in the function's own
    /// order, edits within a block in `Output::block_insts_and_edits`'s.
    fn oracle_dead_edits<F>(input: &Input<'_, F>, output: &Output<'_>) -> BTreeSet<usize>
    where
        F: InputFunction,
    {
        let func = input.func;
        let machine = input.machine;
        let track_regs = input.options.eliminate_dead_register_moves;
        let len_blocks = func.len_blocks();

        // The pass decides edits in reachable blocks and on edges out of
        // reachable predecessors, and nowhere else.
        let mut reachable = Vec::from_iter(core::iter::repeat_n(false, len_blocks));
        let mut stack = Vec::from([func.entry_block()]);
        reachable[func.entry_block().index()] = true;
        while let Some(block) = stack.pop() {
            for succ in func.block(block).successors() {
                if !core::mem::replace(&mut reachable[succ.index()], true) {
                    stack.push(succ);
                }
            }
        }

        // Number the edits exactly as `placed_edits` does, including in
        // unreachable blocks, whose edits still take up indices.
        let mut blocks = Vec::from_iter((0..len_blocks).map(|_| OracleBlock::default()));
        let mut flat = 0;
        for (block, _) in func.blocks() {
            let cut = &mut blocks[block.index()];
            let mut seen_inst = false;
            for item in output.block_insts_and_edits(func, block) {
                match item {
                    InstOrEdit::Inst(inst) => {
                        seen_inst = true;
                        cut.rest.push(Item::Inst(inst));
                    }
                    InstOrEdit::Edit(edit) => {
                        let index = flat;
                        flat += 1;
                        match edit {
                            Edit::CriticalEdge(CriticalEdgeEdit { succ, edit, .. }) => {
                                cut.edges.push((succ, index, edit));
                            }
                            Edit::Move(mv) if !seen_inst => {
                                cut.arriving.push(Item::Edit(index, EdgeEdit::Move(mv)));
                            }
                            Edit::Remat(remat) if !seen_inst => {
                                cut.arriving.push(Item::Edit(index, EdgeEdit::Remat(remat)));
                            }
                            Edit::Move(mv) => cut.rest.push(Item::Edit(index, EdgeEdit::Move(mv))),
                            Edit::Remat(remat) => {
                                cut.rest.push(Item::Edit(index, EdgeEdit::Remat(remat)))
                            }
                        }
                    }
                }
            }
        }

        // Walk one block backwards, leaving `live` holding its live-in set.
        let transfer = |block: Block, live: &mut BTreeSet<Loc>, dead: &mut BTreeSet<usize>| {
            let cut = &blocks[block.index()];
            let walk = |items: &[Item], live: &mut BTreeSet<Loc>, dead: &mut BTreeSet<usize>| {
                for item in items.iter().rev() {
                    match *item {
                        Item::Edit(flat, edit) => {
                            oracle_edit(machine, track_regs, live, flat, edit, dead)
                        }
                        Item::Inst(inst) => {
                            let allocs = output.inst_allocs(inst);
                            // Backwards: late before early, and a def before
                            // the read it may share a register with.
                            for pos in [Position::Late, Position::Early] {
                                for kind in [DefUse::Def, DefUse::Use] {
                                    for (i, op) in func.inst(inst).operands().enumerate() {
                                        if op.pos() != pos
                                            || op.kind() != kind
                                            || op.val().is_none()
                                        {
                                            continue;
                                        }
                                        for loc in locs_of(machine, output, track_regs, allocs[i]) {
                                            match kind {
                                                DefUse::Def => live.remove(&loc),
                                                DefUse::Use => live.insert(loc),
                                            };
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            };

            walk(&cut.rest, live, dead);

            // Parameters arrive where `Output::block_param_allocs` says, which
            // is a read nothing in the block names. Mark it on both sides of the
            // arriving run: the checker pins the arrival after those edits
            // normally, but against the entry state when the block also departs
            // from that same gap.
            let gen_params = |live: &mut BTreeSet<Loc>| {
                for &alloc in output.block_param_allocs(block) {
                    let Some(alloc) = alloc else { continue };
                    live.extend(locs_of(machine, output, track_regs, alloc));
                }
            };

            gen_params(live);
            walk(&cut.arriving, live, dead);
            gen_params(live);
        };

        // One edge at a time: an edge's critical-edge edits run on that edge
        // alone, so they apply to a copy of the successor's live-in.
        let live_out =
            |block: Block, live_in: &BTreeMap<usize, BTreeSet<Loc>>, dead: &mut BTreeSet<usize>| {
                let mut out = BTreeSet::new();
                for (i, succ) in func.block(block).successors().enumerate() {
                    let mut edge = live_in.get(&succ.index()).cloned().unwrap_or_default();
                    for &(on, flat, edit) in blocks[block.index()].edges.iter().rev() {
                        if on == i {
                            oracle_edit(machine, track_regs, &mut edge, flat, edit, dead);
                        }
                    }
                    out.extend(edge);
                }
                out
            };

        // Sweep every reachable block until nothing changes. No worklist, no
        // ordering.
        let mut live_in: BTreeMap<usize, BTreeSet<Loc>> = BTreeMap::new();
        let mut ignored = BTreeSet::new();
        loop {
            let mut changed = false;
            for (block, _) in func.blocks() {
                if !reachable[block.index()] {
                    continue;
                }
                let mut live = live_out(block, &live_in, &mut ignored);
                transfer(block, &mut live, &mut ignored);
                if live_in.get(&block.index()) != Some(&live) {
                    live_in.insert(block.index(), live);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        // With the answer settled, say which edits are dead.
        let mut dead = BTreeSet::new();
        for (block, _) in func.blocks() {
            if !reachable[block.index()] {
                continue;
            }
            let mut live = live_out(block, &live_in, &mut dead);
            transfer(block, &mut live, &mut dead);
        }
        dead
    }

    /// The pass drops exactly the edits an independent, naive analysis calls
    /// dead.
    ///
    /// Every other test here says the pass did not delete too much; this one
    /// says it deleted the right things, which catches a transfer function that
    /// is conservative in the wrong place, or wrong in a way the checker does
    /// not see.
    #[test]
    fn the_pass_matches_a_naive_oracle() -> CheckResult<TestInput> {
        /// How many edits the pass eliminated, so a pass that stopped
        /// eliminating could not make this vacuous.
        static ELIMINATED: AtomicUsize = AtomicUsize::new(0);
        ELIMINATED.store(0, Ordering::Relaxed);

        let result = Check::new().iters(5_000).run_with(
            m::default::<TestInput>(),
            crate::test::corpus(),
            |test_input: &TestInput| -> Result<(), String> {
                let Some(none) = run_at(test_input, MoveEliminationLevel::None)? else {
                    return Ok(());
                };
                let Some(global) = run_at(test_input, MoveEliminationLevel::Global)? else {
                    return Err(String::from(
                        "`Global` ran out of registers where `None` did not",
                    ));
                };
                let by_pass: BTreeSet<usize> = deleted(&global.edits, &none.edits)
                    .ok_or_else(|| String::from("`Global` did more than delete"))?
                    .into_iter()
                    .collect();
                ELIMINATED.fetch_add(by_pass.len(), Ordering::Relaxed);

                // The oracle reads the unoptimized results: the same list the
                // pass decided against.
                let mut unoptimized = test_input.clone();
                unoptimized.options.redundant_move_elimination_level = MoveEliminationLevel::None;
                unoptimized.options.dead_move_elimination_level = MoveEliminationLevel::None;

                let mut context = Context::new();
                let by_oracle = unoptimized.with_input(|input| {
                    crate::run_dispatch(&mut context, input)
                        .map_err(|e| format!("allocation failed: {e:?}"))?;
                    Ok::<_, String>(oracle_dead_edits(input, &Output::new(&context)))
                });
                context.reset();
                let by_oracle = by_oracle?;

                // Compare the lists the two answers leave, not the index sets:
                // with equal edits in the list, which index is called deleted
                // is not well defined, but the surviving list is. See
                // `deleted`.
                let kept_by_oracle = surviving(&none.edits, &by_oracle);
                if kept_by_oracle != global.edits {
                    return Err(format!(
                        "the pass and the oracle disagree:\n\
                         only the pass   = {:?}\n\
                         only the oracle = {:?}\n\
                         the pass kept   = {:?}\n\
                         the oracle kept = {:?}\n\
                         edits = {:?}",
                        by_pass.difference(&by_oracle).collect::<Vec<_>>(),
                        by_oracle.difference(&by_pass).collect::<Vec<_>>(),
                        global.edits,
                        kept_by_oracle,
                        none.edits,
                    ));
                }
                Ok(())
            },
        );

        if result.is_ok() {
            assert!(
                ELIMINATED.load(Ordering::Relaxed) > 0,
                "nothing was eliminated anywhere, so the oracle only ever \
                 agreed that nothing was dead",
            );
        }
        result
    }
}
