//! Demanded-move hoisting.
//!
//! Move generation places each edit where a span boundary or an edge needs it,
//! so every arm of a branch can begin by writing the same value into the same
//! location: each arm reloads one slot into `r3`, say. Redundant-move
//! elimination only drops a write an equal one dominates, and spill placement
//! only climbs while a block has one successor, so neither merges siblings.
//! This pass hoists such writes into one move before the branch and drops the
//! arms' copies.
//!
//! # The analysis
//!
//! A backwards, flow-sensitive "must" analysis of what each location is
//! *demanded* to hold: location `l` demands the value parts `R` at a point when
//! every path from there first touches `l` with a surviving edit leaving
//! exactly `R` in it.
//!
//! Per location the lattice is flat:
//!
//! ```text
//!                   Top             (no path has touched it yet)
//!                /   |     \
//!               /    |      \
//!              /     |       \
//!     Demand(R1)  Demand(R2)  ...   (every path first writes exactly R)
//!              \     |       /
//!               \    |      /
//!                \   |     /
//!                  Bottom           (some path reads it, writes something
//!                                    else, or leaves the extended block)
//! ```
//!
//! Two `Demand`s meet to `Bottom` unless they are equal.
//!
//! The transfer, backwards:
//!
//! * A surviving edit writing `d` kills every demand overlapping `d` but not
//!   `d` itself, sets `d` to `Demand(what it writes)`, then kills every demand
//!   overlapping what it reads.
//! * An instruction kills every demand overlapping its operands or clobbers.
//! * An edit an earlier pass eliminated is the identity.
//!
//! # No partial redundancy
//!
//! The analysis only covers *extended blocks*: a branching block, the
//! successors whose only predecessor it is and which take no parameters,
//! theirs, and so on. That is the textbook extended basic block, with two
//! restrictions: the root must branch, with every successor qualifying (see
//! `may_hoist_into`), and no block below the root takes parameters. An extended
//! block may span across `Region`s.
//!
//! A block reachable from more than one predecessor (a join, or any entry to a
//! cycle, reducible or not) is never inside an extended block, so every path
//! into one of its blocks passes through its root: a hoisted move never runs
//! on a path that did not already pay for one. Excluding parameters is a
//! simplification, not a property of the input: it keeps value names from
//! changing inside an extended block, at the cost of skipping the few roots
//! with a parameterized successor. An edge into a child carries its edits at
//! the child's top, never in the gap before the root's terminator.
//!
//! Extended blocks are acyclic, so one post-order walk settles them without a
//! fixpoint, and `Top` never needs representing: a location absent from a set
//! is `Bottom`.
//!
//! # The rewrite
//!
//! As spill placement does, this climbs while climbing pays. For each location
//! `l` demanded just before a root's terminator, it may insert `l <- s` there,
//! from any `s` known to hold everything demanded. A bottom-up dynamic program
//! compares that against the children's own best answers, under an
//! estimated-cycles cost model, and keeps the insertion only when strictly
//! cheaper. An insertion replaces at least two writes, so neither the estimate
//! nor the number of edits ever rises.
//!
//! # Against the other passes
//!
//! This runs after redundant- and dead-move elimination, against the edit list
//! as move generation left it, treating both passes' eliminations as not
//! happening.
//!
//! * The state after an insertion holds everything it did before, plus `l`
//!   holding `R` early, and nothing reads `l` in between: every write
//!   redundant-move elimination dropped stays redundant.
//! * The writes replaced survived dead-move elimination, so the insertion is
//!   not dead. Its source must also survive it, so a source has to be live out
//!   of the root as far as that pass knows.

use crate::{
    Entity as _, Input,
    context::ContextInner,
    counts::Counts,
    dead_move_elimination::DeadMoveElimination,
    entity::{
        Block, DecisionsStorageIndex, EntityRange, EntityRepr, EntryDemandsStorageIndex, Inst,
        PrimaryMap, SecondaryMap,
    },
    error::IResult,
    events::EventsLog,
    input::{DefUse, InputBlock, InputFunction, InputInst, MoveEliminationLevel},
    machine::{Interfere, Machine, Reg},
    move_generation::{MoveGeneration, PackedMovePosition},
    output::{EdgeEdit, Edit, InstOrEdit, Move, OutputInner, ScalarAllocation, block_iter},
    redundant_move_elimination::{Fact, Part, Recorded, edge_edit_at, scalars_of},
    region_tree::RegionTree,
    rpo::Rpo,
    spill_slot_allocation::SpillSlots,
    timing::Timing,
};
use alloc::vec::Vec;

macro_rules! test_stat {
    ( $me:expr, $field:ident ) => {{
        #[cfg(test)]
        {
            $me.test_stats.$field += 1;
        }
    }};
}

/// Run the demanded-move hoisting pass.
pub(crate) fn hoist_demanded_moves<E>(
    context: &mut ContextInner<E>,
    input: &Input<'_, impl InputFunction>,
) -> IResult<()>
where
    E: EntityRepr,
{
    if !context.redundant_move_elimination.recorded.enabled {
        return Ok(());
    }

    let _timing = Timing::new("hoist demanded moves");

    let mut hoister = Hoister {
        input,
        output: &context.output,
        move_generation: &context.move_generation,
        spill_slots: &context.spill_slots,
        rpo: &context.rpo,
        region_tree: &context.region_tree,
        recorded: &context.redundant_move_elimination.recorded,
        redundant: &context.redundant_move_elimination.eliminated,
        dead: &context.dead_move_elimination,
        counts: &mut context.counts,
        events: &mut context.events,
        me: &mut context.demanded_moves,
    };
    hoister.run();

    context.demanded_moves.eliminated.sort_unstable();
    debug_assert!(
        context
            .demanded_moves
            .eliminated
            .windows(2)
            .all(|w| w[0] < w[1]),
        "must have no duplicates",
    );
    context.demanded_moves.inserted.sort_by_key(|&(pos, _)| pos);

    // The edits are removed and inserted by `crate::remove_eliminated_edits`,
    // with the other passes' removals.
    Ok(())
}

/// Should redundant-move elimination record what this pass needs?
pub(crate) fn wants_recording(input: &Input<'_, impl InputFunction>) -> bool {
    input.options.hoist_demanded_moves
        && input.options.redundant_move_elimination_level == MoveEliminationLevel::Global
}

/// Is `block` the root of an extended block with something to hoist into: does
/// it branch, and is it the only predecessor of every block it branches to?
pub(crate) fn may_hoist_into(func: &impl InputFunction, block: crate::Block) -> bool {
    let input_block = func.block(block);
    input_block.len_successors() >= 2
        && input_block
            .successors()
            .all(|succ| is_extended_block_child(func, block, succ))
}

/// Does `succ` have `block` as its only way in, and no parameters to rename?
fn is_extended_block_child(
    func: &impl InputFunction,
    block: crate::Block,
    succ: crate::Block,
) -> bool {
    let input_succ = func.block(succ);
    succ != block
        && succ != func.entry_block()
        && input_succ.len_predecessors() == 1
        && input_succ.len_params() == 0
}

/// The estimated cost of running one edit once in `block`, as the `run`
/// example's estimated cycles count it.
fn edit_cost<E>(
    input: &Input<'_, impl InputFunction>,
    region_tree: &RegionTree<E>,
    block: Block<E>,
    edit: EdgeEdit<E>,
) -> f64
where
    E: EntityRepr,
{
    let base = match edit {
        EdgeEdit::Move(Move::RegReg { .. }) | EdgeEdit::Remat(_) => 1.0,
        EdgeEdit::Move(Move::Spill { .. }) | EdgeEdit::Move(Move::Reload { .. }) => 5.0,
    };
    base * block.weight(input, region_tree)
}

/// The move from `from` to `to`, or `None` when no single move can make it:
/// between two slots, or between locations of different banks or sizes.
fn move_between<E>(
    machine: &Machine,
    spill_slots: &SpillSlots<E>,
    from: ScalarAllocation<E>,
    to: ScalarAllocation<E>,
) -> Option<Move<E>>
where
    E: EntityRepr,
{
    match (from, to) {
        (ScalarAllocation::Reg(from), ScalarAllocation::Reg(to)) => {
            (from.bank(machine) == to.bank(machine)).then_some(Move::RegReg { from, to })
        }
        (ScalarAllocation::Reg(from), ScalarAllocation::Stack(to)) => (to.size(spill_slots)
            == from.bank(machine).size(machine))
        .then_some(Move::Spill { from, to }),
        (ScalarAllocation::Stack(from), ScalarAllocation::Reg(to)) => (from.size(spill_slots)
            == to.bank(machine).size(machine))
        .then_some(Move::Reload { from, to }),
        (ScalarAllocation::Stack(_), ScalarAllocation::Stack(_)) => None,
    }
}

/// One location's demand.
#[derive(Clone, Copy, Debug)]
struct Demand {
    /// An edit leaving exactly the parts demanded, whose `Recorded::written`
    /// names them. Every write this demand stands for leaves the same parts.
    parts_of: usize,

    /// What the writes this demand stands for cost, all told, if they are
    /// left where they are or wherever below they were best placed.
    cost: f64,

    /// How the subtree this demand came from settled it: the edit index of the
    /// one write it stands for, or `None` when it is a block's bottom passing
    /// its children's demands through.
    target: Option<usize>,
}

/// The demands holding at one point, one per location that has one.
///
/// Sorted by location. Locations do not overlap: a write kills every demand on
/// a location overlapping it.
type Demands<E> = Vec<(ScalarAllocation<E>, Demand)>;

/// What a block's bottom decided for one location.
#[derive(Clone, Copy, Debug)]
struct Decision<E>
where
    E: EntityRepr,
{
    loc: ScalarAllocation<E>,

    /// The source to hoist from, or `None` to leave the children be.
    source: Option<ScalarAllocation<E>>,
}

/// Reusable storage for the pass.
pub(crate) struct DemandedMoves<E>
where
    E: EntityRepr,
{
    /// Each extended-block child's demands on entry, as a range within
    /// `entry_demands`.
    entry: SecondaryMap<Block<E>, Option<EntityRange<EntryDemandsStorageIndex>>>,

    /// Contiguous storage for those, each block's sorted by location.
    entry_demands: PrimaryMap<EntryDemandsStorageIndex, (ScalarAllocation<E>, Demand)>,

    /// Each candidate root's decisions, as a range within `decisions`.
    decided: SecondaryMap<Block<E>, Option<EntityRange<DecisionsStorageIndex>>>,

    /// Contiguous storage for those.
    decisions: PrimaryMap<DecisionsStorageIndex, Decision<E>>,

    /// The demands at the point the backwards walk has reached.
    live: Demands<E>,

    /// Scratch space for a meet.
    meet: Demands<E>,

    /// The block's instructions and edits, collected forwards so that the walk
    /// can take them in reverse.
    items: Vec<(InstOrEdit<E>, Option<usize>)>,

    /// Scratch space for the single locations one allocation is made of.
    scalars: Vec<ScalarAllocation<E>>,

    /// The current root's arrivals, from `Hoister::collect_terminator`: where
    /// its parameters arrive, when that is the gap a hoist would go in.
    arrivals: Vec<ScalarAllocation<E>>,

    /// What the current root's terminator reads.
    terminator_reads: Vec<ScalarAllocation<E>>,

    /// What the current root's terminator writes or clobbers.
    terminator_writes: Vec<ScalarAllocation<E>>,

    /// Blocks to commit, top-down, each with the range of `covered` holding
    /// the locations a hoist above it already filled.
    commit_stack: Vec<(Block<E>, u32, u32)>,

    /// The covers of every block on `commit_stack`.
    covered: Vec<ScalarAllocation<E>>,

    /// The edits to remove, sorted, by index into the edit list as move
    /// generation left it. See `crate::remove_eliminated_edits`.
    pub(crate) eliminated: Vec<usize>,

    /// The edits to insert, sorted by position.
    pub(crate) inserted: Vec<(PackedMovePosition<E>, Edit<E>)>,

    #[cfg(test)]
    pub(crate) test_stats: TestStats,
}

impl<E> DemandedMoves<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        Self {
            entry: SecondaryMap::new(None),
            entry_demands: PrimaryMap::new(),
            decided: SecondaryMap::new(None),
            decisions: PrimaryMap::new(),
            live: Vec::new(),
            meet: Vec::new(),
            items: Vec::new(),
            scalars: Vec::new(),
            arrivals: Vec::new(),
            terminator_reads: Vec::new(),
            terminator_writes: Vec::new(),
            commit_stack: Vec::new(),
            covered: Vec::new(),
            eliminated: Vec::new(),
            inserted: Vec::new(),
            #[cfg(test)]
            test_stats: TestStats::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            entry,
            entry_demands,
            decided,
            decisions,
            live,
            meet,
            items,
            scalars,
            arrivals,
            terminator_reads,
            terminator_writes,
            commit_stack,
            covered,
            eliminated,
            inserted,
            #[cfg(test)]
            test_stats,
        } = self;
        entry.reset();
        entry_demands.reset();
        decided.reset();
        decisions.reset();
        live.clear();
        meet.clear();
        items.clear();
        scalars.clear();
        arrivals.clear();
        terminator_reads.clear();
        terminator_writes.clear();
        commit_stack.clear();
        covered.clear();
        eliminated.clear();
        inserted.clear();
        #[cfg(test)]
        {
            *test_stats = TestStats::new();
        }
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            entry,
            entry_demands,
            decided,
            decisions,
            live,
            meet,
            items,
            scalars,
            arrivals,
            terminator_reads,
            terminator_writes,
            commit_stack,
            covered,
            eliminated,
            inserted,
            #[cfg(test)]
                test_stats: _,
        } = self;
        entry.is_reset()
            && entry_demands.is_reset()
            && decided.is_reset()
            && decisions.is_reset()
            && live.is_empty()
            && meet.is_empty()
            && items.is_empty()
            && scalars.is_empty()
            && arrivals.is_empty()
            && terminator_reads.is_empty()
            && terminator_writes.is_empty()
            && commit_stack.is_empty()
            && covered.is_empty()
            && eliminated.is_empty()
            && inserted.is_empty()
    }
}

impl<E> Default for DemandedMoves<E>
where
    E: EntityRepr,
{
    fn default() -> Self {
        Self::new()
    }
}

/// The analysis and the rewrite, and everything they read.
struct Hoister<'a, E, F>
where
    E: EntityRepr,
    F: InputFunction,
{
    input: &'a Input<'a, F>,
    output: &'a OutputInner<E>,
    move_generation: &'a MoveGeneration<E>,
    spill_slots: &'a SpillSlots<E>,
    rpo: &'a Rpo<E>,
    region_tree: &'a RegionTree<E>,
    recorded: &'a Recorded<E>,

    /// Redundant-move elimination's choices, sorted.
    redundant: &'a [usize],

    dead: &'a DeadMoveElimination<E>,
    counts: &'a mut Counts,
    events: &'a mut EventsLog<E>,
    me: &'a mut DemandedMoves<E>,
}

impl<E, F> Hoister<'_, E, F>
where
    E: EntityRepr,
    F: InputFunction,
{
    fn run(&mut self) {
        // Post-order: every extended-block child before the block it hangs off.
        for block in self.rpo.iter().rev() {
            let wide = block.with_repr32();
            let func = self.input.func;
            let is_child = {
                let input_block = func.block(wide);
                input_block.len_predecessors() == 1
                    && input_block.predecessors().next().is_some_and(|pred| {
                        self.rpo
                            .is_reachable(Block::<E>::try_new(pred.index()).unwrap())
                            && may_hoist_into(func, pred)
                    })
            };
            let is_root = self.recorded.before_terminator(block).is_some();
            if !is_child && !is_root {
                continue;
            }
            self.visit_block(block, is_child, is_root);
        }

        self.commit();
    }

    /// Does `loc` take part in the analysis at all?
    ///
    /// Redundant-move elimination knows nothing about a non-allocatable
    /// register, and an emergency slot holds nothing across a parallel-move
    /// sequence.
    fn is_tracked(&self, loc: ScalarAllocation<E>) -> bool {
        match loc {
            ScalarAllocation::Reg(reg) => reg.is_allocatable(self.input.machine),
            ScalarAllocation::Stack(slot) => !self.spill_slots.is_emergency(slot),
        }
    }

    /// Walk `block` backwards from the meet of its children's entry demands.
    ///
    /// A root decides, at its terminator, whether to hoist each demand there.
    /// An extended-block child goes on to its top and records its entry demands
    /// for its own parent.
    fn visit_block(&mut self, block: Block<E>, is_child: bool, is_root: bool) {
        let func = self.input.func;
        let wide = block.with_repr32();

        self.meet_successors(block, is_root);

        let mut items = core::mem::take(&mut self.me.items);
        items.clear();
        let mut iter = block_iter(self.move_generation, func, wide);
        while let Some(item) = iter.next_indexed() {
            items.push(item);
        }

        let terminator =
            Inst::<E>::try_new(crate::liveness::block_last_inst(&func.block(wide)).index())
                .unwrap();
        let mut reached_terminator = false;
        for &(item, index) in items.iter().rev() {
            match item {
                InstOrEdit::Inst(inst) => {
                    self.apply_inst(inst);
                    if inst == terminator {
                        reached_terminator = true;
                        if is_root {
                            self.decide(block);
                        }
                        if !is_child {
                            break;
                        }
                    }
                }
                InstOrEdit::Edit(Edit::CriticalEdge(_)) => {
                    debug_assert!(
                        !is_root,
                        "an extended-block child takes its edge's edits at its own top",
                    );
                    // On an edge out of a child, so towards a block outside the
                    // extended block.
                    self.me.live.clear();
                }
                InstOrEdit::Edit(edit) => {
                    debug_assert!(reached_terminator, "no edit follows a terminator");
                    let index = index.expect("`block_iter` numbers every edit it yields");
                    self.apply_edit(block, edit, index);
                }
            }
        }
        self.me.items = items;

        if is_child {
            let start = self.me.entry_demands.next_key_unwrap();
            for &demand in &self.me.live {
                self.me.entry_demands.push_unwrap(demand);
            }
            self.me.entry[block] = Some(self.me.entry_demands.range_from(start));
        }
        self.me.live.clear();
    }

    /// Start `live` at `block`'s bottom: the meet of its successors' entry
    /// demands for a root, and nothing otherwise.
    fn meet_successors(&mut self, block: Block<E>, is_root: bool) {
        self.me.live.clear();
        if !is_root {
            return;
        }

        let func = self.input.func;
        let mut first = true;
        for succ in func.block(block.with_repr32()).successors() {
            let succ = Block::<E>::try_new(succ.index()).unwrap();
            let Some(range) = self.me.entry[succ] else {
                // Unreachable, or never walked: nothing is known of it.
                self.me.live.clear();
                return;
            };
            let entry = self.me.entry_demands.range(range);
            if first {
                first = false;
                self.me.live.extend(entry.iter().map(|&(loc, demand)| {
                    (
                        loc,
                        Demand {
                            target: None,
                            ..demand
                        },
                    )
                }));
                continue;
            }

            // Keep a location only where both demand the same parts, and add
            // up what leaving it to the children costs.
            let mut meet = core::mem::take(&mut self.me.meet);
            meet.clear();
            let mut j = 0;
            for &(loc, demand) in &self.me.live {
                while j < entry.len() && entry[j].0 < loc {
                    j += 1;
                }
                if j < entry.len() && entry[j].0 == loc && self.same_parts(demand, entry[j].1) {
                    meet.push((
                        loc,
                        Demand {
                            parts_of: demand.parts_of,
                            cost: demand.cost + entry[j].1.cost,
                            target: None,
                        },
                    ));
                }
            }
            core::mem::swap(&mut self.me.live, &mut meet);
            self.me.meet = meet;
        }
    }

    fn parts_of(&self, demand: Demand) -> &[Part<E>] {
        self.recorded
            .written(demand.parts_of)
            .expect("a demand names an edit that is happening")
    }

    fn same_parts(&self, a: Demand, b: Demand) -> bool {
        self.parts_of(a) == self.parts_of(b)
    }

    /// Kill every demand on a location overlapping `loc`, except `loc` itself
    /// when `keep_exact` is set.
    fn kill_overlapping(&mut self, loc: ScalarAllocation<E>, keep_exact: bool) {
        let machine = self.input.machine;
        self.me.live.retain(|&(other, _)| {
            (keep_exact && other == loc) || !Interfere::interfere(machine, other, loc)
        });
    }

    /// Run one instruction backwards: everything it touches stops being
    /// demanded above it.
    fn apply_inst(&mut self, inst: Inst<E>) {
        if self.me.live.is_empty() {
            return;
        }

        let func = self.input.func;
        let machine = self.input.machine;
        let wide = inst.with_repr32();
        let input_inst = func.inst(wide);
        let allocs = self.output.inst_allocs(wide);

        let mut scalars = core::mem::take(&mut self.me.scalars);
        for &alloc in allocs {
            scalars_of(machine, self.spill_slots, alloc, &mut scalars);
            for &loc in &scalars {
                self.kill_overlapping(loc, false);
            }
        }
        self.me.scalars = scalars;

        for reg in input_inst.clobbers().iter() {
            let reg = Reg::<E>::try_new(reg.index()).unwrap();
            self.kill_overlapping(ScalarAllocation::Reg(reg), false);
        }
    }

    /// Is the edit at `index` not happening, by an earlier pass's choice?
    fn already_eliminated(&self, index: usize) -> bool {
        self.recorded.written(index).is_none() || self.dead.eliminated.binary_search(&index).is_ok()
    }

    /// Run one edit backwards: what it writes is now demanded, and what it
    /// reads is not.
    fn apply_edit(&mut self, block: Block<E>, edit: Edit<E>, index: usize) {
        debug_assert!(
            self.redundant.binary_search(&index).is_err() || self.already_eliminated(index),
            "redundant-move elimination records nothing for an edit it drops",
        );
        if self.already_eliminated(index) {
            return;
        }

        debug_assert!(
            !matches!(edit, Edit::CriticalEdge(_)),
            "handled by the caller"
        );
        let edit = edge_edit_at(self.move_generation, index);
        let (from, to) = match edit {
            EdgeEdit::Move(Move::RegReg { from, to }) => {
                (Some(ScalarAllocation::Reg(from)), ScalarAllocation::Reg(to))
            }
            EdgeEdit::Move(Move::Spill { from, to }) => (
                Some(ScalarAllocation::Reg(from)),
                ScalarAllocation::Stack(to),
            ),
            EdgeEdit::Move(Move::Reload { from, to }) => (
                Some(ScalarAllocation::Stack(from)),
                ScalarAllocation::Reg(to),
            ),
            EdgeEdit::Remat(remat) => (None, ScalarAllocation::Reg(remat.dest)),
        };

        // The write.
        self.kill_overlapping(to, true);
        let written = self
            .recorded
            .written(index)
            .expect("checked above that it is happening");
        if !written.is_empty() && self.is_tracked(to) {
            let demand = Demand {
                parts_of: index,
                cost: edit_cost(self.input, self.region_tree, block, edit),
                target: Some(index),
            };
            match self.me.live.binary_search_by_key(&to, |&(loc, _)| loc) {
                Ok(i) => self.me.live[i].1 = demand,
                Err(i) => self.me.live.insert(i, (to, demand)),
            }
        } else {
            self.me.live.retain(|&(loc, _)| loc != to);
        }

        // The read.
        if let Some(from) = from {
            self.kill_overlapping(from, false);
        }
    }

    /// At `block`'s terminator, with `live` holding the demands just before
    /// it, decide for each whether to hoist it here, and record the cheaper
    /// answer's cost as the demand's own, for `block`'s parent to weigh.
    fn decide(&mut self, block: Block<E>) {
        let facts = self
            .recorded
            .before_terminator(block)
            .expect("only a recorded block is a root");
        let start = self.me.decisions.next_key_unwrap();
        self.collect_terminator(block);

        for i in 0..self.me.live.len() {
            let (loc, demand) = self.me.live[i];
            // A root has no edits below its terminator: each successor has one
            // predecessor, so an edge's edits go atop the successor.
            debug_assert!(
                demand.target.is_none(),
                "every demand at a root's terminator comes from its children",
            );
            test_stat!(self.me, demands_at_roots);

            if self
                .me
                .arrivals
                .iter()
                .any(|&arrival| Interfere::interfere(self.input.machine, arrival, loc))
            {
                test_stat!(self.me, overwrites_an_arrival);
                continue;
            }

            let Some((source, cost)) = self.best_source(block, facts, loc, demand) else {
                test_stat!(self.me, no_source);
                continue;
            };
            if cost < demand.cost {
                self.me.live[i].1.cost = cost;
                self.me.decisions.push_unwrap(Decision {
                    loc,
                    source: Some(source),
                });
            } else {
                test_stat!(self.me, not_cheaper);
            }
        }

        self.me.decided[block] = Some(self.me.decisions.range_from(start));
    }

    /// Fill `arrivals`, `terminator_reads` and `terminator_writes` for the
    /// root `block`, once, for every demand `decide` weighs there.
    ///
    /// Arrivals are where `block`'s parameters arrive, when a move hoisted
    /// before its terminator would run before they do. That is a block whose
    /// terminator is its only instruction: the gap before the terminator is
    /// then the gap atop the block, and `Output::block_param_allocs` promises
    /// each parameter is in its location once every edit there has run. The
    /// checker holds it to that, which is why dead-move elimination keeps those
    /// locations live too.
    fn collect_terminator(&mut self, block: Block<E>) {
        let func = self.input.func;
        let machine = self.input.machine;
        let wide = block.with_repr32();
        let (first, terminator) = crate::liveness::block_inst_bounds(&func.block(wide));

        let mut scalars = core::mem::take(&mut self.me.scalars);
        let mut arrivals = core::mem::take(&mut self.me.arrivals);
        let mut reads = core::mem::take(&mut self.me.terminator_reads);
        let mut writes = core::mem::take(&mut self.me.terminator_writes);
        arrivals.clear();
        reads.clear();
        writes.clear();

        if first == terminator {
            for &alloc in self.output.block_param_allocs(wide).iter().flatten() {
                scalars_of(machine, self.spill_slots, alloc, &mut scalars);
                arrivals.extend_from_slice(&scalars);
            }
        }

        let input_inst = func.inst(terminator);
        for (op, &alloc) in input_inst
            .operands()
            .zip(self.output.inst_allocs(terminator))
        {
            scalars_of(machine, self.spill_slots, alloc, &mut scalars);
            match op.kind() {
                DefUse::Use => reads.extend_from_slice(&scalars),
                DefUse::Def => writes.extend_from_slice(&scalars),
            }
        }
        writes.extend(
            input_inst
                .clobbers()
                .iter()
                .map(|reg| ScalarAllocation::Reg(Reg::<E>::try_new(reg.index()).unwrap())),
        );

        self.me.scalars = scalars;
        self.me.arrivals = arrivals;
        self.me.terminator_reads = reads;
        self.me.terminator_writes = writes;
    }

    /// The cheapest location holding everything `demand` wants put in `loc`
    /// just before `block`'s terminator, and what moving it from there costs.
    fn best_source(
        &self,
        block: Block<E>,
        facts: &[Fact<E>],
        loc: ScalarAllocation<E>,
        demand: Demand,
    ) -> Option<(ScalarAllocation<E>, f64)> {
        let machine = self.input.machine;
        let wanted = self.parts_of(demand);
        debug_assert!(!wanted.is_empty());

        let mut best: Option<(ScalarAllocation<E>, f64)> = None;
        let mut i = 0;
        while i < facts.len() {
            let candidate = facts[i].0;
            let mut j = i;
            while j < facts.len() && facts[j].0 == candidate {
                j += 1;
            }
            let held = &facts[i..j];
            i = j;

            if Interfere::interfere(machine, candidate, loc) || !self.is_tracked(candidate) {
                continue;
            }

            // A location the children demand is overwritten before they read
            // it, so nothing guarantees it still holds anything, and another
            // hoist at this same point may be what overwrites it.
            if self
                .me
                .live
                .iter()
                .any(|&(other, _)| Interfere::interfere(machine, other, candidate))
            {
                continue;
            }

            // Everything `loc` must end up holding.
            let mut held_parts = held.iter().map(|&(_, part)| part).peekable();
            let holds_all = wanted.iter().all(|want| {
                while held_parts.next_if(|part| part < want).is_some() {}
                held_parts.next_if(|part| part == want).is_some()
            });
            if !holds_all {
                continue;
            }

            let Some(mv) = move_between(machine, self.spill_slots, candidate, loc) else {
                continue;
            };

            if !self.source_survives(block, candidate) {
                continue;
            }

            let cost = edit_cost(self.input, self.region_tree, block, EdgeEdit::Move(mv));
            if best.is_none_or(|(_, best)| cost < best) {
                best = Some((candidate, cost));
            }
        }
        best
    }

    /// Could dead-move elimination have dropped the write that filled `loc`?
    ///
    /// Redundant-move elimination thought `loc` held its parts just before
    /// `block`'s terminator, but it ran first: a write it saw may since have
    /// been called dead, when nothing read `loc` afterwards. Only a location
    /// live just before the terminator is sure to have been written. That is
    /// not the block's live-out set: a terminator that writes `loc` makes it
    /// live out with its own value. Reads `Hoister::collect_terminator`'s
    /// lists for `block`.
    fn source_survives(&self, block: Block<E>, loc: ScalarAllocation<E>) -> bool {
        let options = &self.input.options;
        if options.dead_move_elimination_level == MoveEliminationLevel::None {
            return true;
        }
        if matches!(loc, ScalarAllocation::Reg(_)) && !options.eliminate_dead_register_moves {
            return true;
        }

        // Only the `Global` fixpoint keeps live-out sets to ask.
        if options.dead_move_elimination_level != MoveEliminationLevel::Global {
            return false;
        }

        let machine = self.input.machine;
        let overlaps = |locs: &[ScalarAllocation<E>]| {
            locs.iter()
                .any(|&other| Interfere::interfere(machine, other, loc))
        };
        if overlaps(&self.me.terminator_reads) {
            return true;
        }
        if overlaps(&self.me.terminator_writes) {
            return false;
        }
        match loc {
            ScalarAllocation::Reg(reg) => self
                .dead
                .reg_may_be_live_out(self.input.machine, block, reg)
                .unwrap_or(false),
            ScalarAllocation::Stack(slot) => {
                self.dead.slot_may_be_live_out(block, slot).unwrap_or(false)
            }
        }
    }

    /// Carry out the decisions, top-down from each extended block's topmost
    /// root.
    ///
    /// Each block is committed with the locations a hoist above it already
    /// filled, its *cover*. A covered location's first write in a child is
    /// redundant and goes, and below it the location holds whatever that write
    /// would have left, so the cover ends there. A root hoists only what is not
    /// already covered.
    fn commit(&mut self) {
        for block in self.rpo.iter() {
            if self.me.decided[block].is_none() || self.me.entry[block].is_some() {
                continue;
            }

            debug_assert!(self.me.commit_stack.is_empty());
            debug_assert!(self.me.covered.is_empty());
            self.me.commit_stack.push((block, 0, 0));
            while let Some((block, start, end)) = self.me.commit_stack.pop() {
                self.commit_block(block, start, end);
            }
            self.me.covered.clear();
        }
    }

    /// Commit one block, whose cover is `covered[start..end]`, and queue its
    /// children with theirs.
    fn commit_block(&mut self, block: Block<E>, start: u32, end: u32) {
        let func = self.input.func;
        let wide = block.with_repr32();

        // This block's cover, as its own copy at the end of `covered`.
        let mine = u32::try_from(self.me.covered.len()).unwrap();
        self.me
            .covered
            .extend_from_within(start as usize..end as usize);

        // The covered writes atop a child go.
        if let Some(range) = self.me.entry[block] {
            let mut k = mine as usize;
            while k < self.me.covered.len() {
                let loc = self.me.covered[k];
                let entry = self.me.entry_demands.range(range);
                let demand = entry
                    .binary_search_by_key(&loc, |&(loc, _)| loc)
                    .map(|i| entry[i].1)
                    .expect("a hoist covers only what every child demands");
                match demand.target {
                    Some(index) => {
                        self.eliminate(index);
                        self.me.covered.swap_remove(k);
                    }
                    None => k += 1,
                }
            }
        }

        // A block that is not a root has nothing hanging off it in an extended
        // block.
        let Some(decided) = self.me.decided[block] else {
            self.me.covered.truncate(mine as usize);
            return;
        };

        // This block's own hoists, for what is not covered already.
        let terminator =
            Inst::<E>::try_new(crate::liveness::block_last_inst(&func.block(wide)).index())
                .unwrap();
        let covered_by_parent = self.me.covered.len();
        for k in decided {
            let Decision { loc, source } = self.me.decisions[k];
            let Some(source) = source else { continue };
            if self.me.covered[mine as usize..covered_by_parent].contains(&loc) {
                test_stat!(self.me, covered_from_above);
                continue;
            }
            self.hoist(terminator, loc, source);
            self.me.covered.push(loc);
        }

        let end = u32::try_from(self.me.covered.len()).unwrap();
        for succ in func.block(wide).successors() {
            let succ = Block::<E>::try_new(succ.index()).unwrap();
            debug_assert!(
                self.me.entry[succ].is_some(),
                "every child of a root was walked"
            );
            self.me.commit_stack.push((succ, mine, end));
        }
    }

    /// Insert `loc <- source` before `terminator`.
    fn hoist(
        &mut self,
        terminator: Inst<E>,
        loc: ScalarAllocation<E>,
        source: ScalarAllocation<E>,
    ) {
        let mv = move_between(self.input.machine, self.spill_slots, source, loc)
            .expect("`best_source` only picks a source a move can read");
        let pos = PackedMovePosition::point(crate::live_ranges::LivePoint::new(
            terminator,
            crate::input::Position::Early,
        ));

        match mv {
            Move::RegReg { .. } => test_stat!(self.me, hoisted_reg_reg),
            Move::Spill { .. } => test_stat!(self.me, hoisted_spills),
            Move::Reload { .. } => test_stat!(self.me, hoisted_reloads),
        }
        self.counts.moves_hoisted.inc();

        let index = self.move_generation.edits().len() + self.me.inserted.len();
        crate::trace!("hoisting {mv:?} to {pos:?}");
        event!(
            self.events,
            EditHoisted {
                pos,
                edit: EdgeEdit::Move(mv),
                index
            }
        );
        self.me.inserted.push((pos, Edit::Move(mv)));
    }

    /// Record that the edit at `index` is not going to happen.
    fn eliminate(&mut self, index: usize) {
        let (pos, _) = self.move_generation.edits()[index];
        let edit = edge_edit_at(self.move_generation, index);
        test_stat!(self.me, eliminated);
        self.counts.hoisted_edits_eliminated.inc();
        crate::trace!("dropping edit {index} at {pos:?}, now hoisted: {edit:?}");
        event!(self.events, HoistedEditEliminated { pos, edit, index });
        self.me.eliminated.push(index);
    }
}

/// What one run of the pass did, for test assertions.
#[cfg(test)]
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct TestStats {
    pub(crate) demands_at_roots: usize,
    pub(crate) no_source: usize,
    pub(crate) not_cheaper: usize,
    pub(crate) hoisted_reg_reg: usize,
    pub(crate) hoisted_spills: usize,
    pub(crate) hoisted_reloads: usize,
    pub(crate) eliminated: usize,
    pub(crate) covered_from_above: usize,
    pub(crate) overwrites_an_arrival: usize,
}

#[cfg(test)]
impl TestStats {
    const fn new() -> Self {
        Self {
            demands_at_roots: 0,
            no_source: 0,
            not_cheaper: 0,
            hoisted_reg_reg: 0,
            hoisted_spills: 0,
            hoisted_reloads: 0,
            eliminated: 0,
            covered_from_above: 0,
            overwrites_an_arrival: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Output,
        context::{Context, WhichContext},
        input::BlockFrequency,
        output::CriticalEdgeEdit,
        test::TestInput,
    };
    use core::sync::atomic::{AtomicUsize, Ordering};
    use mutatis::{
        check::{Check, CheckResult},
        mutators as m,
    };
    use std::{format, string::String, vec::Vec};

    /// What one allocation's results hold, and what the pass did on the way.
    struct Run {
        edits: Vec<(crate::Block, Edit)>,
        estimate: f64,
        stats: TestStats,
    }

    /// Allocate `test_input` with the pass on or off, and read the results as
    /// a client would.
    fn run_with(test_input: &TestInput, hoist: bool) -> Result<Option<Run>, String> {
        let mut test_input = test_input.clone();
        test_input.options.hoist_demanded_moves = hoist;

        let mut context = Context::new();
        let result = test_input.with_input(|input| -> Result<Option<Run>, String> {
            match crate::run_dispatch(&mut context, input) {
                Ok(()) => {}
                Err(crate::Error::TooManyLiveRegs) => return Ok(None),
                Err(e) => return Err(format!("allocation failed: {e:?}")),
            }
            let stats = match context.which.expect("`run_dispatch` chose a context") {
                #[cfg(feature = "entity-repr-8")]
                WhichContext::Context8 => context.context8.demanded_moves.test_stats.clone(),
                #[cfg(feature = "entity-repr-16")]
                WhichContext::Context16 => context.context16.demanded_moves.test_stats.clone(),
                WhichContext::Context32 => context.context32.demanded_moves.test_stats.clone(),
            };

            let output = Output::new(&context);
            crate::checker::check(input, &output).map_err(|e| format!("checker: {e:?}"))?;

            let mut edits = Vec::new();
            let mut estimate = 0.0;
            for (block, _) in input.func.blocks() {
                let weight = estimate_weight(input, &output, block);
                for item in output.block_insts_and_edits(input.func, block) {
                    if let InstOrEdit::Edit(edit) = item {
                        let edge = match edit {
                            Edit::Move(mv) => EdgeEdit::Move(mv),
                            Edit::Remat(remat) => EdgeEdit::Remat(remat),
                            Edit::CriticalEdge(CriticalEdgeEdit { edit, .. }) => edit,
                        };
                        estimate += weight
                            * match edge {
                                EdgeEdit::Move(Move::RegReg { .. }) | EdgeEdit::Remat(_) => 1.0,
                                EdgeEdit::Move(_) => 5.0,
                            };
                        edits.push((block, edit));
                    }
                }
            }
            Ok(Some(Run {
                edits,
                estimate,
                stats,
            }))
        });
        context.reset();
        assert!(context.is_reset(), "the pass's storage should reset");
        result
    }

    /// `Block::weight`, read through the public results, as the `run`
    /// example's estimated cycles read it.
    fn estimate_weight(
        input: &Input<'_, impl InputFunction>,
        output: &Output<'_>,
        block: crate::Block,
    ) -> f64 {
        let mut weight = input.func.block(block).frequency().estimate_weight();
        for _ in 0..output.loop_depth(block) {
            weight *= 10.0;
        }
        weight
    }

    /// The canonical frequencies weigh what the `run` example says they do.
    #[test]
    fn canonical_frequencies_weigh_as_estimated() {
        for (frequency, want) in [
            (BlockFrequency::COLD, 0.05),
            (BlockFrequency::NORMAL, 1.0),
            (BlockFrequency::HOT, 10.0),
        ] {
            let mut test_input = TestInput::with_a_value_reloaded_on_every_arm(2);
            test_input.set_block_frequencies(frequency);
            let mut context = Context::new();
            test_input.with_input(|input| {
                crate::run_dispatch(&mut context, input).unwrap();
                let weight = match context.which.unwrap() {
                    #[cfg(feature = "entity-repr-8")]
                    WhichContext::Context8 => Block::try_new(0)
                        .unwrap()
                        .weight(input, &context.context8.region_tree),
                    #[cfg(feature = "entity-repr-16")]
                    WhichContext::Context16 => Block::try_new(0)
                        .unwrap()
                        .weight(input, &context.context16.region_tree),
                    WhichContext::Context32 => Block::try_new(0)
                        .unwrap()
                        .weight(input, &context.context32.region_tree),
                };
                assert!((weight - want).abs() < 1e-6, "{frequency:?}: {weight}");
            });
            context.reset();
        }
    }

    #[test]
    fn reloads_on_every_arm_become_one() {
        for arms in [2, 3] {
            let test_input = TestInput::with_a_value_reloaded_on_every_arm(arms);
            let off = run_with(&test_input, false).unwrap().unwrap();
            let on = run_with(&test_input, true).unwrap().unwrap();

            let reloads = |run: &Run| {
                run.edits
                    .iter()
                    .filter(|(_, edit)| matches!(edit, Edit::Move(Move::Reload { .. })))
                    .count()
            };
            assert_eq!(reloads(&off), arms, "{:?}", off.edits);
            assert_eq!(reloads(&on), 1, "{:?}", on.edits);
            assert_eq!(on.stats.hoisted_reloads, 1);
            assert_eq!(on.stats.eliminated, arms);

            // And it lands in the block that forks.
            let entry = test_input.with_input(|input| input.func.entry_block());
            assert!(
                on.edits.iter().any(|&(block, edit)| block == entry
                    && matches!(edit, Edit::Move(Move::Reload { .. }))),
                "{:?}",
                on.edits,
            );
        }
    }

    /// Arms at different, non-canonical frequencies: the hoist is taken only
    /// when the estimate the `run` example reports agrees it is cheaper.
    #[test]
    fn mixed_frequency_arms_are_priced_as_estimated() {
        let block = |i| crate::Block::try_new(i).unwrap();
        for (one, two) in [
            (BlockFrequency::COLD, BlockFrequency::new(0.5)),
            (BlockFrequency::COLD, BlockFrequency::new(10.0)),
            (BlockFrequency::new(0.5), BlockFrequency::new(10.0)),
            (BlockFrequency::COLD, BlockFrequency::COLD),
        ] {
            let mut test_input = TestInput::with_a_value_reloaded_on_every_arm(2);
            test_input.set_block_frequency(block(1), one);
            test_input.set_block_frequency(block(2), two);
            let off = run_with(&test_input, false).unwrap().unwrap();
            let on = run_with(&test_input, true).unwrap().unwrap();
            assert!(
                on.estimate <= off.estimate,
                "{one:?}, {two:?}: {} > {}",
                on.estimate,
                off.estimate,
            );
        }
    }

    /// A move hoisted before the terminator of a block that is nothing but its
    /// terminator lands in the gap its parameters arrive in, so it must not
    /// write where one arrives.
    #[test]
    fn a_hoist_spares_where_a_parameter_arrives() {
        let test_input = TestInput::with_a_reload_demanded_where_a_parameter_arrives();
        let on = run_with(&test_input, true).unwrap().unwrap();
        assert!(on.stats.overwrites_an_arrival > 0, "{:?}", on.stats);

        // The arms' moves into `r0` stay where they are.
        let block3 = crate::Block::try_new(3).unwrap();
        assert!(
            !on.edits.iter().any(|&(block, edit)| block == block3
                && matches!(edit, Edit::Move(Move::RegReg { .. } | Move::Reload { .. }))),
            "{:?}",
            on.edits,
        );
    }

    /// A source must still hold its value just before the terminator, not
    /// just after it: here `r0` is live out of the root only because the
    /// terminator defines it, and the write that filled it before was dead.
    #[cfg(feature = "deserialize")]
    #[test]
    fn a_source_the_terminator_overwrites_is_not_used() {
        let input: crate::deserialize::DeserializedInput = serde_json::from_str(include_str!(
            "demanded_moves_tests/hoist-from-a-register-the-terminator-overwrites.json"
        ))
        .unwrap();
        assert!(input.options().hoist_demanded_moves);

        let input = input.as_input();
        let mut context = Context::new();
        let output = crate::run(&mut context, &input).unwrap();
        crate::checker::check(&input, &output).unwrap();
    }

    /// The pass changes nothing when it is off, and when it is on: the checker
    /// passes, the estimated cost never rises, and neither does the number of
    /// edits.
    #[test]
    fn hoisting_never_costs_more() -> CheckResult<TestInput> {
        static HOISTED: AtomicUsize = AtomicUsize::new(0);
        HOISTED.store(0, Ordering::Relaxed);

        let result = Check::new().iters(10_000).run_with(
            m::default::<TestInput>(),
            crate::test::corpus(),
            |test_input: &TestInput| -> Result<(), String> {
                let Some(off) = run_with(test_input, false)? else {
                    return Ok(());
                };
                let on = run_with(test_input, true)?
                    .ok_or_else(|| String::from("hoisting ran out of registers"))?;

                if off.stats != TestStats::new() {
                    return Err(format!("the pass ran while off: {:?}", off.stats));
                }
                HOISTED.fetch_add(on.stats.eliminated, Ordering::Relaxed);

                if on.edits.len() > off.edits.len() {
                    return Err(format!(
                        "hoisting added edits:\noff = {:?}\non  = {:?}",
                        off.edits, on.edits,
                    ));
                }
                if !(on.estimate.is_finite() && off.estimate.is_finite()) {
                    return Err(format!(
                        "a non-finite estimate: {} and {}",
                        off.estimate, on.estimate
                    ));
                }
                // Relative, since a deep loop weighs `10^depth`.
                if on.estimate > off.estimate * (1.0 + 1e-12) {
                    return Err(format!(
                        "hoisting raised the estimate from {} to {}:\noff = {:?}\non  = {:?}",
                        off.estimate, on.estimate, off.edits, on.edits,
                    ));
                }
                if on.stats.eliminated == 0 && on.edits != off.edits {
                    return Err(String::from("nothing was hoisted, but the edits changed"));
                }
                Ok(())
            },
        );

        if result.is_ok() {
            assert!(
                HOISTED.load(Ordering::Relaxed) > 0,
                "nothing was ever hoisted, so this check says nothing",
            );
        }
        result
    }

    /// The checker passes with the pass on under every combination of the
    /// other options, which the mutator picks at random.
    #[test]
    fn hoisting_passes_the_checker() -> CheckResult<TestInput> {
        Check::new().iters(10_000).run_with(
            m::default::<TestInput>(),
            crate::test::corpus(),
            |test_input: &TestInput| -> Result<(), String> {
                let mut test_input = test_input.clone();
                test_input.options.hoist_demanded_moves = true;
                crate::test::check_allocation(&test_input)
            },
        )
    }
}
