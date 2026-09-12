//! Test utilities.

#![allow(missing_docs, reason = "internal test utilities")]

mod parallel_moves;

pub use parallel_moves::*;

use crate::{
    Block, InputBlock, InputFunction, InputInst, InputValue, Machine, MachineBuilder, Operand, Reg,
    RegClass, RegGroup, RegUnit, Val,
    dfs::{Dfs, DfsEvent},
    dominators::DominatorTree,
    entity::{Entity, EntityRepr, Inst, PrimaryMap, Region, Scc, SccBlockIndex, SecondaryMap},
    input::{
        BlockFrequency, DefUse, Input, InputOptions, MoveEliminationLevel, OperandConstraint,
        Position, RematCost,
    },
    live_ranges::{LiveBundle, LiveSpan, MAX_OPERANDS_PER_INST},
    output::OutputInner,
    spill_slot_allocation::{SpillSlot, SpillSlotSize},
    union_find::UnionFind,
};
use alloc::{vec, vec::Vec};
use core::{
    fmt::{self, Display},
    marker::PhantomData,
    mem, slice,
};
use mutatis::{DefaultMutate, Generate, Mutate};
use std::collections::{BTreeSet, HashMap, hash_map::Entry};

pub struct EntityMutator<E>(PhantomData<E>);

impl<E> Default for EntityMutator<E> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

impl<E> Mutate<E> for EntityMutator<E>
where
    E: Entity,
{
    fn mutate(
        &mut self,
        mutations: &mut mutatis::Candidates<'_>,
        value: &mut E,
    ) -> mutatis::Result<()> {
        mutations.mutation(|ctx| {
            if ctx.shrink() {
                let old_index = value.index();
                if old_index == 0 {
                    Err(mutatis::error::Error::exhausted())
                } else {
                    let new_index = ctx.rng().gen_usize();
                    *value = E::try_new(new_index % old_index).unwrap();
                    Ok(())
                }
            } else {
                *value = self.generate(ctx)?;
                Ok(())
            }
        })
    }
}

impl<E> Generate<E> for EntityMutator<E>
where
    E: Entity,
{
    fn generate(&mut self, ctx: &mut mutatis::Context) -> mutatis::Result<E> {
        let new_index = ctx.rng().gen_usize();
        let max = E::MAX_REPRESENTABLE.index();
        let value = E::try_new(new_index % max).unwrap();
        Ok(value)
    }
}

macro_rules! entity_default_mutate {
    ( $( $name:ident )* ) => {
        $(
            impl<E> DefaultMutate for $name<E>
            where
                E: EntityRepr,
            {
                type DefaultMutate = EntityMutator<Self>;
            }
        )*
    };
}

entity_default_mutate! {
    Val
    Inst
    Block
    Scc
    SccBlockIndex
    Region
    Reg
    SpillSlot
    LiveSpan
    LiveBundle
}

/// A mutator for [`Operand`].
pub struct OperandMutator<E>(PhantomData<E>);

impl<E> Default for OperandMutator<E> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

/// Generate a constraint that the packed `Operand` encoding can represent.
fn gen_operand_constraint(ctx: &mut mutatis::Context) -> mutatis::Result<OperandConstraint> {
    Ok(match ctx.rng().gen_index(4).unwrap() {
        0 => OperandConstraint::Any,
        1 => {
            let index = ctx
                .rng()
                .gen_index(RegClass::MAX_INCLUDING_DERIVED)
                .unwrap();
            OperandConstraint::Reg(RegClass::try_new(index).unwrap())
        }
        2 => OperandConstraint::Stack,
        _ => {
            let index = ctx.rng().gen_index(MAX_OPERANDS_PER_INST).unwrap();
            OperandConstraint::Reuse(index)
        }
    })
}

/// Generate a level of redundant-move elimination.
fn gen_move_elimination_level(ctx: &mut mutatis::Context) -> mutatis::Result<MoveEliminationLevel> {
    Ok(match ctx.rng().gen_index(3).unwrap() {
        0 => MoveEliminationLevel::None,
        1 => MoveEliminationLevel::Local,
        _ => MoveEliminationLevel::Global,
    })
}

impl<E> Mutate<Operand<E>> for OperandMutator<E>
where
    E: EntityRepr,
{
    fn mutate(
        &mut self,
        mutations: &mut mutatis::Candidates<'_>,
        operand: &mut Operand<E>,
    ) -> mutatis::Result<()> {
        mutations.mutation(|ctx| {
            let val = if ctx.shrink() {
                let old_index = operand.val().index();
                if old_index == 0 {
                    return Err(mutatis::error::Error::exhausted());
                }
                Val::<E>::try_new(ctx.rng().gen_usize() % old_index).unwrap()
            } else {
                EntityMutator::<Val<E>>::default().generate(ctx)?
            };
            *operand = Operand::new(operand.pos(), operand.kind(), operand.constraint(), val);
            Ok(())
        })?;

        mutations.mutation(|_ctx| {
            let pos = match operand.pos() {
                Position::Early => Position::Late,
                Position::Late => Position::Early,
            };
            *operand = Operand::new(pos, operand.kind(), operand.constraint(), operand.val());
            Ok(())
        })?;

        mutations.mutation(|_ctx| {
            let kind = match operand.kind() {
                DefUse::Def => DefUse::Use,
                DefUse::Use => DefUse::Def,
            };
            *operand = Operand::new(operand.pos(), kind, operand.constraint(), operand.val());
            Ok(())
        })?;

        // There is no order on constraints to shrink along, so this mutation
        // simply does not apply when we are shrinking.
        if !mutations.shrink() {
            mutations.mutation(|ctx| {
                let constraint = gen_operand_constraint(ctx)?;
                *operand = Operand::new(operand.pos(), operand.kind(), constraint, operand.val());
                Ok(())
            })?;
        }

        Ok(())
    }
}

impl<E> Generate<Operand<E>> for OperandMutator<E>
where
    E: EntityRepr,
{
    fn generate(&mut self, ctx: &mut mutatis::Context) -> mutatis::Result<Operand<E>> {
        let pos = if ctx.rng().gen_bool() {
            Position::Early
        } else {
            Position::Late
        };
        let kind = if ctx.rng().gen_bool() {
            DefUse::Def
        } else {
            DefUse::Use
        };
        let constraint = gen_operand_constraint(ctx)?;
        let val = EntityMutator::<Val<E>>::default().generate(ctx)?;
        Ok(Operand::new(pos, kind, constraint, val))
    }
}

impl<E> DefaultMutate for Operand<E>
where
    E: EntityRepr,
{
    type DefaultMutate = OperandMutator<E>;
}

#[derive(Clone, Default, Debug, Hash, Mutate)]
pub struct BlockCall {
    target: Block,
    args: Vec<Val>,
}

#[derive(Clone, Debug, Hash, Mutate)]
pub enum InstData {
    Op {
        operands: Vec<Operand>,
        side_effects: bool,
    },
    Branch {
        operands: Vec<Operand>,
        targets: Vec<BlockCall>,
    },
}

impl Default for InstData {
    fn default() -> Self {
        Self::Op {
            operands: vec![],
            side_effects: false,
        }
    }
}

impl InstData {
    /// This instruction's operands.
    fn operands(&self) -> &[Operand] {
        match self {
            InstData::Op { operands, .. } | InstData::Branch { operands, .. } => operands,
        }
    }

    /// Get mutable access to this instruction's operands.
    fn operands_mut(&mut self) -> &mut [Operand] {
        match self {
            InstData::Op { operands, .. } | InstData::Branch { operands, .. } => operands,
        }
    }

    /// This instruction's block calls: the control-flow edges it takes, and the
    /// arguments passed along each of them.
    fn block_calls(&self) -> &[BlockCall] {
        match self {
            InstData::Op { .. } => &[],
            InstData::Branch { targets, .. } => targets,
        }
    }

    /// Get mutable access to this instruction's block calls.
    fn block_calls_mut(&mut self) -> &mut [BlockCall] {
        match self {
            InstData::Op { .. } => &mut [],
            InstData::Branch { targets, .. } => targets,
        }
    }

    /// This instruction's block-call list itself, mutably, so that outgoing
    /// edges can be added and removed.
    #[cfg(test)]
    fn block_call_list_mut(&mut self) -> Option<&mut Vec<BlockCall>> {
        match self {
            InstData::Op { .. } => None,
            InstData::Branch { targets, .. } => Some(targets),
        }
    }

    /// This instruction's operand list itself, mutably, so that operands can
    /// be added and removed.
    #[cfg(test)]
    fn operand_list_mut(&mut self) -> &mut Vec<Operand> {
        match self {
            InstData::Op { operands, .. } | InstData::Branch { operands, .. } => operands,
        }
    }
}

/// The most register classes any `TestMachine` can define, and so the range a
/// `TestFunction`'s value classes are reduced to before `TestInput::fixup`
/// narrows them further to one particular machine's classes.
const MAX_REG_CLASSES: usize = TestMachine::MAX_BANKS * TestMachine::MAX_CLASSES_PER_BANK;

#[derive(Clone, Default, Debug, Hash, Mutate)]
pub struct ValData {
    /// An index into the machine's register classes, narrowed to a class the
    /// machine really defines by `TestInput::fixup`.
    reg_class: u8,
    def: ValDef,

    /// An index into [`REMAT_COSTS`].
    remat: u8,
}

/// The rematerialization costs that a `TestFunction`'s values may take, indexed
/// by `ValData::remat`.
///
/// `None` comes first so that a default, unmutated value is not
/// rematerializable, which is the common case in a real function.
const REMAT_COSTS: [Option<RematCost>; 4] = [
    None,
    Some(RematCost::AlwaysRemat),
    Some(RematCost::CheaperThanMove),
    Some(RematCost::CheaperThanReload),
];

/// Where a value is defined.
#[derive(Clone, Debug, Hash, PartialEq, Eq, Mutate)]
pub enum ValDef {
    /// The value is defined by an instruction, as its `i`th definition.
    InstResult { inst: Inst, i: usize },

    /// The value is `block`'s `i`th parameter.
    BlockParam { block: Block, i: usize },
}

impl Default for ValDef {
    fn default() -> Self {
        ValDef::BlockParam {
            block: Block::try_new(0).unwrap(),
            i: 0,
        }
    }
}

#[derive(Clone, Default, Debug, Hash, Mutate)]
pub struct BlockData {
    pub params: Vec<Val>,
    pub insts: Vec<Inst>,
    pub frequency: u8,
}

/// The block frequencies that a `TestFunction`'s blocks may take, indexed by
/// `BlockData::frequency`.
///
/// `NORMAL` comes first so that a default, unmutated block is neither hot nor
/// cold.
const BLOCK_FREQUENCIES: [BlockFrequency; 6] = [
    BlockFrequency::NORMAL,
    BlockFrequency::COLD,
    BlockFrequency::new(0.5),
    BlockFrequency::new(10.0),
    BlockFrequency::HOT,
    BlockFrequency::new(10_000.0),
];

#[derive(Clone, Hash)]
pub struct TestFunction {
    mutated: bool,
    values: PrimaryMap<Val, ValData>,
    blocks: PrimaryMap<Block, BlockData>,
    insts: PrimaryMap<Inst, InstData>,
    predecessors: SecondaryMap<Block, Vec<Block>>,
    inst_blocks: SecondaryMap<Inst, Option<Block>>,
    dominators: DominatorTree,
}

impl Default for TestFunction {
    fn default() -> Self {
        let mut func = TestFunction {
            mutated: false,
            values: PrimaryMap::default(),
            blocks: PrimaryMap::default(),
            insts: PrimaryMap::default(),
            predecessors: SecondaryMap::new(Vec::new()),
            inst_blocks: SecondaryMap::new(None),
            dominators: DominatorTree::default(),
        };
        func.fixup();
        func
    }
}

#[derive(Default)]
pub struct TestFunctionMutator {}

impl Mutate<TestFunction> for TestFunctionMutator {
    fn mutate(
        &mut self,
        mutations: &mut mutatis::Candidates<'_>,
        func: &mut TestFunction,
    ) -> mutatis::Result<()> {
        let result = (|| -> mutatis::Result<()> {
            <PrimaryMap<Val, ValData> as DefaultMutate>::DefaultMutate::default()
                .mutate(mutations, &mut func.values)?;
            <PrimaryMap<Block, BlockData> as DefaultMutate>::DefaultMutate::default()
                .mutate(mutations, &mut func.blocks)?;
            <PrimaryMap<Inst, InstData> as DefaultMutate>::DefaultMutate::default()
                .mutate(mutations, &mut func.insts)?;
            Ok(())
        })();

        if func.mutated {
            func.fixup();
            func.mutated = false;
        } else {
            func.mutated = true;
        }

        result
    }
}

#[cfg(test)]
fn hash<T>(value: &T) -> u64
where
    T: core::hash::Hash,
{
    use core::hash::Hasher;
    let mut hasher = std::hash::DefaultHasher::new();
    <T as core::hash::Hash>::hash(value, &mut hasher);
    hasher.finish()
}

impl Generate<TestFunction> for TestFunctionMutator {
    fn generate(&mut self, context: &mut mutatis::Context) -> mutatis::Result<TestFunction> {
        let mut func = TestFunction {
            mutated: false,
            values: <PrimaryMap<Val, ValData> as DefaultMutate>::DefaultMutate::default()
                .generate(context)?,
            blocks: <PrimaryMap<Block, BlockData> as DefaultMutate>::DefaultMutate::default()
                .generate(context)?,
            insts: <PrimaryMap<Inst, InstData> as DefaultMutate>::DefaultMutate::default()
                .generate(context)?,
            predecessors: SecondaryMap::new(Vec::new()),
            inst_blocks: SecondaryMap::new(None),
            dominators: DominatorTree::default(),
        };
        func.fixup();
        Ok(func)
    }
}

impl DefaultMutate for TestFunction {
    type DefaultMutate = TestFunctionMutator;
}

impl fmt::Debug for TestFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            f.debug_struct("TestFunction")
                .field("values", &self.values)
                .field("blocks", &self.blocks)
                .field("insts", &self.insts)
                .finish()
        } else {
            self.display().fmt(f)
        }
    }
}

impl TestFunction {
    /// Get this function's dominator tree, which [`TestFunction::fixup`] keeps
    /// up to date.
    #[cfg(test)]
    pub(crate) fn dominators(&self) -> &DominatorTree {
        &self.dominators
    }

    /// One of an instruction's operands, mutably, without repairing the
    /// function afterwards.
    #[cfg(test)]
    pub(crate) fn operand_mut(&mut self, inst: Inst, operand: usize) -> &mut Operand {
        &mut self.insts[inst].operands_mut()[operand]
    }

    /// An instruction's whole operand list, mutably, so that a test can change
    /// its length without repairing the function.
    #[cfg(test)]
    pub(crate) fn operands_mut(&mut self, inst: Inst) -> &mut Vec<Operand> {
        self.insts[inst].operand_list_mut()
    }

    /// Give `block` another parameter, without repairing the function.
    ///
    /// The results side cannot grow to match --- `block_param_allocs_mut`
    /// hands back a slice --- so this is the only way to make a block's
    /// parameters and its parameter allocations disagree.
    #[cfg(test)]
    pub(crate) fn push_block_param(&mut self, block: Block, val: Val) {
        self.blocks[block].params.push(val);
    }

    /// Move `val` into the machine's `reg_class`th class, the numbering
    /// [`TestMachine::BOTH_REGS_CLASS`] uses, without repairing the function.
    #[cfg(test)]
    pub(crate) fn set_reg_class(&mut self, val: Val, reg_class: u8) {
        self.values[val].reg_class = reg_class;
    }

    /// Point one of a branch's edges at a different block, without repair.
    #[cfg(test)]
    pub(crate) fn set_block_call_target(&mut self, inst: Inst, call: usize, target: Block) {
        self.insts[inst].block_calls_mut()[call].target = target;
    }

    /// Give a branch a second copy of one of its outgoing edges, so that the
    /// block has more successors than before without changing where any of
    /// them go or what they carry. Without repair.
    #[cfg(test)]
    pub(crate) fn duplicate_block_call(&mut self, inst: Inst, call: usize) {
        let calls = self.insts[inst]
            .block_call_list_mut()
            .expect("only a branch has outgoing edges");
        let call = calls[call].clone();
        calls.push(call);
    }

    /// Repair this function until it is well formed: a terminated,
    /// fully-reachable control-flow graph in valid SSA form.
    ///
    /// Every pass below is idempotent, and none of the value-level passes
    /// changes the control-flow graph, so the dominator tree computed in the
    /// middle stays valid for the passes that follow it.
    pub fn fixup(&mut self) {
        let mut output = OutputInner::<u32>::new();
        self.ensure_non_empty(&mut output);
        self.ensure_unique_insts_in_layout(&mut output);
        self.ensure_terminators();
        self.ensure_all_blocks_are_reachable(&mut output);
        self.fixup_predecessors();
        self.fixup_dominator_tree();
        self.ensure_entry_param_when_needed();
        self.ensure_unique_defs(&mut output);
        self.ensure_block_call_arity();
        self.ensure_uses_dominated_by_defs();
        self.ensure_operand_constraints();
        self.ensure_reg_classes_agree();
    }

    /// Make sure that this function has at least one block, instruction, and
    /// value, and that no block has an empty layout.
    fn ensure_non_empty(&mut self, output: &mut OutputInner<u32>) {
        if self.blocks.is_empty() {
            self.blocks
                .push(
                    output,
                    BlockData {
                        params: vec![],
                        insts: vec![],
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        if self.insts.is_empty() {
            self.insts
                .push(
                    output,
                    InstData::Op {
                        operands: vec![Operand::new(
                            Position::Early,
                            DefUse::Def,
                            OperandConstraint::Any,
                            Val::try_new(0).unwrap(),
                        )],
                        side_effects: true,
                    },
                )
                .unwrap();
        }

        if self.values.is_empty() {
            self.values
                .push(
                    output,
                    ValData {
                        reg_class: 0,
                        def: ValDef::InstResult {
                            inst: Inst::try_new(0).unwrap(),
                            i: 0,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        // `ensure_unique_insts_in_layout` gives each of these its own copy of
        // the instruction data and its own `Inst`.
        for (_block, block_data) in self.blocks.iter_mut() {
            if block_data.insts.is_empty() {
                block_data.insts.push(Inst::try_new(0).unwrap());
            }
        }
    }

    /// Make sure each instruction appears in the layout exactly once, cloning
    /// instructions as needed, and dropping instructions that aren't in the
    /// layout.
    ///
    /// Returns a map from old `Inst`s to new `Inst`s and the old `PrimaryMap`
    /// of `Inst`s.
    fn ensure_unique_insts_in_layout(
        &mut self,
        output: &mut OutputInner<u32>,
    ) -> (HashMap<Inst, Inst>, PrimaryMap<Inst, InstData>) {
        let mut new_insts = PrimaryMap::<Inst, InstData>::new();
        new_insts.reserve(self.blocks.iter().map(|(_, b)| b.insts.len()).sum());

        let mut old_to_new = HashMap::<Inst, Inst>::new();

        // Ensure `self.insts` isn't empty so that the `%` below never panics.
        if self.insts.is_empty() {
            self.insts.push(output, InstData::default()).unwrap();
        }

        for (block, block_data) in self.blocks.iter_mut() {
            for inst in &mut block_data.insts {
                let clamped_inst = Inst::<u32>::try_new(inst.index() % self.insts.len()).unwrap();
                let cloned_inst = self.insts[clamped_inst].clone();
                let new_inst = new_insts.push(output, cloned_inst).unwrap();
                match old_to_new.entry(*inst) {
                    Entry::Occupied(_) => {}
                    Entry::Vacant(e) => {
                        e.insert(new_inst);
                    }
                };
                *inst = new_inst;
                self.inst_blocks[new_inst] = Some(block);
            }
        }

        let old_insts = mem::replace(&mut self.insts, new_insts);
        (old_to_new, old_insts)
    }

    /// Make sure that every block ends in a terminator instruction, and that
    /// they name valid blocks as their successors.
    fn ensure_terminators(&mut self) {
        let num_blocks = self.blocks.len();
        assert!(num_blocks > 0);

        for (_block, block_data) in self.blocks.iter_mut() {
            let (&terminator, rest) = block_data
                .insts
                .split_last()
                .expect("`ensure_non_empty` gives every block an instruction");

            // Only the last instruction in a block can be a terminator.
            for inst in rest {
                if let InstData::Branch {
                    operands,
                    targets: _,
                } = &mut self.insts[*inst]
                {
                    let operands = mem::take(operands);
                    self.insts[*inst] = InstData::Op {
                        operands,
                        side_effects: false,
                    };
                }
            }

            match &mut self.insts[terminator] {
                InstData::Op { operands, .. } => {
                    let operands = mem::take(operands);
                    self.insts[terminator] = InstData::Branch {
                        operands,
                        targets: vec![],
                    };
                }
                InstData::Branch {
                    operands: _,
                    targets,
                } => {
                    for target in targets {
                        target.target = Block::try_new(target.target.index() % num_blocks).unwrap();
                    }
                }
            }
        }
    }

    fn ensure_all_blocks_are_reachable(&mut self, output: &mut OutputInner<u32>) {
        let mut dfs = Dfs::new();
        dfs.construct(self, output).unwrap();

        let mut seen = BTreeSet::new();
        while let Some(event) = dfs.next(self, output, |b| seen.contains(&b)).unwrap() {
            match event {
                DfsEvent::Pre(block) => {
                    seen.insert(block);
                }
                DfsEvent::AfterEdge(..) | DfsEvent::Post(_) => {}
            }
        }

        let seen_vec: Vec<_> = seen.iter().copied().collect();

        for block in self.blocks.keys() {
            if seen.contains(&block) {
                continue;
            }
            let from = seen_vec[block.index() % seen_vec.len()];
            let from_inst = self.blocks[from].insts.last().copied().unwrap();
            match &mut self.insts[from_inst] {
                InstData::Op { .. } => unreachable!(),
                InstData::Branch {
                    operands: _,
                    targets,
                } => {
                    targets.push(BlockCall {
                        target: block,
                        args: vec![],
                    });
                }
            }
        }
    }

    /// Rebuild the control-flow graph's predecessors.
    fn fixup_predecessors(&mut self) {
        // Empty every entry rather than resetting the map, which would drop the
        // vectors and their allocations. Cover both the blocks that exist now
        // and any entries left over from when the function had more of them.
        let len = self.predecessors.len().max(self.blocks.len());
        for i in 0..len {
            self.predecessors[Block::try_new(i).unwrap()].clear();
        }

        let Self {
            blocks,
            insts,
            predecessors,
            ..
        } = self;
        for (block, block_data) in blocks.iter() {
            let terminator = *block_data.insts.last().unwrap();
            // These are the same block calls that `successors` reads, so the
            // two cannot disagree about what the edges are. One entry per edge,
            // so a block that branches to the same target twice appears twice
            // in that target's predecessors.
            for call in insts[terminator].block_calls() {
                predecessors[call.target].push(block);
            }
        }
    }

    fn fixup_dominator_tree(&mut self) {
        let mut dominators = mem::take(&mut self.dominators);
        dominators.compute(self);
        self.dominators = dominators;
    }

    /// Give the entry block a parameter if this function has any use that would
    /// otherwise have no value in scope.
    fn ensure_entry_param_when_needed(&mut self) {
        let entry = self.entry_block();
        let mut needs_param = false;
        let mut scope_len = 0;
        let mut stack = vec![ScopeFrame::Enter(entry)];

        'walk: while let Some(frame) = stack.pop() {
            let block = match frame {
                ScopeFrame::Restore(len) => {
                    scope_len = len;
                    continue;
                }
                ScopeFrame::Enter(block) => block,
            };

            stack.push(ScopeFrame::Restore(scope_len));
            scope_len += self.blocks[block].params.len();

            for inst in &self.blocks[block].insts {
                let inst_data = &self.insts[*inst];

                // The block calls' arguments count as uses, because
                // `ensure_block_call_arity` is about to give each of them one
                // argument per parameter of its target block.
                let uses = inst_data
                    .operands()
                    .iter()
                    .filter(|op| op.kind() == DefUse::Use)
                    .count()
                    + inst_data
                        .block_calls()
                        .iter()
                        .map(|call| self.blocks[call.target].params.len())
                        .sum::<usize>();
                if scope_len == 0 && uses > 0 {
                    needs_param = true;
                    break 'walk;
                }

                scope_len += inst_data
                    .operands()
                    .iter()
                    .filter(|op| op.kind() == DefUse::Def)
                    .count();
            }

            stack.extend(block.dom_children(&self.dominators).map(ScopeFrame::Enter));
        }

        if needs_param {
            // `ensure_unique_defs` mints this parameter's real value in a
            // moment, along with every other definition.
            self.blocks[entry].params.push(Val::default());
        }
    }

    /// Rebuild `self.values` from the definition sites in the layout, so that
    /// every value is defined exactly once and its [`ValData::def`] says where.
    ///
    /// A definition site and the `ValData::def` that describes it are
    /// redundant, and mutation can make them disagree. Rather than reconcile
    /// them, this discards the old value map and mints a fresh value at each
    /// definition site, in layout order, which makes both invariants true by
    /// construction.
    fn ensure_unique_defs(&mut self, output: &mut OutputInner<u32>) {
        let old_values = mem::take(&mut self.values);
        let num_old_values = old_values.len();
        assert!(num_old_values > 0, "`ensure_non_empty` runs first");

        // Mint a fresh value for a definition site, keeping the register class of
        // whichever old value used to be named there so that mutating a value's
        // class still means something.
        let mut fresh_val = |values: &mut PrimaryMap<Val, ValData>, old: Val, def: ValDef| -> Val {
            let old = Val::try_new(old.index() % num_old_values).unwrap();
            let reg_class = old_values[old].reg_class;
            let remat = old_values[old].remat;
            values
                .push(
                    output,
                    ValData {
                        reg_class,
                        def,
                        remat,
                    },
                )
                .unwrap()
        };

        let Self {
            values,
            blocks,
            insts,
            ..
        } = self;

        for (block, block_data) in blocks.iter_mut() {
            for (i, param) in block_data.params.iter_mut().enumerate() {
                *param = fresh_val(values, *param, ValDef::BlockParam { block, i });
            }

            for inst in &block_data.insts {
                let inst = *inst;
                let mut i = 0;
                for op in insts[inst].operands_mut() {
                    if op.kind() == DefUse::Def {
                        op.set_val(fresh_val(values, op.val(), ValDef::InstResult { inst, i }));
                        i += 1;
                    }
                }
            }
        }
    }

    /// Make every block call pass exactly as many arguments as its target block
    /// has parameters.
    fn ensure_block_call_arity(&mut self) {
        let Self { blocks, insts, .. } = self;
        for (_block, block_data) in blocks.iter() {
            for inst in &block_data.insts {
                for call in insts[*inst].block_calls_mut() {
                    let arity = blocks[call.target].params.len();
                    call.args.resize(arity, Val::default());
                }
            }
        }
    }

    /// Put every `Reuse` into the only shape the allocator accepts: on a late
    /// definition, naming an early use of the same instruction alone.
    ///
    /// A definition carrying one moves to [`Position::Late`]; a use carrying
    /// one loses it, since making it a definition would give its value two.
    fn ensure_operand_constraints(&mut self) {
        let Self { insts, .. } = self;
        let mut reusable = Vec::new();

        for (_inst, inst_data) in insts.iter_mut() {
            let operands = inst_data.operands_mut();

            reusable.clear();
            reusable.extend(operands.iter().enumerate().filter_map(|(i, op)| {
                let ok = op.kind() == DefUse::Use
                    && op.pos() == Position::Early
                    && op.constraint() != OperandConstraint::Stack;
                ok.then_some(i)
            }));

            for i in 0..operands.len() {
                let op = operands[i];
                let OperandConstraint::Reuse(target) = op.constraint() else {
                    continue;
                };

                let claim = if op.kind() != DefUse::Def {
                    None
                } else if let Some(j) = reusable.iter().position(|&r| r == target) {
                    Some(reusable.remove(j))
                } else if reusable.is_empty() {
                    None
                } else {
                    Some(reusable.remove(target % reusable.len()))
                };

                let constraint = match claim {
                    Some(target) => OperandConstraint::Reuse(target),
                    None => OperandConstraint::Any,
                };

                let pos = match constraint {
                    OperandConstraint::Reuse(_) => Position::Late,
                    _ => op.pos(),
                };

                operands[i] = Operand::new(pos, op.kind(), constraint, op.val());
            }
        }
    }

    /// Make the values that this function pins to a single location agree about
    /// which register class they belong to.
    fn ensure_reg_classes_agree(&mut self) {
        let Self {
            values,
            blocks,
            insts,
            ..
        } = self;

        let mut sets = UnionFind::<Val>::new();

        for (_block, block_data) in blocks.iter() {
            for inst in &block_data.insts {
                let inst_data = &insts[*inst];

                // Block-call arguments and block params must agree.
                for call in inst_data.block_calls() {
                    for (arg, param) in call.args.iter().zip(&blocks[call.target].params) {
                        sets.union(*arg, *param);
                    }
                }

                // Reuse operands must agree.
                let operands = inst_data.operands();
                for op in operands {
                    let OperandConstraint::Reuse(i) = op.constraint() else {
                        continue;
                    };
                    sets.union(op.val(), operands[i].val());
                }
            }
        }

        let max_reg_classes = u8::try_from(MAX_REG_CLASSES).unwrap();
        for i in 0..values.len() {
            let val = Val::try_new(i).unwrap();
            let root = sets.find(val);
            debug_assert!(root.index() < values.len());
            let reg_class = values[root].reg_class % max_reg_classes;
            values[val].reg_class = reg_class;
        }
    }

    /// Rewrite every use whose value is not defined by a definition that
    /// dominates it.
    fn ensure_uses_dominated_by_defs(&mut self) {
        let entry = self.entry_block();
        let Self {
            blocks,
            insts,
            dominators,
            ..
        } = self;

        let mut scope = Vec::<Val>::new();
        let mut stack = vec![ScopeFrame::Enter(entry)];

        while let Some(frame) = stack.pop() {
            let block = match frame {
                ScopeFrame::Restore(len) => {
                    scope.truncate(len);
                    continue;
                }
                ScopeFrame::Enter(block) => block,
            };

            stack.push(ScopeFrame::Restore(scope.len()));
            scope.extend_from_slice(&blocks[block].params);

            for inst in &blocks[block].insts {
                let inst = *inst;

                for op in insts[inst].operands_mut() {
                    if op.kind() == DefUse::Use {
                        op.set_val(in_scope(&scope, op.val()));
                    }
                }
                for call in insts[inst].block_calls_mut() {
                    for arg in &mut call.args {
                        *arg = in_scope(&scope, *arg);
                    }
                }

                for op in insts[inst].operands() {
                    if op.kind() == DefUse::Def {
                        scope.push(op.val());
                    }
                }
            }

            // Every block is reachable, so this walk reaches every block.
            stack.extend(block.dom_children(dominators).map(ScopeFrame::Enter));
        }
    }
}

enum ScopeFrame {
    Enter(Block),
    Restore(usize),
}

/// Get `val` if it is in scope, or else some value that is.
fn in_scope(scope: &[Val], val: Val) -> Val {
    if scope.contains(&val) {
        return val;
    }
    assert!(
        !scope.is_empty(),
        "`ensure_entry_param_when_needed` should have given the entry block a parameter \
         so that at least one value is in scope at every use",
    );
    scope[val.index() % scope.len()]
}

pub struct TestBlock<'a> {
    func: &'a TestFunction,
    block: Block,
}

pub struct TestInst<'a> {
    func: &'a TestFunction,
    inst: Inst,
}

pub struct TestValue<'a> {
    func: &'a TestFunction,
    val: Val,
}

pub struct TestValuesIter<'a> {
    func: &'a TestFunction,
    keys: crate::entity::PrimaryMapKeys<Val>,
}

impl<'a> Iterator for TestValuesIter<'a> {
    type Item = (Val, TestValue<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        let val = self.keys.next()?;
        Some((
            val,
            TestValue {
                func: self.func,
                val,
            },
        ))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.keys.size_hint()
    }
}

impl<'a> ExactSizeIterator for TestValuesIter<'a> {}

impl<'a> InputValue<'a> for TestValue<'a> {
    fn val(&self) -> Val {
        self.val
    }

    fn remat_cost(&self) -> Option<RematCost> {
        let index = self.func.values[self.val].remat;
        REMAT_COSTS[usize::from(index) % REMAT_COSTS.len()]
    }

    fn reg_class(&self) -> RegClass {
        RegClass::try_new(usize::from(self.func.values[self.val].reg_class)).unwrap()
    }
}

pub struct TestBlocksIter<'a> {
    func: &'a TestFunction,
    keys: crate::entity::PrimaryMapKeys<Block>,
}

impl<'a> Iterator for TestBlocksIter<'a> {
    type Item = (Block, TestBlock<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        let block = self.keys.next()?;
        Some((
            block,
            TestBlock {
                func: self.func,
                block,
            },
        ))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.keys.size_hint()
    }
}

impl<'a> ExactSizeIterator for TestBlocksIter<'a> {}

pub struct TestInstsIter<'b> {
    func: &'b TestFunction,
    insts: slice::Iter<'b, Inst>,
}

impl<'b> TestInstsIter<'b> {
    fn item(&self, inst: &Inst) -> (Inst, TestInst<'b>) {
        (
            *inst,
            TestInst {
                func: self.func,
                inst: *inst,
            },
        )
    }
}

impl<'b> Iterator for TestInstsIter<'b> {
    type Item = (Inst, TestInst<'b>);

    fn next(&mut self) -> Option<Self::Item> {
        let inst = self.insts.next()?;
        Some(self.item(inst))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.insts.size_hint()
    }
}

impl<'b> DoubleEndedIterator for TestInstsIter<'b> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let inst = self.insts.next_back()?;
        Some(self.item(inst))
    }
}

impl<'b> ExactSizeIterator for TestInstsIter<'b> {}

impl InputFunction for TestFunction {
    type InputBlock<'a>
        = TestBlock<'a>
    where
        Self: 'a;

    type InputInst<'a>
        = TestInst<'a>
    where
        Self: 'a;

    type InputValue<'a>
        = TestValue<'a>
    where
        Self: 'a;

    fn len_values(&self) -> usize {
        self.values.len()
    }

    fn len_insts(&self) -> usize {
        self.insts.len()
    }

    fn inst(&self, inst: Inst) -> Self::InputInst<'_> {
        TestInst { func: self, inst }
    }

    type ValuesIter<'a>
        = TestValuesIter<'a>
    where
        Self: 'a;

    fn values(&self) -> Self::ValuesIter<'_> {
        TestValuesIter {
            func: self,
            keys: self.values.keys(),
        }
    }

    fn value(&self, val: Val) -> Self::InputValue<'_> {
        TestValue { func: self, val }
    }

    fn entry_block(&self) -> Block {
        Block::try_new(0).unwrap()
    }

    fn len_blocks(&self) -> usize {
        self.blocks.len()
    }

    fn block(&self, block: Block) -> Self::InputBlock<'_> {
        TestBlock { func: self, block }
    }

    type BlocksIter<'a>
        = TestBlocksIter<'a>
    where
        Self: 'a;

    fn blocks(&self) -> Self::BlocksIter<'_> {
        TestBlocksIter {
            func: self,
            keys: self.blocks.keys(),
        }
    }
}

impl<'a> InputBlock<'a> for TestBlock<'a> {
    type InputInst<'b>
        = TestInst<'b>
    where
        Self: 'b;

    fn block(&self) -> Block {
        self.block
    }

    fn frequency(&self) -> BlockFrequency {
        let index = self.func.blocks[self.block].frequency;
        BLOCK_FREQUENCIES[usize::from(index) % BLOCK_FREQUENCIES.len()]
    }

    fn len_insts(&self, _block: Block) -> usize {
        self.func.blocks[self.block].insts.len()
    }

    type InstsIter<'b>
        = TestInstsIter<'b>
    where
        Self: 'b;

    fn insts(&self) -> TestInstsIter<'_> {
        TestInstsIter {
            func: self.func,
            insts: self.func.blocks[self.block].insts.iter(),
        }
    }

    fn len_params(&self) -> usize {
        self.func.blocks[self.block].params.len()
    }

    type ParamsIter<'b>
        = core::iter::Copied<core::slice::Iter<'b, Val>>
    where
        Self: 'b;

    fn params(&self) -> Self::ParamsIter<'_> {
        self.func.blocks[self.block].params.iter().copied()
    }

    fn immediate_dominator(&self) -> Option<Block> {
        self.block.idom(&self.func.dominators)
    }

    fn dominates(&self, other: Block) -> bool {
        self.block.dominates(&self.func.dominators, other)
    }

    fn len_successors(&self) -> usize {
        self.successors().len()
    }

    type SuccessorsIter<'b>
        = TestBlockSuccessorsIter<'b>
    where
        Self: 'b;

    fn successors(&self) -> Self::SuccessorsIter<'_> {
        TestBlockSuccessorsIter {
            inner: self.block_calls().iter(),
        }
    }

    fn len_predecessors(&self) -> usize {
        self.func.predecessors[self.block].len()
    }

    type PredecessorsIter<'b>
        = core::iter::Copied<slice::Iter<'b, Block>>
    where
        Self: 'b;

    fn predecessors(&self) -> Self::PredecessorsIter<'_> {
        self.func.predecessors[self.block].iter().copied()
    }

    fn len_successor_block_args(&self, i: usize) -> usize {
        self.block_calls()[i].args.len()
    }

    type SuccessorBlockArgsIter<'b>
        = core::iter::Copied<core::slice::Iter<'b, Val>>
    where
        Self: 'b;

    fn successor_block_args(&self, successor: usize) -> Self::SuccessorBlockArgsIter<'_> {
        self.block_calls()[successor].args.iter().copied()
    }
}

impl<'a> TestBlock<'a> {
    /// Get the block calls in this block's terminator, i.e. its outgoing
    /// control-flow edges and the arguments passed along each of them.
    fn block_calls(&self) -> &'a [BlockCall] {
        let inst = *self.func.blocks[self.block].insts.last().unwrap();
        match &self.func.insts[inst] {
            InstData::Op { .. } => panic!("invalid function; should have called `fixup`"),
            InstData::Branch {
                operands: _,
                targets,
            } => targets,
        }
    }
}

pub struct TestBlockSuccessorsIter<'a> {
    inner: core::slice::Iter<'a, BlockCall>,
}

impl Iterator for TestBlockSuccessorsIter<'_> {
    type Item = Block;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.inner.next()?.target)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl ExactSizeIterator for TestBlockSuccessorsIter<'_> {}

impl<'a> InputInst<'a> for TestInst<'a> {
    fn inst(&self) -> Inst {
        self.inst
    }

    fn operands_len(&self) -> usize {
        self.operands().len()
    }

    type OperandsIter<'b>
        = core::iter::Cloned<slice::Iter<'b, Operand>>
    where
        Self: 'b;

    fn operands(&self) -> Self::OperandsIter<'_> {
        self.func.insts[self.inst].operands().iter().cloned()
    }

    fn operand(&self, i: usize) -> Operand {
        self.func.insts[self.inst].operands()[i]
    }

    fn block(&self) -> Block {
        self.func.inst_blocks[self.inst]
            .expect("should have been inserted by `ensure_unique_insts_in_layout`")
    }
}

/// A description of a machine, in a form that `mutatis` can generate and
/// mutate.
#[derive(Clone, Debug, Hash)]
pub struct TestMachine {
    banks: Vec<TestBank>,

    /// How many registers every bank should have, or `None` for however many
    /// the mutator happened to generate.
    ///
    /// The visualizer example's `--regs` knob, and the reason it lives here
    /// rather than being applied by the caller: [`TestInputMutator`] calls
    /// [`TestMachine::fixup`] after every mutation, and `fixup` is what
    /// decides how many registers a bank has. A count set from outside would
    /// be undone by the next mutation; a count set here is re-applied by it.
    ///
    /// Every bank, not a total: the mutated machine's shape is kept, so
    /// `Some(8)` on a two-bank machine is sixteen registers.
    regs_per_bank: Option<usize>,
}

#[derive(Clone, Debug, Default, Hash, Mutate)]
pub struct TestBank {
    /// The base-two logarithm of this bank's registers' byte size.
    ///
    /// Stored as the logarithm because `declare_reg_bank` only accepts powers
    /// of two, so generating the exponent means every generated machine is
    /// valid without a fixup rejecting anything.
    log2_size: u8,

    /// One entry per register the allocator owns: how many register units wide
    /// it is.
    regs: Vec<u8>,

    /// How many further registers this bank has that the allocator does not own.
    non_allocatable: u8,

    /// This bank's register groups.
    groups: Vec<TestGroup>,

    /// This bank's register classes.
    classes: Vec<TestClass>,
}

#[derive(Clone, Debug, Default, Hash, Mutate)]
pub struct TestGroup {
    /// Indices into the bank's `regs`, in the group's order.
    members: Vec<u8>,
}

#[derive(Clone, Debug, Default, Hash, Mutate)]
pub struct TestClass {
    members: TestClassMembers,

    /// Scaled into the `f32` spill cost that `define_reg_class` wants; an
    /// integer here so that `TestMachine` can derive `Hash`.
    spill_cost: u8,
}

/// What a class holds: either individual registers or whole register groups,
/// never a mix of the two.
#[derive(Clone, Debug, Hash, Mutate)]
pub enum TestClassMembers {
    /// Indices into the bank's `regs`, in preference order.
    Regs(Vec<u8>),

    /// Indices into the bank's `groups`, in preference order.
    Groups(Vec<u8>),
}

impl Default for TestClassMembers {
    fn default() -> Self {
        Self::Regs(Vec::new())
    }
}

impl Default for TestMachine {
    fn default() -> Self {
        let mut machine = TestMachine {
            banks: Vec::new(),
            regs_per_bank: None,
        };
        machine.fixup();
        machine
    }
}

impl TestMachine {
    /// The ceilings on a generated machine's size.
    ///
    /// Well within the actual imposed limits so that, e.g., we will always have
    /// entity capacity for the derived intersection register classes.
    const MAX_BANKS: usize = 2;
    const MAX_REGS_PER_BANK: usize = 4;
    const MAX_NON_ALLOCATABLE_PER_BANK: u8 = 2;
    const MAX_GROUPS_PER_BANK: usize = 3;
    const MAX_CLASSES_PER_BANK: usize = 4;

    /// The most registers per bank that [`TestMachine::set_regs_per_bank`] will
    /// take.
    ///
    /// Deliberately far above `MAX_REGS_PER_BANK`, which bounds the machines
    /// the mutator *generates* and so the shape of every property test: this
    /// bounds only what a caller may ask for. Well inside the real ceilings --
    /// `Reg::MAX` and `RegUnit::MAX` are both 512, and two banks of sixty-four
    /// two-unit registers is 256 units.
    pub const MAX_REGS_PER_BANK_TARGET: usize = 64;

    /// The widest a generated register may be, in register units.
    const MAX_REG_UNITS: u8 = 2;

    /// The largest generated register size, as a base-two logarithm: banks hold
    /// registers of one, two, four, or eight bytes.
    ///
    /// More than one size, so that spill slots really do get pooled separately;
    /// few enough that two banks often land on the same size, which is the case
    /// where they share a pool.
    const MAX_LOG2_REG_SIZE: u8 = 3;

    /// The class holding both of [`TestMachine::two_registers`]' registers,
    /// and so the only one of its classes that a value can belong to while
    /// still meeting either an `rc0` or an `rc1` operand constraint.
    pub const BOTH_REGS_CLASS: u8 = 2;

    /// The class holding [`TestMachine::two_registers`]' first register alone,
    /// and so the way to pin an operand there.
    pub const FIRST_REG_CLASS: u8 = 0;

    /// The class holding [`TestMachine::two_registers`]' second register alone,
    /// which nothing pinned to [`TestMachine::FIRST_REG_CLASS`] can satisfy.
    pub const SECOND_REG_CLASS: u8 = 1;

    /// A machine of one bank with two registers and three classes: `rc0` holds
    /// the first register, `rc1` the second, and `rc2` both.
    ///
    /// `rc0` and `rc1` are disjoint, so nothing can satisfy both of them at
    /// once.
    pub fn two_registers() -> Self {
        let one_reg = |i| TestClass {
            members: TestClassMembers::Regs(vec![i]),
            spill_cost: 0,
        };
        let mut machine = TestMachine {
            banks: vec![TestBank {
                log2_size: 3,
                regs: vec![1, 1],
                non_allocatable: 0,
                groups: Vec::new(),
                classes: vec![
                    one_reg(0),
                    one_reg(1),
                    TestClass {
                        members: TestClassMembers::Regs(vec![0, 1]),
                        spill_cost: 0,
                    },
                ],
            }],
            regs_per_bank: None,
        };
        machine.fixup();
        machine
    }

    /// The class holding [`TestMachine::one_register_group`]'s only register
    /// group, and its only class.
    pub const GROUP_CLASS: u8 = 0;

    /// A machine of one bank whose two registers form its only register group,
    /// with one class, `rc0`, holding that group.
    ///
    /// A value here occupies both registers at once, so spilling one takes two
    /// slots and moving one takes two moves.
    pub fn one_register_group() -> Self {
        let mut machine = TestMachine {
            banks: vec![TestBank {
                log2_size: 3,
                regs: vec![1, 1],
                non_allocatable: 0,
                groups: vec![TestGroup {
                    members: vec![0, 1],
                }],
                classes: vec![TestClass {
                    members: TestClassMembers::Groups(vec![0]),
                    spill_cost: 0,
                }],
            }],
            regs_per_bank: None,
        };
        machine.fixup();
        machine
    }

    /// [`TestMachine::groups_and_registers`]' `rc0`: its first register group.
    pub const FIRST_GROUP_CLASS: u8 = 0;

    /// [`TestMachine::groups_and_registers`]' `rc1`: its second register
    /// group, and so nothing `rc0` holds.
    pub const SECOND_GROUP_CLASS: u8 = 1;

    /// [`TestMachine::groups_and_registers`]' `rc2`: both register groups.
    pub const EITHER_GROUP_CLASS: u8 = 2;

    /// [`TestMachine::groups_and_registers`]' `rc3`: its first bank's four
    /// registers, one at a time rather than in groups.
    pub const WIDE_REGS_CLASS: u8 = 3;

    /// [`TestMachine::groups_and_registers`]' `rc4`: its second bank, an
    /// eighth the width of the first.
    pub const NARROW_REGS_CLASS: u8 = 4;

    /// A machine with confusable allocations: bank 0's four eight-byte
    /// registers pair into two groups, with classes for each group, both
    /// groups, and the four alone; bank 1 has two one-byte registers. So a
    /// group, a single register, and two slot sizes can all be told apart.
    pub fn groups_and_registers() -> Self {
        let mut machine = TestMachine {
            banks: vec![
                TestBank {
                    log2_size: 3,
                    regs: vec![1, 1, 1, 1],
                    non_allocatable: 0,
                    groups: vec![
                        TestGroup {
                            members: vec![0, 1],
                        },
                        TestGroup {
                            members: vec![2, 3],
                        },
                    ],
                    classes: vec![
                        TestClass {
                            members: TestClassMembers::Groups(vec![0]),
                            spill_cost: 0,
                        },
                        TestClass {
                            members: TestClassMembers::Groups(vec![1]),
                            spill_cost: 0,
                        },
                        TestClass {
                            members: TestClassMembers::Groups(vec![0, 1]),
                            spill_cost: 0,
                        },
                        TestClass {
                            members: TestClassMembers::Regs(vec![0, 1, 2, 3]),
                            spill_cost: 0,
                        },
                    ],
                },
                TestBank {
                    log2_size: 0,
                    regs: vec![1, 1],
                    non_allocatable: 0,
                    groups: Vec::new(),
                    classes: vec![TestClass {
                        members: TestClassMembers::Regs(vec![0, 1]),
                        spill_cost: 0,
                    }],
                },
            ],
            regs_per_bank: None,
        };
        machine.fixup();
        machine
    }

    /// Give `bank` one more register that the allocator does not own, and
    /// answer which [`Reg`] it will be once the machine is built.
    ///
    /// No class holds it. That is the ordinary state of affairs for a stack
    /// pointer or a flags register --- a class holds one only when an operand
    /// has to pin a read to it --- and it leaves every choice the allocator
    /// makes exactly as it was, so a test that puts something in this register
    /// by hand knows that nothing else did.
    #[cfg(test)]
    pub(crate) fn push_non_allocatable_reg(&mut self, bank: usize) -> Reg {
        let before: usize = self.banks[..bank]
            .iter()
            .map(|bank| bank.regs.len() + usize::from(bank.non_allocatable))
            .sum();
        let bank = &mut self.banks[bank];
        let reg = before + bank.regs.len() + usize::from(bank.non_allocatable);
        bank.non_allocatable += 1;
        assert!(
            bank.non_allocatable <= Self::MAX_NON_ALLOCATABLE_PER_BANK,
            "a bank holds at most {} registers the allocator does not own",
            Self::MAX_NON_ALLOCATABLE_PER_BANK,
        );
        Reg::try_new(reg).unwrap()
    }

    /// How many register classes this machine defines, which is the number of
    /// classes an operand may name.
    ///
    /// This counts only the classes described here, not the intersections that
    /// `MachineBuilder::finish` derives from them.
    pub fn num_classes(&self) -> usize {
        self.banks.iter().map(|bank| bank.classes.len()).sum()
    }

    /// Give every bank exactly `n` registers, now and after every later
    /// [`TestMachine::fixup`].
    ///
    /// The machine's shape survives: banks, groups, non-allocatable registers
    /// and classes are all still whatever they were, so this widens a machine
    /// rather than replacing it. `n` is per bank, so a two-bank machine ends
    /// up with `2 * n` registers.
    ///
    /// # Panics
    ///
    /// Panics unless `n` is between one and
    /// [`TestMachine::MAX_REGS_PER_BANK_TARGET`]: a bank needs one register
    /// the allocator owns for stack-to-stack moves, and the ceiling is what
    /// keeps the derived register classes inside the real entity limits.
    pub fn set_regs_per_bank(&mut self, n: usize) {
        assert!(
            (1..=Self::MAX_REGS_PER_BANK_TARGET).contains(&n),
            "regs per bank must be between 1 and {}, not {n}",
            Self::MAX_REGS_PER_BANK_TARGET,
        );
        self.regs_per_bank = Some(n);
        self.fixup();
    }

    /// Repair this description so that [`TestMachine::build`] cannot fail.
    pub fn fixup(&mut self) {
        self.banks.truncate(Self::MAX_BANKS);
        if self.banks.is_empty() {
            self.banks.push(TestBank::default());
        }

        for bank in &mut self.banks {
            bank.log2_size %= Self::MAX_LOG2_REG_SIZE + 1;

            // A bank needs a register that the allocator owns for
            // stack-to-stack moves.
            let target = self.regs_per_bank.unwrap_or(Self::MAX_REGS_PER_BANK);
            bank.regs.truncate(target);
            if self.regs_per_bank.is_some() {
                // Padded with the narrowest register, so that a wider bank is
                // a bank with more places to put a value rather than one with
                // wider values in it.
                bank.regs.resize(target, 1);
            }
            if bank.regs.is_empty() {
                bank.regs.push(1);
            }
            for units in &mut bank.regs {
                // Clamped rather than reduced modulo, because `x % n` is not
                // idempotent once shifted off zero.
                *units = (*units).clamp(1, Self::MAX_REG_UNITS);
            }
            bank.non_allocatable %= Self::MAX_NON_ALLOCATABLE_PER_BANK + 1;

            let num_regs = bank.regs.len();

            // A group holds at least two distinct registers, so a bank with
            // only one register has no groups at all.
            bank.groups.truncate(Self::MAX_GROUPS_PER_BANK);
            if num_regs < 2 {
                bank.groups.clear();
            }
            for group in &mut bank.groups {
                for member in &mut group.members {
                    *member %= u8::try_from(num_regs).unwrap();
                }
                dedupe_keeping_first(&mut group.members);
                group
                    .members
                    .truncate(core::cmp::min(RegGroup::MAX_SIZE, num_regs));
                while group.members.len() < 2 {
                    let next = (0..u8::try_from(num_regs).unwrap())
                        .find(|reg| !group.members.contains(reg))
                        .unwrap();
                    group.members.push(next);
                }
            }

            bank.classes.truncate(Self::MAX_CLASSES_PER_BANK);
            if bank.classes.is_empty() {
                bank.classes.push(TestClass::default());
            }
            for class in &mut bank.classes {
                // A class of groups needs a group to name; the pass below
                // gives the empty register list a member.
                if bank.groups.is_empty() && matches!(class.members, TestClassMembers::Groups(_)) {
                    class.members = TestClassMembers::Regs(Vec::new());
                }

                match &mut class.members {
                    TestClassMembers::Regs(regs) => {
                        for member in regs.iter_mut() {
                            *member %= u8::try_from(num_regs).unwrap();
                        }
                        dedupe_keeping_first(regs);
                        if regs.is_empty() {
                            regs.push(0);
                        }
                        // A widened bank's new registers have to reach a
                        // class, or they are registers the allocator can see
                        // and never use: the repair above only reduces member
                        // indices modulo `num_regs`, it never adds members, so
                        // padding alone would widen the machine without
                        // loosening the allocation by a single register.
                        //
                        // Appended, so the class's original members stay at
                        // the front and its preference order survives. Classes
                        // of groups are left alone: one class holds groups of
                        // one size, and there is no group to put a lone new
                        // register in.
                        if self.regs_per_bank.is_some() {
                            for reg in 0..u8::try_from(num_regs).unwrap() {
                                if !regs.contains(&reg) {
                                    regs.push(reg);
                                }
                            }
                        }
                    }

                    TestClassMembers::Groups(groups) => {
                        for member in groups.iter_mut() {
                            *member %= u8::try_from(bank.groups.len()).unwrap();
                        }
                        dedupe_keeping_first(groups);
                        if groups.is_empty() {
                            groups.push(0);
                        }
                        // One class holds groups of one size, so keep the
                        // groups that match the first one's size and drop the
                        // rest.
                        let size = bank.groups[usize::from(groups[0])].members.len();
                        groups
                            .retain(|&group| bank.groups[usize::from(group)].members.len() == size);
                    }
                }
            }
        }
    }

    /// Build the [`Machine`] this `TestMachine` describes.
    pub fn build(&self) -> Machine {
        let mut builder = MachineBuilder::new();

        for bank in &self.banks {
            let size = SpillSlotSize::from_log2(bank.log2_size);
            let reg_bank = builder.declare_reg_bank(size).unwrap();

            let mut next_unit = 0;
            let regs: Vec<Reg> = bank
                .regs
                .iter()
                .map(|&units| {
                    let start = RegUnit::try_new(next_unit).unwrap();
                    next_unit += usize::from(units);
                    let end = RegUnit::try_new(next_unit).unwrap();
                    builder.define_reg(reg_bank, start..end).unwrap()
                })
                .collect();

            for _ in 0..bank.non_allocatable {
                builder.define_non_allocatable_reg(reg_bank).unwrap();
            }

            let groups: Vec<RegGroup> = bank
                .groups
                .iter()
                .map(|group| {
                    let members = group.members.iter().map(|&m| regs[usize::from(m)]);
                    builder.define_reg_group(reg_bank, members).unwrap()
                })
                .collect();

            for class in &bank.classes {
                let spill_cost = f32::from(class.spill_cost) + 1.0;
                match &class.members {
                    TestClassMembers::Regs(members) => {
                        let members = members.iter().map(|&m| regs[usize::from(m)]);
                        builder
                            .define_reg_class(reg_bank, spill_cost, members)
                            .unwrap();
                    }
                    TestClassMembers::Groups(members) => {
                        let members = members.iter().map(|&m| groups[usize::from(m)]);
                        builder
                            .define_reg_group_class(reg_bank, spill_cost, members)
                            .unwrap();
                    }
                }
            }
        }

        builder.finish().unwrap()
    }
}

fn dedupe_keeping_first(members: &mut Vec<u8>) {
    let mut seen = [false; 256];
    members.retain(|&member| !mem::replace(&mut seen[usize::from(member)], true));
}

#[derive(Default)]
pub struct TestMachineMutator {}

impl Mutate<TestMachine> for TestMachineMutator {
    fn mutate(
        &mut self,
        mutations: &mut mutatis::Candidates<'_>,
        machine: &mut TestMachine,
    ) -> mutatis::Result<()> {
        <Vec<TestBank> as DefaultMutate>::DefaultMutate::default()
            .proj(|TestMachine { banks, .. }: &mut TestMachine| banks)
            .map(|_ctx, m| {
                m.fixup();
                Ok(())
            })
            .mutate(mutations, machine)
    }
}

impl Generate<TestMachine> for TestMachineMutator {
    fn generate(&mut self, context: &mut mutatis::Context) -> mutatis::Result<TestMachine> {
        let mut machine = TestMachine {
            banks: <Vec<TestBank> as DefaultMutate>::DefaultMutate::default().generate(context)?,
            regs_per_bank: None,
        };
        machine.fixup();
        Ok(machine)
    }
}

impl DefaultMutate for TestMachine {
    type DefaultMutate = TestMachineMutator;
}

/// A whole register allocation problem for testing: a machine and a function to
/// allocate registers in.
#[derive(Clone, Debug, Hash)]
pub struct TestInput {
    pub options: InputOptions,
    pub machine: TestMachine,
    pub func: TestFunction,
}

impl Default for TestInput {
    fn default() -> Self {
        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::default(),
            func: TestFunction::default(),
        };
        input.fixup();
        input
    }
}

impl TestInput {
    /// Repair this test input.
    pub fn fixup(&mut self) {
        self.machine.fixup();
        self.func.fixup();

        let num_classes = self.machine.num_classes();
        for (_inst, inst_data) in self.func.insts.iter_mut() {
            for operand in inst_data.operands_mut() {
                let OperandConstraint::Reg(class) = operand.constraint() else {
                    continue;
                };
                let class = RegClass::try_new(class.index() % num_classes).unwrap();
                *operand = Operand::new(
                    operand.pos(),
                    operand.kind(),
                    OperandConstraint::Reg(class),
                    operand.val(),
                );
            }
        }

        // One modulus applied uniformly, so the classes that
        // `TestFunction::ensure_reg_classes_agree` made equal stay equal.
        let num_classes = u8::try_from(num_classes).unwrap();
        for (_val, val_data) in self.func.values.iter_mut() {
            val_data.reg_class %= num_classes;
        }

        // An operand constraint must name a subset of its value's register
        // class.
        let machine = self.machine.build();
        for (_inst, inst_data) in self.func.insts.iter_mut() {
            for operand in inst_data.operands_mut() {
                let OperandConstraint::Reg(class) = operand.constraint() else {
                    continue;
                };
                let val_class =
                    RegClass::try_new(usize::from(self.func.values[operand.val()].reg_class))
                        .unwrap();
                if class.intersect(&machine, val_class) == Some(class) {
                    continue;
                }
                *operand = Operand::new(
                    operand.pos(),
                    operand.kind(),
                    OperandConstraint::Reg(val_class),
                    operand.val(),
                );
            }
        }
    }

    /// A single-block input whose one value is defined by the first
    /// instruction and then used once per entry in `constraints`, one use per
    /// instruction, in that order.
    ///
    /// The machine is [`TestMachine::two_registers`], so `Reg(rc0)` and
    /// `Reg(rc1)` are the pair of constraints that conflict and `Reg(rc2)` is
    /// the one that can be met alongside either.
    pub fn with_use_constraints(constraints: &[OperandConstraint]) -> Self {
        Self::with_use_constraints_in(
            TestMachine::two_registers(),
            TestMachine::BOTH_REGS_CLASS,
            OperandConstraint::Any,
            constraints,
        )
    }

    /// As [`TestInput::with_use_constraints`], but on
    /// [`TestMachine::one_register_group`], where the value occupies a whole
    /// register group.
    ///
    /// The definition is pinned to the group rather than left to `Any`, which
    /// the allocator is free to satisfy on the stack, so that a use on the
    /// stack really is a spill.
    pub fn with_group_use_constraints(constraints: &[OperandConstraint]) -> Self {
        let class = RegClass::try_new(usize::from(TestMachine::GROUP_CLASS)).unwrap();
        Self::with_use_constraints_in(
            TestMachine::one_register_group(),
            TestMachine::GROUP_CLASS,
            OperandConstraint::Reg(class),
            constraints,
        )
    }

    /// [`TestInput::with_use_constraints`] on any machine, with the value in
    /// `reg_class` and defined under `def_constraint`.
    pub fn with_use_constraints_in(
        machine: TestMachine,
        reg_class: u8,
        def_constraint: OperandConstraint,
        constraints: &[OperandConstraint],
    ) -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = Val::try_new(0).unwrap();
        let def = Inst::try_new(0).unwrap();

        func.values = PrimaryMap::new();
        func.values
            .push(
                &mut output,
                ValData {
                    reg_class,
                    def: ValDef::InstResult { inst: def, i: 0 },
                    remat: 0,
                },
            )
            .unwrap();

        func.insts = PrimaryMap::new();
        func.insts
            .push(
                &mut output,
                InstData::Op {
                    operands: vec![Operand::new(
                        Position::Late,
                        DefUse::Def,
                        def_constraint,
                        val,
                    )],
                    side_effects: true,
                },
            )
            .unwrap();
        for &constraint in constraints {
            func.insts
                .push(
                    &mut output,
                    InstData::Op {
                        operands: vec![Operand::new(Position::Early, DefUse::Use, constraint, val)],
                        side_effects: true,
                    },
                )
                .unwrap();
        }

        // `ensure_terminators` turns a block's last instruction into a branch,
        // so hand it one of its own rather than letting it take the last use.
        func.insts
            .push(
                &mut output,
                InstData::Op {
                    operands: vec![],
                    side_effects: true,
                },
            )
            .unwrap();

        let num_insts = func.insts.len();
        func.blocks = PrimaryMap::new();
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: vec![],
                    insts: (0..num_insts).map(|i| Inst::try_new(i).unwrap()).collect(),
                    frequency: 0,
                },
            )
            .unwrap();

        let mut input = TestInput {
            options: InputOptions::default(),
            machine,
            func,
        };
        input.fixup();
        input
    }

    /// A single-block input whose third instruction reads two different
    /// values, one pinned to each of [`TestMachine::two_registers`]' two
    /// registers.
    ///
    /// This is the smallest function with one instruction whose operands are
    /// in known, *different* places, which is what it takes to say that an
    /// operand went somewhere another operand of the same instruction did not.
    pub fn with_two_uses_of_different_values() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let first = Val::try_new(0).unwrap();
        let second = Val::try_new(1).unwrap();
        let r0 = RegClass::try_new(0).unwrap();
        let r1 = RegClass::try_new(1).unwrap();

        func.values = PrimaryMap::new();
        for i in 0..2 {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def: ValDef::InstResult {
                            inst: Inst::try_new(i).unwrap(),
                            i: 0,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let def = |val| InstData::Op {
            operands: vec![Operand::new(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Any,
                val,
            )],
            side_effects: true,
        };

        func.insts = PrimaryMap::new();
        for inst_data in [
            def(first),
            def(second),
            InstData::Op {
                operands: vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(r0),
                        first,
                    ),
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(r1),
                        second,
                    ),
                ],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the reads.
            InstData::Op {
                operands: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        let num_insts = func.insts.len();
        func.blocks = PrimaryMap::new();
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: vec![],
                    insts: (0..num_insts).map(|i| Inst::try_new(i).unwrap()).collect(),
                    frequency: 0,
                },
            )
            .unwrap();

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A single-block input on [`TestMachine::groups_and_registers`] whose two
    /// values live in different banks, and each of which is defined in a
    /// register, then read on the stack, then read in a register again.
    ///
    /// The stack reads force one spill per value, into slots of different
    /// sizes, and the register reads force one reload per value, into
    /// registers of different banks. That makes this the fixture on which
    /// swapping a pair of moves' destinations is a well-defined perturbation:
    /// there is exactly one wrong slot and exactly one wrong bank to swap in,
    /// and neither has to be guessed at by index.
    pub fn with_values_in_two_banks_spilled_and_reloaded() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let wide = Val::try_new(0).unwrap();
        let narrow = Val::try_new(1).unwrap();
        let wide_regs = RegClass::try_new(TestMachine::WIDE_REGS_CLASS.into()).unwrap();
        let narrow_regs = RegClass::try_new(TestMachine::NARROW_REGS_CLASS.into()).unwrap();

        func.values = PrimaryMap::new();
        for (i, reg_class) in [TestMachine::WIDE_REGS_CLASS, TestMachine::NARROW_REGS_CLASS]
            .into_iter()
            .enumerate()
        {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class,
                        def: ValDef::InstResult {
                            inst: Inst::try_new(i).unwrap(),
                            i: 0,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let def = |val, class| InstData::Op {
            operands: vec![Operand::new(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Reg(class),
                val,
            )],
            side_effects: true,
        };
        let reads = |constraint: fn(RegClass) -> OperandConstraint| InstData::Op {
            operands: vec![
                Operand::new(Position::Early, DefUse::Use, constraint(wide_regs), wide),
                Operand::new(
                    Position::Early,
                    DefUse::Use,
                    constraint(narrow_regs),
                    narrow,
                ),
            ],
            side_effects: true,
        };

        func.insts = PrimaryMap::new();
        for inst_data in [
            def(wide, wide_regs),
            def(narrow, narrow_regs),
            reads(|_| OperandConstraint::Stack),
            reads(OperandConstraint::Reg),
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the reads.
            InstData::Op {
                operands: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        let num_insts = func.insts.len();
        func.blocks = PrimaryMap::new();
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: vec![],
                    insts: (0..num_insts).map(|i| Inst::try_new(i).unwrap()).collect(),
                    frequency: 0,
                },
            )
            .unwrap();

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::groups_and_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A single-block input with one instruction that ties a def to a use: the
    /// def carries a `Reuse` naming the use operand, whose own constraint is
    /// `use_constraint`.
    ///
    /// This is the smallest function with a tied operand, which is the case
    /// that the spill weight model prices differently from every other use.
    pub fn with_reuse_def(use_constraint: OperandConstraint) -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let defined = Val::try_new(0).unwrap();
        let tied = Val::try_new(1).unwrap();

        func.values = PrimaryMap::new();
        for i in 0..2 {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def: ValDef::InstResult {
                            inst: Inst::try_new(i).unwrap(),
                            i: 0,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        func.insts = PrimaryMap::new();
        for inst_data in [
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    defined,
                )],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![
                    Operand::new(Position::Early, DefUse::Use, use_constraint, defined),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(0),
                        tied,
                    ),
                ],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the tied instruction.
            InstData::Op {
                operands: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        let num_insts = func.insts.len();
        func.blocks = PrimaryMap::new();
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: vec![],
                    insts: (0..num_insts).map(|i| Inst::try_new(i).unwrap()).collect(),
                    frequency: 0,
                },
            )
            .unwrap();

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A single-block input whose reuse target outlives the tie: the value is
    /// read at the tied use and again later. The smallest function that needs
    /// construction's reuse split.
    pub fn with_reuse_of_a_surviving_value() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let defined = Val::try_new(0).unwrap();
        let tied = Val::try_new(1).unwrap();

        func.values = PrimaryMap::new();
        for i in 0..2 {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def: ValDef::InstResult {
                            inst: Inst::try_new(i).unwrap(),
                            i: 0,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        func.insts = PrimaryMap::new();
        for inst_data in [
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    defined,
                )],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        defined,
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(0),
                        tied,
                    ),
                ],
                side_effects: true,
            },
            // The read that makes the tied use's value a survivor.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Any,
                    defined,
                )],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the later read.
            InstData::Op {
                operands: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        let num_insts = func.insts.len();
        func.blocks = PrimaryMap::new();
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: vec![],
                    insts: (0..num_insts).map(|i| Inst::try_new(i).unwrap()).collect(),
                    frequency: 0,
                },
            )
            .unwrap();

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// Like `with_reuse_of_a_surviving_value`, but the tied instruction reads
    /// the survivor *twice*. Both reads are at one point, so construction must
    /// put both in the overwritten span or the value needs a third register.
    pub fn with_two_reads_and_a_reuse_of_a_surviving_value() -> Self {
        Self::two_reads_and_a_reuse_of_a_surviving_value(OperandConstraint::Any)
    }

    /// Like `with_two_reads_and_a_reuse_of_a_surviving_value`, but the plain
    /// read is pinned to one register while the tie resolves to the value's
    /// two-register class.
    ///
    /// The overwritten span inherits its fixedness from that read rather than
    /// from the tie: the tie is not fixed, but the read joins it, and the
    /// span they share can only live in `r0`.
    pub fn with_a_fixed_read_beside_a_reuse_of_a_surviving_value() -> Self {
        let class = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();
        Self::two_reads_and_a_reuse_of_a_surviving_value(OperandConstraint::Reg(class))
    }

    /// The body of `with_two_reads_and_a_reuse_of_a_surviving_value` and
    /// `with_a_fixed_read_beside_a_reuse_of_a_surviving_value`, which differ
    /// only in what the plain read demands.
    fn two_reads_and_a_reuse_of_a_surviving_value(plain_read: OperandConstraint) -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let defined = Val::try_new(0).unwrap();
        let tied = Val::try_new(1).unwrap();

        func.values = PrimaryMap::new();
        for i in 0..2 {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def: ValDef::InstResult {
                            inst: Inst::try_new(i).unwrap(),
                            i: 0,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        func.insts = PrimaryMap::new();
        for inst_data in [
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    defined,
                )],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![
                    // The plain read, at the same point as the tied one.
                    Operand::new(Position::Early, DefUse::Use, plain_read, defined),
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        defined,
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(1),
                        tied,
                    ),
                ],
                side_effects: true,
            },
            // The read that makes the tied use's value a survivor.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Any,
                    defined,
                )],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the later read.
            InstData::Op {
                operands: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        let num_insts = func.insts.len();
        func.blocks = PrimaryMap::new();
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: vec![],
                    insts: (0..num_insts).map(|i| Inst::try_new(i).unwrap()).collect(),
                    frequency: 0,
                },
            )
            .unwrap();

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// Like `with_two_reads_and_a_reuse_of_a_surviving_value`, but with an
    /// *earlier* read pinned to `r0` and the tie pinned to `r1`.
    ///
    /// The two plain reads share the tie's point and demand nothing, so they
    /// can join the overwritten piece --- the pinned read is at an earlier
    /// point and stays behind, so its `r0` has no say. Letting it speak splits
    /// the value into two registers across the tie's instruction where one
    /// would do.
    pub fn with_a_pinned_read_before_a_reuse_that_reads_twice() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let defined = Val::try_new(0).unwrap();
        let tied = Val::try_new(1).unwrap();

        let first_reg = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();
        let second_reg = RegClass::try_new(TestMachine::SECOND_REG_CLASS.into()).unwrap();

        func.values = PrimaryMap::new();
        for inst in [0, 2] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def: ValDef::InstResult {
                            inst: Inst::try_new(inst).unwrap(),
                            i: 0,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        func.insts = PrimaryMap::new();
        for inst_data in [
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    defined,
                )],
                side_effects: true,
            },
            // The pinned read, on an instruction of its own so that it is not
            // part of the tie's run.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Reg(first_reg),
                    defined,
                )],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![
                    // Two plain reads at the tie's point, so that the run has
                    // more than one use and accumulates a constraint at all.
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        defined,
                    ),
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        defined,
                    ),
                    // The tie's target, which the pinned read cannot share a
                    // register with.
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(second_reg),
                        defined,
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(2),
                        tied,
                    ),
                ],
                side_effects: true,
            },
            // The read that makes the tied use's value a survivor.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Any,
                    defined,
                )],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the later read.
            InstData::Op {
                operands: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        let num_insts = func.insts.len();
        func.blocks = PrimaryMap::new();
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: vec![],
                    insts: (0..num_insts).map(|i| Inst::try_new(i).unwrap()).collect(),
                    frequency: 0,
                },
            )
            .unwrap();

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// Like `with_reuse_of_a_surviving_value`, but the tie is at a *second*
    /// block's first instruction, so the reused value arrives live-in and the
    /// piece up to the tie is empty. Pushing one anyway would hold a third
    /// location that nothing reads, and this machine has two registers.
    pub fn with_a_reuse_of_a_live_in_value() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let defined = Val::try_new(0).unwrap();
        let tied = Val::try_new(1).unwrap();

        func.values = PrimaryMap::new();
        for inst in [0, 2] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def: ValDef::InstResult {
                            inst: Inst::try_new(inst).unwrap(),
                            i: 0,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        func.insts = PrimaryMap::new();
        for inst_data in [
            // `block0`: define the value; `block1` does all the reading.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    defined,
                )],
                side_effects: true,
            },
            InstData::Branch {
                operands: vec![],
                targets: vec![BlockCall {
                    target: Block::try_new(1).unwrap(),
                    args: vec![],
                }],
            },
            // `block1`'s first instruction: the tie, on a live-in value that
            // the read below keeps alive past it.
            InstData::Op {
                operands: vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        defined,
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(0),
                        tied,
                    ),
                ],
                side_effects: true,
            },
            // A read to make the tied value a survivor, and one of the
            // definition so that it needs a register of its own.
            InstData::Op {
                operands: vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        defined,
                    ),
                    Operand::new(Position::Early, DefUse::Use, OperandConstraint::Any, tied),
                ],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the reads.
            InstData::Op {
                operands: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        for block in [
            BlockData {
                params: vec![],
                insts: vec![inst(0), inst(1)],
                frequency: 0,
            },
            BlockData {
                params: vec![],
                insts: vec![inst(2), inst(3), inst(4)],
                frequency: 0,
            },
        ] {
            func.blocks.push(&mut output, block).unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A single-block input whose second instruction reads one surviving value
    /// twice and ties a definition to each read. Validation forbids two reuses
    /// of the *same* operand, not of different ones, so two ties sit at one
    /// point, and the piece before the second is empty and never pushed.
    pub fn with_two_reuses_at_one_point() -> Self {
        Self::two_reuses_at_one_point(true)
    }

    /// Like `with_two_reuses_at_one_point`, but nothing reads the value after
    /// the ties. The definitions overwriting the two reads cannot share a
    /// register, so nor can the reads, dying value or not.
    pub fn with_two_reuses_of_a_dying_value() -> Self {
        Self::two_reuses_at_one_point(false)
    }

    /// The body of `with_two_reuses_at_one_point` and
    /// `with_two_reuses_of_a_dying_value`, which differ only in `survives`.
    fn two_reuses_at_one_point(survives: bool) -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let defined = Val::try_new(0).unwrap();
        let first_tied = Val::try_new(1).unwrap();
        let second_tied = Val::try_new(2).unwrap();

        func.values = PrimaryMap::new();
        for def in [
            ValDef::InstResult {
                inst: Inst::try_new(0).unwrap(),
                i: 0,
            },
            ValDef::InstResult {
                inst: Inst::try_new(1).unwrap(),
                i: 0,
            },
            ValDef::InstResult {
                inst: Inst::try_new(1).unwrap(),
                i: 1,
            },
        ] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        // One location per tie, plus one for the tail if there
                        // is a later read; three of them need the wide class.
                        reg_class: if survives {
                            TestMachine::WIDE_REGS_CLASS
                        } else {
                            TestMachine::BOTH_REGS_CLASS
                        },
                        def,
                        remat: 0,
                    },
                )
                .unwrap();
        }

        func.insts = PrimaryMap::new();
        for inst_data in [
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    defined,
                )],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        defined,
                    ),
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        defined,
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(0),
                        first_tied,
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(1),
                        second_tied,
                    ),
                ],
                side_effects: true,
            },
            // The read that makes the tied value a survivor, if it has one.
            InstData::Op {
                operands: if survives {
                    vec![Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        defined,
                    )]
                } else {
                    vec![]
                },
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the read.
            InstData::Op {
                operands: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        let num_insts = func.insts.len();
        func.blocks = PrimaryMap::new();
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: vec![],
                    insts: (0..num_insts).map(|i| Inst::try_new(i).unwrap()).collect(),
                    frequency: 0,
                },
            )
            .unwrap();

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: if survives {
                TestMachine::groups_and_registers()
            } else {
                TestMachine::two_registers()
            },
            func,
        };
        input.fixup();
        input
    }

    /// Report `frequency`, one of `BLOCK_FREQUENCIES`, for every block in this
    /// function.
    pub fn set_block_frequencies(&mut self, frequency: BlockFrequency) {
        let index = BLOCK_FREQUENCIES
            .iter()
            .position(|f| *f == frequency)
            .expect("not a frequency a `TestFunction` can report");
        let index = u8::try_from(index).unwrap();
        for (_block, block_data) in self.func.blocks.iter_mut() {
            block_data.frequency = index;
        }
    }

    /// Report `frequency`, one of `BLOCK_FREQUENCIES`, for `block` alone.
    pub fn set_block_frequency(&mut self, block: Block, frequency: BlockFrequency) {
        let index = BLOCK_FREQUENCIES
            .iter()
            .position(|f| *f == frequency)
            .expect("not a frequency a `TestFunction` can report");
        self.func.blocks[block].frequency = u8::try_from(index).unwrap();
    }

    /// Report `remat` for every value in this function.
    pub fn set_remat_costs(&mut self, remat: Option<RematCost>) {
        let index = REMAT_COSTS
            .iter()
            .position(|r| *r == remat)
            .expect("not a remat cost a `TestFunction` can report");
        let index = u8::try_from(index).unwrap();
        for (_val, val_data) in self.func.values.iter_mut() {
            val_data.remat = index;
        }
    }

    /// A two-block input passing one value along an edge as a block argument,
    /// the argument's use constrained by `arg` and the parameter's by `param`:
    /// the smallest function with an argument-to-parameter affinity to find. On
    /// [`TestMachine::two_registers`], `Reg(rc0)` and `Reg(rc1)` conflict.
    pub fn with_block_arg_constraints(arg: OperandConstraint, param: OperandConstraint) -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let arg_val = Val::try_new(0).unwrap();
        let param_val = Val::try_new(1).unwrap();
        let def = Inst::try_new(0).unwrap();
        let target = Block::try_new(1).unwrap();

        func.values = PrimaryMap::new();
        for def in [
            ValDef::InstResult { inst: def, i: 0 },
            ValDef::BlockParam {
                block: target,
                i: 0,
            },
        ] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def,
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let op = |pos, kind, constraint, val| InstData::Op {
            operands: vec![Operand::new(pos, kind, constraint, val)],
            side_effects: true,
        };

        func.insts = PrimaryMap::new();
        for inst in [
            // The definition, a use to constrain the argument's span, then the
            // branch that passes it along.
            op(Position::Late, DefUse::Def, OperandConstraint::Any, arg_val),
            op(Position::Early, DefUse::Use, arg, arg_val),
            InstData::Branch {
                operands: vec![],
                targets: vec![BlockCall {
                    target,
                    args: vec![arg_val],
                }],
            },
            // A use to constrain the parameter's span, then a terminator of the
            // block's own so `ensure_terminators` does not take the use away.
            op(Position::Early, DefUse::Use, param, param_val),
            InstData::Op {
                operands: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        for block in [
            BlockData {
                params: vec![],
                insts: vec![inst(0), inst(1), inst(2)],
                frequency: 0,
            },
            BlockData {
                params: vec![param_val],
                insts: vec![inst(3), inst(4)],
                frequency: 0,
            },
        ] {
            func.blocks.push(&mut output, block).unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// [`TestInput::with_block_arg_constraints`] with the argument read on the
    /// stack, the parameter read in a register, and every value cheap enough to
    /// recompute: the edge fills the parameter by rematerializing the argument,
    /// atop the block, which the checker must rename after rather than before.
    pub fn with_a_rematerialized_block_arg() -> Self {
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();
        let mut input = Self::with_block_arg_constraints(
            OperandConstraint::Stack,
            OperandConstraint::Reg(class),
        );
        input.set_remat_costs(Some(RematCost::AlwaysRemat));
        input
    }

    /// An input with a critical edge that really needs an edit: `block0`
    /// branches to `block1` or `block2` and `block1` falls through to `block2`,
    /// so `block0`'s edge joins two successors to two predecessors. Its two
    /// predecessors pass different values in different registers and the
    /// parameter is read where `block1`'s already is, so only `block0`'s edge
    /// needs a move, and only an edge block can hold it.
    pub fn with_a_critical_edge() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let first = Val::try_new(0).unwrap();
        let param = Val::try_new(1).unwrap();
        let second = Val::try_new(2).unwrap();
        let merge = Block::try_new(2).unwrap();
        let r0 = RegClass::try_new(0).unwrap();
        let r1 = RegClass::try_new(1).unwrap();

        func.values = PrimaryMap::new();
        for def in [
            ValDef::InstResult {
                inst: Inst::try_new(0).unwrap(),
                i: 0,
            },
            ValDef::BlockParam { block: merge, i: 0 },
            ValDef::InstResult {
                inst: Inst::try_new(3).unwrap(),
                i: 0,
            },
        ] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def,
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let op = |pos, kind, constraint, val| InstData::Op {
            operands: vec![Operand::new(pos, kind, constraint, val)],
            side_effects: true,
        };
        let call = |target, args: &[Val]| BlockCall {
            target,
            args: args.to_vec(),
        };

        func.insts = PrimaryMap::new();
        for inst in [
            // `block0`: define a value in `r1` and branch two ways, passing it
            // along the edge straight to the merge.
            op(Position::Late, DefUse::Def, OperandConstraint::Any, first),
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(r1),
                first,
            ),
            InstData::Branch {
                operands: vec![],
                targets: vec![call(Block::try_new(1).unwrap(), &[]), call(merge, &[first])],
            },
            // `block1`: pass a value of its own in `r0` instead, giving the
            // merge its second predecessor.
            op(Position::Late, DefUse::Def, OperandConstraint::Any, second),
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(r0),
                second,
            ),
            InstData::Branch {
                operands: vec![],
                targets: vec![call(merge, &[second])],
            },
            // `block2`: read the parameter from `r0`, where `block1`'s value
            // already is.
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(r0),
                param,
            ),
            InstData::Op {
                operands: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        for block in [
            BlockData {
                params: vec![],
                insts: vec![inst(0), inst(1), inst(2)],
                frequency: 0,
            },
            BlockData {
                params: vec![],
                insts: vec![inst(3), inst(4), inst(5)],
                frequency: 0,
            },
            BlockData {
                params: vec![param],
                insts: vec![inst(6), inst(7)],
                frequency: 0,
            },
        ] {
            func.blocks.push(&mut output, block).unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A diamond whose merge block takes a parameter that spends part of its
    /// live range on the stack: `block1` and `block2` each pass `block0`'s
    /// value to `block3`, which reads it first in a register and then on the
    /// stack. A parameter is logically defined on its incoming edges, so this
    /// exposes a store placed on one of them but not the others.
    pub fn with_spilled_merge_param() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let arg_val = Val::try_new(0).unwrap();
        let param_val = Val::try_new(1).unwrap();
        let def = Inst::try_new(0).unwrap();
        let block = |i| Block::try_new(i).unwrap();
        let merge = block(3);

        func.values = PrimaryMap::new();
        for def in [
            ValDef::InstResult { inst: def, i: 0 },
            ValDef::BlockParam { block: merge, i: 0 },
        ] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def,
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let reg = OperandConstraint::Reg(
            RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap(),
        );
        let op = |pos, kind, constraint, val| InstData::Op {
            operands: vec![Operand::new(pos, kind, constraint, val)],
            side_effects: true,
        };
        let branch = |target, args| InstData::Branch {
            operands: vec![],
            targets: vec![BlockCall { target, args }],
        };

        func.insts = PrimaryMap::new();
        for inst in [
            // block0: define the value and fork.
            op(Position::Late, DefUse::Def, OperandConstraint::Any, arg_val),
            InstData::Branch {
                operands: vec![],
                targets: vec![
                    BlockCall {
                        target: block(1),
                        args: vec![],
                    },
                    BlockCall {
                        target: block(2),
                        args: vec![],
                    },
                ],
            },
            // block1 and block2: pass the value to the merge block.
            branch(merge, vec![arg_val]),
            branch(merge, vec![arg_val]),
            // `block3`: the parameter arrives in a register and is then read
            // off the stack, splitting its live range. The terminator is the
            // block's own so that `ensure_terminators` spares the stack use.
            op(Position::Early, DefUse::Use, reg, param_val),
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Stack,
                param_val,
            ),
            InstData::Op {
                operands: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        for block in [
            BlockData {
                params: vec![],
                insts: vec![inst(0), inst(1)],
                frequency: 0,
            },
            BlockData {
                params: vec![],
                insts: vec![inst(2)],
                frequency: 0,
            },
            BlockData {
                params: vec![],
                insts: vec![inst(3)],
                frequency: 0,
            },
            BlockData {
                params: vec![param_val],
                insts: vec![inst(4), inst(5), inst(6)],
                frequency: 0,
            },
        ] {
            func.blocks.push(&mut output, block).unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// An input with a move placed after a block's terminator.
    ///
    /// Two predecessors of a merge block pass *different* values for its one
    /// parameter, so at least one of the two edges needs a move to put the
    /// parameter where the other edge already leaves it. `first` is pinned to
    /// the second register right up to `block1`'s terminator and the merge
    /// block reads its parameter out of the first register, so that move
    /// cannot be hoisted to the start of `block1`: it belongs to the
    /// `block1 -> block3` edge.
    ///
    /// `block1` ends in an unconditional branch with no operands of its own,
    /// which is the one shape that lets move generation place that move after
    /// the predecessor's terminator rather than splitting the edge.
    pub fn with_a_move_after_an_unconditional_branch() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let first = Val::try_new(0).unwrap();
        let second = Val::try_new(1).unwrap();
        let param = Val::try_new(2).unwrap();
        let block = |i| Block::try_new(i).unwrap();
        let inst = |i| Inst::try_new(i).unwrap();
        let merge = block(3);
        let first_reg = RegClass::try_new(usize::from(TestMachine::FIRST_REG_CLASS)).unwrap();
        let second_reg = RegClass::try_new(usize::from(TestMachine::SECOND_REG_CLASS)).unwrap();

        func.values = PrimaryMap::new();
        for def in [
            ValDef::InstResult {
                inst: inst(0),
                i: 0,
            },
            ValDef::InstResult {
                inst: inst(1),
                i: 0,
            },
            ValDef::BlockParam { block: merge, i: 0 },
        ] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def,
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let op = |pos, kind, constraint, val| InstData::Op {
            operands: vec![Operand::new(pos, kind, constraint, val)],
            side_effects: true,
        };
        let branch = |target, args| InstData::Branch {
            operands: vec![],
            targets: vec![BlockCall { target, args }],
        };

        func.insts = PrimaryMap::new();
        for inst_data in [
            // block0: define both values and fork.
            op(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Reg(second_reg),
                first,
            ),
            op(Position::Late, DefUse::Def, OperandConstraint::Any, second),
            InstData::Branch {
                operands: vec![],
                targets: vec![
                    BlockCall {
                        target: block(1),
                        args: vec![],
                    },
                    BlockCall {
                        target: block(2),
                        args: vec![],
                    },
                ],
            },
            // block1: read `first` where it is defined, and then pass it to
            // the merge block, which wants it somewhere else.
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(second_reg),
                first,
            ),
            branch(merge, vec![first]),
            // block2: pass its own value for the same parameter.
            branch(merge, vec![second]),
            // block3: read the parameter. The terminator is the block's own so
            // that `ensure_terminators` does not append one after the read.
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(first_reg),
                param,
            ),
            InstData::Op {
                operands: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        func.blocks = PrimaryMap::new();
        for block_data in [
            BlockData {
                params: vec![],
                insts: vec![inst(0), inst(1), inst(2)],
                frequency: 0,
            },
            BlockData {
                params: vec![],
                insts: vec![inst(3), inst(4)],
                frequency: 0,
            },
            BlockData {
                params: vec![],
                insts: vec![inst(5)],
                frequency: 0,
            },
            BlockData {
                params: vec![param],
                insts: vec![inst(6), inst(7)],
                frequency: 0,
            },
        ] {
            func.blocks.push(&mut output, block_data).unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// An input whose entry block branches back to itself, passing a value of
    /// its own for its own parameter: the one shape where the checker's entry
    /// state is met against something rather than believed. `block0` reads its
    /// parameter, defines a value, and branches to itself or on to `block1`.
    pub fn with_a_self_looping_entry_block() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let param = Val::try_new(0).unwrap();
        let next = Val::try_new(1).unwrap();
        let entry = Block::try_new(0).unwrap();
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();

        func.values = PrimaryMap::new();
        for def in [
            ValDef::BlockParam { block: entry, i: 0 },
            ValDef::InstResult {
                inst: Inst::try_new(0).unwrap(),
                i: 0,
            },
        ] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def,
                        remat: 0,
                    },
                )
                .unwrap();
        }

        func.insts = PrimaryMap::new();
        for inst in [
            // `block0`: read the parameter and define its replacement on the
            // back edge.
            InstData::Op {
                operands: vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(class),
                        param,
                    ),
                    Operand::new(Position::Late, DefUse::Def, OperandConstraint::Any, next),
                ],
                side_effects: true,
            },
            InstData::Branch {
                operands: vec![],
                targets: vec![
                    BlockCall {
                        target: entry,
                        args: vec![next],
                    },
                    BlockCall {
                        target: Block::try_new(1).unwrap(),
                        args: vec![],
                    },
                ],
            },
            // `block1`: one more read, so the parameter is live out of the
            // entry block along both edges.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Stack,
                    param,
                )],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        for block in [
            BlockData {
                params: vec![param],
                insts: vec![inst(0), inst(1)],
                frequency: 0,
            },
            BlockData {
                params: vec![],
                insts: vec![inst(2), inst(3)],
                frequency: 0,
            },
        ] {
            func.blocks.push(&mut output, block).unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// An input whose entry block branches back to itself passing its own
    /// parameter straight back for its own parameter, and whose parameter is
    /// split at the top of the block.
    ///
    /// The gap atop the entry block is the one gap two paths share: the
    /// function's own arrival and the back edge both run it. The parameter is
    /// pinned to the one register that its own instruction's result takes over,
    /// so it is spilled and reloaded around that instruction, and the store
    /// lands in that gap. An edge into the entry block therefore cannot lean on
    /// that store the way an edge into any other block can.
    pub fn with_a_spilled_self_looping_entry_param() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let param = Val::try_new(0).unwrap();
        let clobber = Val::try_new(1).unwrap();
        let entry = Block::try_new(0).unwrap();
        let pinned = RegClass::try_new(usize::from(TestMachine::SECOND_REG_CLASS)).unwrap();

        func.values = PrimaryMap::new();
        for def in [
            ValDef::BlockParam { block: entry, i: 0 },
            ValDef::InstResult {
                inst: Inst::try_new(0).unwrap(),
                i: 0,
            },
        ] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::SECOND_REG_CLASS,
                        def,
                        remat: 0,
                    },
                )
                .unwrap();
        }

        func.insts = PrimaryMap::new();
        for inst in [
            // Read the parameter in the one register it is allowed, and define
            // a value that takes that same register over: the parameter has to
            // go somewhere else to survive the instruction.
            InstData::Op {
                operands: vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(pinned),
                        param,
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(0),
                        clobber,
                    ),
                ],
                side_effects: true,
            },
            // And read it there again afterwards, so it comes back.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Reg(pinned),
                    param,
                )],
                side_effects: true,
            },
            InstData::Branch {
                operands: vec![],
                targets: vec![BlockCall {
                    target: entry,
                    args: vec![param],
                }],
            },
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: vec![param],
                    insts: vec![inst(0), inst(1), inst(2)],
                    frequency: 0,
                },
            )
            .unwrap();

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A single-block input whose entry block takes two parameters, each read
    /// once. One place for both would be a contract no caller could meet, and
    /// no other fixture has a block with two parameters to say so with.
    pub fn with_two_entry_params() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let first = Val::try_new(0).unwrap();
        let second = Val::try_new(1).unwrap();
        let entry = Block::try_new(0).unwrap();

        func.values = PrimaryMap::new();
        for i in [0, 1] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def: ValDef::BlockParam { block: entry, i },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        func.insts = PrimaryMap::new();
        for inst in [
            InstData::Op {
                operands: vec![
                    Operand::new(Position::Early, DefUse::Use, OperandConstraint::Any, first),
                    Operand::new(Position::Early, DefUse::Use, OperandConstraint::Any, second),
                ],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: vec![first, second],
                    insts: vec![inst(0), inst(1)],
                    frequency: 0,
                },
            )
            .unwrap();

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A single-block input whose entry block takes three parameters of
    /// different shapes: a register group, a wide single register, and a
    /// narrow one from the other bank.
    ///
    /// Each is read off the stack, so the allocation ends up holding a slot
    /// group and slots of both of the machine's sizes at once. That is what
    /// lets a test claim a parameter arrives in a slot of the wrong size, or
    /// in a group where a single register belongs, without inventing a
    /// location the results never mention.
    pub fn with_entry_params_in_two_banks() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let entry = Block::try_new(0).unwrap();
        let classes = [
            TestMachine::FIRST_GROUP_CLASS,
            TestMachine::WIDE_REGS_CLASS,
            TestMachine::NARROW_REGS_CLASS,
        ];

        func.values = PrimaryMap::new();
        for (i, reg_class) in classes.into_iter().enumerate() {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class,
                        def: ValDef::BlockParam { block: entry, i },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        func.insts = PrimaryMap::new();
        for inst in [
            InstData::Op {
                operands: (0..classes.len())
                    .map(|i| {
                        Operand::new(
                            Position::Early,
                            DefUse::Use,
                            OperandConstraint::Stack,
                            Val::try_new(i).unwrap(),
                        )
                    })
                    .collect(),
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the reads.
            InstData::Op {
                operands: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: (0..classes.len())
                        .map(|i| Val::try_new(i).unwrap())
                        .collect(),
                    insts: vec![inst(0), inst(1)],
                    frequency: 0,
                },
            )
            .unwrap();

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::groups_and_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A single-block input whose entry block takes a parameter read twice at
    /// one point, once in a register and once on the stack, so several of its
    /// live-in pieces start at the function's first program point. The caller
    /// fills the one [`crate::Output::block_param_allocs`] reports; with no
    /// incoming edge to carry moves, the allocator must fill the rest.
    pub fn with_an_entry_param_read_two_ways() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let param = Val::try_new(0).unwrap();
        let entry = Block::try_new(0).unwrap();
        let narrow = RegClass::try_new(TestMachine::NARROW_REGS_CLASS.into()).unwrap();

        func.values = PrimaryMap::new();
        func.values
            .push(
                &mut output,
                ValData {
                    reg_class: TestMachine::NARROW_REGS_CLASS,
                    def: ValDef::BlockParam { block: entry, i: 0 },
                    remat: 0,
                },
            )
            .unwrap();

        func.insts = PrimaryMap::new();
        for inst in [
            InstData::Op {
                operands: vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(narrow),
                        param,
                    ),
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Stack,
                        param,
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Use,
                        OperandConstraint::Reg(narrow),
                        param,
                    ),
                ],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Stack,
                    param,
                )],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the reads.
            InstData::Op {
                operands: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: vec![param],
                    insts: vec![inst(0), inst(1), inst(2)],
                    frequency: 0,
                },
            )
            .unwrap();

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::groups_and_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A block parameter that lives in a spill slot, passed an argument that
    /// lives in a different one.
    ///
    /// `block0` defines a value, reads it off the stack, and passes it to
    /// `block1` as a block argument. `block1` reads its parameter off the
    /// stack, and then reads the argument off the stack again, which keeps the
    /// argument live into `block1` so that the two cannot share a slot.
    ///
    /// Only the edge can fill the parameter's slot: spill placement stores a
    /// value into its own home and never into another value's, so this is the
    /// shape where a missing destination half leaves the slot holding whatever
    /// was in it before.
    pub fn with_stack_param_and_arg() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let arg_val = Val::try_new(0).unwrap();
        let param_val = Val::try_new(1).unwrap();
        let def = Inst::try_new(0).unwrap();
        let target = Block::try_new(1).unwrap();

        func.values = PrimaryMap::new();
        for def in [
            ValDef::InstResult { inst: def, i: 0 },
            ValDef::BlockParam {
                block: target,
                i: 0,
            },
        ] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def,
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let op = |pos, kind, constraint, val| InstData::Op {
            operands: vec![Operand::new(pos, kind, constraint, val)],
            side_effects: true,
        };

        func.insts = PrimaryMap::new();
        for inst in [
            // block0: define the value, read it off the stack so that it is
            // there at the branch, and pass it along.
            op(Position::Late, DefUse::Def, OperandConstraint::Any, arg_val),
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Stack,
                arg_val,
            ),
            InstData::Branch {
                operands: vec![],
                targets: vec![BlockCall {
                    target,
                    args: vec![arg_val],
                }],
            },
            // block1: the parameter off the stack, then the argument off the
            // stack again. The last instruction is a terminator of the block's
            // own, so that `ensure_terminators` does not take the uses away.
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Stack,
                param_val,
            ),
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Stack,
                arg_val,
            ),
            InstData::Op {
                operands: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        for block in [
            BlockData {
                params: vec![],
                insts: vec![inst(0), inst(1), inst(2)],
                frequency: 0,
            },
            BlockData {
                params: vec![param_val],
                insts: vec![inst(3), inst(4), inst(5)],
                frequency: 0,
            },
        ] {
            func.blocks.push(&mut output, block).unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// Build the [`Input`] that this describes and hand it to `f`.
    ///
    /// The `Machine` has to be built to be borrowed, hence the callback.
    pub fn with_input<R>(&self, f: impl FnOnce(&Input<'_, TestFunction>) -> R) -> R {
        let machine = self.machine.build();
        f(&Input {
            options: &self.options,
            machine: &machine,
            func: &self.func,
        })
    }
}

/// A mutator for `InputOptions`.
///
/// Only the move-elimination level is mutated: `TestInput::fixup` guarantees
/// that the input is valid, so turning `validate_input` off would only lose
/// coverage of the validator.
#[derive(Default)]
pub struct InputOptionsMutator {}

impl Mutate<InputOptions> for InputOptionsMutator {
    fn mutate(
        &mut self,
        mutations: &mut mutatis::Candidates<'_>,
        options: &mut InputOptions,
    ) -> mutatis::Result<()> {
        mutations.mutation(|ctx| {
            options.move_elimination_level = if ctx.shrink() {
                // Doing less move elimination is the simpler test case, so
                // shrink towards `None`.
                match options.move_elimination_level {
                    MoveEliminationLevel::None => {
                        return Err(mutatis::error::Error::exhausted());
                    }
                    MoveEliminationLevel::Local => MoveEliminationLevel::None,
                    MoveEliminationLevel::Global => {
                        if ctx.rng().gen_bool() {
                            MoveEliminationLevel::None
                        } else {
                            MoveEliminationLevel::Local
                        }
                    }
                }
            } else {
                gen_move_elimination_level(ctx)?
            };
            Ok(())
        })
    }
}

impl Generate<InputOptions> for InputOptionsMutator {
    fn generate(&mut self, ctx: &mut mutatis::Context) -> mutatis::Result<InputOptions> {
        Ok(InputOptions {
            move_elimination_level: gen_move_elimination_level(ctx)?,
            ..InputOptions::default()
        })
    }
}

impl DefaultMutate for InputOptions {
    type DefaultMutate = InputOptionsMutator;
}

#[derive(Default)]
pub struct TestInputMutator {}

impl Mutate<TestInput> for TestInputMutator {
    fn mutate(
        &mut self,
        mutations: &mut mutatis::Candidates<'_>,
        input: &mut TestInput,
    ) -> mutatis::Result<()> {
        let result = (|| -> mutatis::Result<()> {
            InputOptionsMutator::default().mutate(mutations, &mut input.options)?;
            TestMachineMutator::default().mutate(mutations, &mut input.machine)?;
            TestFunctionMutator::default().mutate(mutations, &mut input.func)?;
            Ok(())
        })();

        input.fixup();
        result
    }
}

impl Generate<TestInput> for TestInputMutator {
    fn generate(&mut self, context: &mut mutatis::Context) -> mutatis::Result<TestInput> {
        let mut input = TestInput {
            options: InputOptionsMutator::default().generate(context)?,
            machine: TestMachineMutator::default().generate(context)?,
            func: TestFunctionMutator::default().generate(context)?,
        };
        input.fixup();
        Ok(input)
    }
}

impl DefaultMutate for TestInput {
    type DefaultMutate = TestInputMutator;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        error::{Error, InternalError},
        validation,
    };
    use mutatis::check::{Check, CheckResult};
    use std::{format, string::String};

    /// Check that `func` is a well-formed function in valid SSA form, as
    /// `TestFunction::fixup` is supposed to guarantee.
    fn check_ssa(machine: &Machine, func: &TestFunction) -> Result<(), String> {
        let mut output = OutputInner::<u32>::new();
        let options = InputOptions::default();
        let input = Input {
            options: &options,
            machine,
            func,
        };
        if validation::validate(&input, &mut output).is_err() {
            return Err(format!("invalid input: {:?}", output.take_error()));
        }

        // `ValData::def` describes where a value is defined, which is a
        // `TestFunction` concept that the input traits have no notion of.
        // `validate` has already established that these are exactly the
        // function's definition sites, so all that is left is to check that
        // each value's own record of its definition agrees.
        for (block, block_data) in func.blocks.iter() {
            for (i, &param) in block_data.params.iter().enumerate() {
                let expected = ValDef::BlockParam { block, i };
                let actual = &func.values[param].def;
                if *actual != expected {
                    return Err(format!(
                        "{param:?} is {block:?}'s parameter {i}, but its `ValData::def` \
                         says {actual:?}",
                    ));
                }
            }
            for &inst in &block_data.insts {
                let mut i = 0;
                for op in func.insts[inst].operands() {
                    if !matches!(op.kind(), DefUse::Def) {
                        continue;
                    }
                    let expected = ValDef::InstResult { inst, i };
                    let actual = &func.values[op.val()].def;
                    if *actual != expected {
                        return Err(format!(
                            "{:?} is definition {i} of {inst:?}, but its `ValData::def` \
                             says {actual:?}",
                            op.val(),
                        ));
                    }
                    i += 1;
                }
            }
        }

        // Every block reports one of the frequencies it can report, whatever
        // the mutator did to the index.
        for (block, _) in func.blocks() {
            let frequency = func.block(block).frequency();
            if !BLOCK_FREQUENCIES.contains(&frequency) {
                return Err(format!(
                    "{block:?} reports a frequency of {frequency:?}, which is not one of \
                     {BLOCK_FREQUENCIES:?}",
                ));
            }
        }

        // `fixup` reaches a fixed point.
        let mut again = func.clone();
        again.fixup();
        if hash(&again) != hash(func) {
            return Err(format!(
                "`fixup` is not idempotent; running it a second time gives:\n{}",
                again.display(),
            ));
        }

        Ok(())
    }

    #[test]
    fn fixup_produces_valid_ssa() -> CheckResult<TestInput> {
        Check::new().iters(10_000).run(|input: &TestInput| {
            check_ssa(&input.machine.build(), &input.func)?;

            // `TestInput::fixup` reaches a fixed point too, and not just the
            // function's half of it: the operand constraints it rewrites refer
            // to the machine, so a second pass has to leave them alone.
            let mut again = input.clone();
            again.fixup();
            if hash(&again) != hash(input) {
                return Err(format!(
                    "`TestInput::fixup` is not idempotent; running it a second time gives:\n{again:#?}"
                ));
            }

            Ok(())
        })
    }

    /// A `TestInput` asks for a level of move elimination, and `with_input`
    /// hands whichever one it holds down to the allocator.
    #[test]
    fn with_input_reports_the_move_elimination_level() {
        let mut input = TestInput::default();
        assert_eq!(
            input.options.move_elimination_level,
            InputOptions::default().move_elimination_level,
        );

        for level in [
            MoveEliminationLevel::None,
            MoveEliminationLevel::Local,
            MoveEliminationLevel::Global,
        ] {
            input.options.move_elimination_level = level;
            input.with_input(|input| assert_eq!(input.options.move_elimination_level, level));
        }
    }

    /// `InputOptionsMutator` really does vary the move-elimination level, so
    /// that the checks which generate `TestInput`s exercise all of them.
    #[test]
    fn generates_every_move_elimination_level() {
        let mut session = mutatis::Session::new().seed(0);
        let mut seen = Vec::new();
        for _ in 0..100 {
            let options: InputOptions = session.generate().unwrap();
            if !seen.contains(&options.move_elimination_level) {
                seen.push(options.move_elimination_level);
            }
        }
        assert_eq!(seen.len(), 3, "only generated {seen:?}");
    }

    /// Every machine that `TestMachine` can describe is one that
    /// `MachineBuilder` accepts, and one whose classes can all be intersected.
    ///
    /// This is what the `unwrap`s in `TestMachine::build` rest on, and what holds
    /// the capacity argument next to `TestMachine`'s ceilings to account: running
    /// out of register classes while closing the class list under intersection
    /// would show up here as a `MachineCapacityExceeded` from `finish`.
    #[test]
    fn every_test_machine_builds() -> CheckResult<TestMachine> {
        Check::new()
            .iters(10_000)
            .run(|test_machine: &TestMachine| -> Result<(), String> {
                let machine = test_machine.build();

                let num_classes = machine.num_user_classes();
                if num_classes != test_machine.num_classes() {
                    return Err(format!(
                        "the machine defines {num_classes} classes, but the description says \
                         {}",
                        test_machine.num_classes(),
                    ));
                }
                if num_classes == 0 {
                    return Err(String::from("the machine defines no register classes"));
                }

                // The class list is closed under intersection, so asking about
                // any pair of classes an operand could name has to be answerable
                // rather than an out-of-bounds index.
                for a in 0..num_classes {
                    for b in 0..num_classes {
                        let a = RegClass::try_new(a).unwrap();
                        let b = RegClass::try_new(b).unwrap();
                        assert_eq!(
                            a.intersect(&machine, b),
                            b.intersect(&machine, a),
                            "intersecting classes is symmetric",
                        );
                    }
                }

                // `fixup` reaches a fixed point.
                let mut again = test_machine.clone();
                again.fixup();
                if hash(&again) != hash(test_machine) {
                    return Err(format!(
                        "`TestMachine::fixup` is not idempotent; running it a second time \
                         gives:\n{again:#?}",
                    ));
                }

                Ok(())
            })
    }

    /// A register count set with `set_regs_per_bank` survives every later
    /// mutation, and every register it adds reaches a class.
    ///
    /// This is the whole reason the count lives on `TestMachine` rather than
    /// being applied by the caller: `TestInputMutator` runs `fixup` after
    /// every mutation, and `fixup` is what decides how many registers a bank
    /// has. Padding without the class pass would be just as useless -- the
    /// allocator would see registers that no operand constraint can name --
    /// so both halves are checked here.
    #[test]
    fn a_register_count_survives_mutation() {
        const REGS: usize = 9;

        let check = |input: &TestInput, when: &str| {
            for (i, bank) in input.machine.banks.iter().enumerate() {
                assert_eq!(
                    bank.regs.len(),
                    REGS,
                    "bank {i} has {} registers {when}, not {REGS}",
                    bank.regs.len(),
                );
                for class in &bank.classes {
                    if let TestClassMembers::Regs(regs) = &class.members {
                        assert_eq!(
                            regs.len(),
                            REGS,
                            "a class of bank {i} holds {} of its {REGS} registers {when}",
                            regs.len(),
                        );
                    }
                }
            }
            // And the machine still builds, which is what says the widened
            // description is a legal one.
            input.machine.build();
        };

        // From a machine with register groups as well as the default one: a
        // bank with groups is where padding could go wrong, since a class of
        // groups is deliberately left as it was.
        for machine in [TestMachine::default(), TestMachine::groups_and_registers()] {
            let mut input = TestInput::default();
            input.machine = machine;
            input.machine.set_regs_per_bank(REGS);
            input.fixup();
            check(&input, "to begin with");

            let mut session = mutatis::Session::new().seed(0);
            for i in 0..1_000 {
                session.mutate(&mut input).unwrap();
                check(&input, &format!("after mutation {i}"));
            }
        }
    }

    /// Build a valid function of `num_blocks` blocks with `insts_per_block`
    /// instructions each, for the checks below to break in specific ways.
    ///
    /// `fixup` is what makes it valid; this only has to hand it a layout of the
    /// requested shape to lay out, since `ensure_unique_insts_in_layout` clones
    /// an instruction for every slot in the layout.
    fn valid_func(num_blocks: usize, insts_per_block: usize) -> TestFunction {
        assert!(num_blocks > 0);
        assert!(insts_per_block > 0);

        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();
        func.blocks = PrimaryMap::new();
        for _ in 0..num_blocks {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts: vec![Inst::try_new(0).unwrap(); insts_per_block],
                        frequency: 0,
                    },
                )
                .unwrap();
        }
        func.fixup();

        assert_eq!(func.len_blocks(), num_blocks);
        assert_eq!(func.len_insts(), num_blocks * insts_per_block);
        assert_eq!(check_ssa(&test_machine(), &func), Ok(()));
        func
    }

    /// `with_use_constraints` is only useful if `fixup` leaves the operands it
    /// writes down alone, so check the shape it produces rather than trusting
    /// it.
    #[test]
    fn use_constraints_survive_fixup() {
        let rc = |i| OperandConstraint::Reg(RegClass::try_new(i).unwrap());
        let constraints = [rc(0), rc(1), OperandConstraint::Stack];
        let input = TestInput::with_use_constraints(&constraints);

        assert_eq!(check_ssa(&input.machine.build(), &input.func), Ok(()));
        assert_eq!(input.func.len_values(), 1);
        assert_eq!(input.func.len_insts(), constraints.len() + 2);

        let val = Val::try_new(0).unwrap();
        for (i, &expected) in constraints.iter().enumerate() {
            let inst = Inst::try_new(i + 1).unwrap();
            let operands: Vec<Operand> = input.func.inst(inst).operands().collect();
            assert_eq!(operands.len(), 1);
            assert_eq!(operands[0].kind(), DefUse::Use);
            assert_eq!(operands[0].val(), val);
            assert_eq!(operands[0].constraint(), expected);
        }
    }

    /// The machine that the checks below validate against.
    ///
    /// A `valid_func`'s operands are all unconstrained, so the machine hardly
    /// matters to them; the smallest one `TestMachine` can describe keeps the
    /// checks about the function.
    fn test_machine() -> Machine {
        TestMachine::default().build()
    }

    /// Validate `func` and return the error that it is rejected with.
    fn expect_invalid(func: &impl InputFunction) -> Error {
        expect_invalid_with(&test_machine(), func)
    }

    fn expect_invalid_with(machine: &Machine, func: &impl InputFunction) -> Error {
        let mut output = OutputInner::<u32>::new();
        let options = InputOptions::default();
        let input = Input {
            options: &options,
            machine,
            func,
        };
        assert!(
            validation::validate(&input, &mut output).is_err(),
            "expected validation to reject this function",
        );
        match output.take_error() {
            InternalError::Error(e) => e,
            InternalError::EntityReprTooSmall => {
                panic!("validation does not report a too-small entity representation")
            }
        }
    }

    /// Assert that validation rejects `$func` with an error matching
    /// `$pattern`. `Error` is not `PartialEq`, so this matches rather than
    /// compares, and reports what it got when the match fails.
    macro_rules! assert_invalid {
        ( $func:expr, $pattern:pat $( if $guard:expr )? $(,)? ) => {{
            let actual = expect_invalid($func);
            assert!(
                matches!(actual, $pattern $( if $guard )?),
                "expected `{}`, got {actual:?}",
                stringify!($pattern),
            );
        }};
    }

    #[test]
    fn every_instruction_reports_the_block_it_lies_within() {
        let func = valid_func(3, 2);
        for (block, block_data) in func.blocks.iter() {
            // Both ways of reaching an instruction agree about its block: the
            // one that walks a block's layout, and the one that looks the
            // instruction up by index.
            for (inst, input_inst) in func.block(block).insts() {
                assert_eq!(input_inst.block(), block);
                assert_eq!(func.inst(inst).block(), block);
            }
            assert_eq!(
                block_data.insts.len(),
                func.block(block).insts().count(),
                "{block:?}'s layout is what `insts` walks",
            );
        }
    }

    #[test]
    fn reject_an_instruction_that_names_the_wrong_block() {
        let mut func = valid_func(2, 1);
        let block = Block::try_new(1).unwrap();
        let inst = func.blocks[Block::try_new(0).unwrap()].insts[0];

        func.inst_blocks[inst] = Some(block);

        assert_invalid!(
            &func,
            Error::InvalidInstBlock { inst: i, block: b } if i == inst && b == block,
        );
    }

    #[test]
    fn reject_an_instruction_that_no_block_contains() {
        let mut func = valid_func(1, 2);
        let block = Block::try_new(0).unwrap();
        let inst = func.blocks[block].insts.pop().unwrap();

        // The instruction is still one that the function declares, so
        // `InputFunction::inst` still hands it out; it is just no longer in any
        // block's layout.
        assert_eq!(func.len_insts(), 2);

        assert_invalid!(&func, Error::InstInNoBlock { inst: i } if i == inst);
    }

    #[test]
    fn reject_an_instruction_outside_the_index_space() {
        let mut func = valid_func(1, 1);
        let block = Block::try_new(0).unwrap();

        // One past the last instruction the function declares, and contiguous
        // with the block's existing instruction, so that it is the index space
        // check that rejects it and not the contiguity check.
        let inst = Inst::try_new(func.len_insts()).unwrap();
        func.blocks[block].insts.push(inst);

        assert_invalid!(&func, Error::InstOutOfBounds { inst: i } if i == inst);
    }

    #[test]
    fn reject_an_operand_naming_a_class_the_machine_does_not_define() {
        let mut func = valid_func(1, 1);
        let block = Block::try_new(0).unwrap();
        let inst = func.blocks[block].insts[0];

        // One past the last class the machine defines, which is a class the
        // machine could have defined and so is representable in the packed
        // operand.
        let machine = test_machine();
        let class = RegClass::try_new(machine.num_user_classes()).unwrap();

        let operand = &mut func.insts[inst].operands_mut()[0];
        *operand = Operand::new(
            operand.pos(),
            operand.kind(),
            OperandConstraint::Reg(class),
            operand.val(),
        );

        assert_invalid!(
            &func,
            Error::InvalidRegClass { inst: i, operand: 0 } if i == inst,
        );
    }

    /// The class one *below* that is a class the machine really does define, so
    /// the check above is about the bound and not about `Reg` constraints in
    /// general.
    #[test]
    fn accept_an_operand_naming_the_last_class_the_machine_defines() {
        let mut func = valid_func(1, 1);
        let block = Block::try_new(0).unwrap();
        let inst = func.blocks[block].insts[0];

        let machine = test_machine();
        let class = RegClass::try_new(machine.num_user_classes() - 1).unwrap();

        let operand = &mut func.insts[inst].operands_mut()[0];
        *operand = Operand::new(
            operand.pos(),
            operand.kind(),
            OperandConstraint::Reg(class),
            operand.val(),
        );

        assert_eq!(check_ssa(&machine, &func), Ok(()));
    }

    #[test]
    fn reject_a_value_in_a_class_the_machine_does_not_define() {
        let mut func = valid_func(1, 1);

        // One past the last class the machine defines, as in the operand case
        // above.
        let machine = test_machine();
        func.values[Val::try_new(0).unwrap()].reg_class =
            u8::try_from(machine.num_user_classes()).unwrap();

        assert_invalid!(&func, Error::InvalidValRegClass { val } if val.index() == 0);
    }

    #[test]
    fn reject_an_operand_whose_class_cannot_hold_its_value() {
        let mut func = valid_func(1, 1);
        let block = Block::try_new(0).unwrap();
        let inst = func.blocks[block].insts[0];

        // `rc0` and `rc1` share no register, so constraining a value in one of
        // them to the other leaves the operand with nowhere to go.
        let machine = TestMachine::two_registers().build();
        let operand = &mut func.insts[inst].operands_mut()[0];
        func.values[operand.val()].reg_class = 0;
        *operand = Operand::new(
            operand.pos(),
            operand.kind(),
            OperandConstraint::Reg(RegClass::try_new(1).unwrap()),
            operand.val(),
        );

        let actual = expect_invalid_with(&machine, &func);
        assert!(
            matches!(actual, Error::IncompatibleRegClass { inst: i, operand: 0 } if i == inst),
            "expected an `IncompatibleRegClass`, got {actual:?}",
        );
    }

    /// The same operand against a value in `rc2`, which holds both registers
    /// and so contains `rc1`, showing that the check above is about where the
    /// constraint's registers sit relative to the value's and not about `Reg`
    /// constraints in general.
    #[test]
    fn accept_an_operand_whose_class_is_inside_its_value() {
        let mut func = valid_func(1, 1);
        let block = Block::try_new(0).unwrap();
        let inst = func.blocks[block].insts[0];

        let machine = TestMachine::two_registers().build();
        for (_val, val_data) in func.values.iter_mut() {
            val_data.reg_class = TestMachine::BOTH_REGS_CLASS;
        }
        let operand = &mut func.insts[inst].operands_mut()[0];
        *operand = Operand::new(
            operand.pos(),
            operand.kind(),
            OperandConstraint::Reg(RegClass::try_new(1).unwrap()),
            operand.val(),
        );

        assert_eq!(check_ssa(&machine, &func), Ok(()));
    }

    /// ... and overlapping is not enough: `rc2` holds a register that a value
    /// in `rc0` may not live in, and allocation would be free to hand that
    /// register out.
    #[test]
    fn reject_an_operand_whose_class_is_wider_than_its_value() {
        let mut func = valid_func(1, 1);
        let block = Block::try_new(0).unwrap();
        let inst = func.blocks[block].insts[0];

        let machine = TestMachine::two_registers().build();
        let operand = &mut func.insts[inst].operands_mut()[0];
        func.values[operand.val()].reg_class = 0;
        *operand = Operand::new(
            operand.pos(),
            operand.kind(),
            OperandConstraint::Reg(
                RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap(),
            ),
            operand.val(),
        );

        let actual = expect_invalid_with(&machine, &func);
        assert!(
            matches!(actual, Error::IncompatibleRegClass { inst: i, operand: 0 } if i == inst),
            "expected an `IncompatibleRegClass`, got {actual:?}",
        );
    }

    /// A machine with one register the allocator owns and one it does not,
    /// plus the two classes that let an operand name either the pair or the
    /// non-allocatable register alone.
    ///
    /// `TestMachine` cannot describe this: it only ever puts allocatable
    /// registers in a class, so the shape these checks are about has to be
    /// built by hand.
    fn machine_with_a_non_allocatable_class() -> Machine {
        let mut builder = MachineBuilder::new();
        let bank = builder
            .declare_reg_bank(SpillSlotSize::from_log2(0))
            .unwrap();

        let reg = builder
            .define_reg(
                bank,
                RegUnit::try_new(0).unwrap()..RegUnit::try_new(1).unwrap(),
            )
            .unwrap();
        let non_allocatable = builder.define_non_allocatable_reg(bank).unwrap();

        // Class 0 holds both, and is what a value in this machine lives in.
        // Class 1 holds only the register the allocator may not hand out.
        builder
            .define_reg_class(bank, 1.0, [reg, non_allocatable])
            .unwrap();
        builder
            .define_reg_class(bank, 1.0, [non_allocatable])
            .unwrap();

        builder.finish().unwrap()
    }

    /// A use may name a non-allocatable register --- that is what those
    /// registers are for --- but a definition constrained to a class with no
    /// register the allocator owns has nowhere to go, so it is the input that
    /// is wrong and not any allocation of it.
    #[test]
    fn reject_a_definition_pinned_to_a_non_allocatable_register() {
        let mut func = valid_func(1, 1);
        let block = Block::try_new(0).unwrap();
        let inst = func.blocks[block].insts[0];

        let machine = machine_with_a_non_allocatable_class();
        let operand = &mut func.insts[inst].operands_mut()[0];
        assert_eq!(operand.kind(), DefUse::Def);
        func.values[operand.val()].reg_class = 0;
        *operand = Operand::new(
            operand.pos(),
            operand.kind(),
            OperandConstraint::Reg(RegClass::try_new(1).unwrap()),
            operand.val(),
        );

        let actual = expect_invalid_with(&machine, &func);
        assert!(
            matches!(
                actual,
                Error::DefInNonAllocatableRegClass { inst: i, operand: 0 } if i == inst,
            ),
            "expected a `DefInNonAllocatableRegClass`, got {actual:?}",
        );
    }

    /// The same constraint on a use of that value, which is exactly how an
    /// instruction says it reads the stack pointer.
    #[test]
    fn accept_a_use_pinned_to_a_non_allocatable_register() {
        let machine = machine_with_a_non_allocatable_class();
        let mut input = TestInput::with_use_constraints(&[OperandConstraint::Reg(
            RegClass::try_new(1).unwrap(),
        )]);
        for (_val, val_data) in input.func.values.iter_mut() {
            val_data.reg_class = 0;
        }

        assert_eq!(check_ssa(&machine, &input.func), Ok(()));
    }

    /// ... and so is a definition in a class that holds a register the
    /// allocator owns as well, which is the whole point of checking the class
    /// rather than the mere presence of a non-allocatable member.
    #[test]
    fn accept_a_definition_in_a_class_that_also_holds_an_allocatable_register() {
        let mut func = valid_func(1, 1);
        let block = Block::try_new(0).unwrap();
        let inst = func.blocks[block].insts[0];

        let machine = machine_with_a_non_allocatable_class();
        let operand = &mut func.insts[inst].operands_mut()[0];
        func.values[operand.val()].reg_class = 0;
        *operand = Operand::new(
            operand.pos(),
            operand.kind(),
            OperandConstraint::Reg(RegClass::try_new(0).unwrap()),
            operand.val(),
        );

        assert_eq!(check_ssa(&machine, &func), Ok(()));
    }

    #[test]
    fn reject_a_block_argument_in_a_different_class_than_its_parameter() {
        let mut input =
            TestInput::with_block_arg_constraints(OperandConstraint::Any, OperandConstraint::Any);

        // Both values are in `rc2` when this input is built; move the parameter
        // out from under the argument.
        let param = Val::try_new(1).unwrap();
        assert!(matches!(
            input.func.values[param].def,
            ValDef::BlockParam { .. }
        ));
        input.func.values[param].reg_class = 0;

        let actual = expect_invalid_with(&input.machine.build(), &input.func);
        assert!(
            matches!(
                actual,
                Error::BlockArgRegClassMismatch {
                    block,
                    successor: 0,
                    index: 0,
                } if block.index() == 0
            ),
            "expected a `BlockArgRegClassMismatch`, got {actual:?}",
        );
    }

    /// Where `func_with_a_reuse`'s one `Reuse` is.
    fn the_reuse(func: &TestFunction) -> (Inst, usize) {
        func.insts
            .iter()
            .find_map(|(inst, inst_data)| {
                let j = inst_data
                    .operands()
                    .iter()
                    .position(|op| matches!(op.constraint(), OperandConstraint::Reuse(_)))?;
                Some((inst, j))
            })
            .expect("`func_with_a_reuse` has a reuse operand")
    }

    /// A single-block function whose second instruction defines a value that
    /// must reuse the register of one of its own operands, tying the two values
    /// together.
    fn func_with_a_reuse() -> TestFunction {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let inst = |i| Inst::try_new(i).unwrap();
        let val = |i| Val::try_new(i).unwrap();

        func.values = PrimaryMap::new();
        for i in 0..2 {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: 0,
                        def: ValDef::InstResult {
                            inst: inst(i),
                            i: 0,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        func.insts = PrimaryMap::new();
        for inst_data in [
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    val(0),
                )],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![
                    Operand::new(Position::Early, DefUse::Use, OperandConstraint::Any, val(0)),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(0),
                        val(1),
                    ),
                ],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        func.blocks = PrimaryMap::new();
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: vec![],
                    insts: vec![inst(0), inst(1)],
                    frequency: 0,
                },
            )
            .unwrap();

        func.fixup();
        func
    }

    /// A `Reuse` may only name a use: reusing a definition would give one
    /// location to two values the same instruction writes.
    #[test]
    fn reject_a_reuse_of_a_def() {
        let mut func = func_with_a_reuse();

        let (inst, j, target) = func
            .insts
            .iter()
            .find_map(|(inst, inst_data)| {
                let operands = inst_data.operands();
                let j = operands
                    .iter()
                    .position(|op| matches!(op.constraint(), OperandConstraint::Reuse(_)))?;
                let OperandConstraint::Reuse(target) = operands[j].constraint() else {
                    unreachable!("just found this operand by its `Reuse` constraint")
                };
                Some((inst, j, target))
            })
            .expect("`func_with_a_reuse` has a reuse operand");

        // Make the named operand a def, leaving the reuse on it. `fixup` does
        // not run, so nothing repairs this behind our back.
        let operands = func.insts[inst].operands_mut();
        let op = &mut operands[target];
        assert_eq!(op.kind(), DefUse::Use);
        *op = Operand::new(op.pos(), DefUse::Def, op.constraint(), op.val());

        let actual = expect_invalid_with(&TestMachine::two_registers().build(), &func);
        assert!(
            matches!(
                actual,
                Error::InvalidReuse { inst: i, operand } if i == inst && operand == j
            ),
            "expected an `InvalidReuse`, got {actual:?}",
        );
    }

    /// A `Reuse` on an early def is rejected: it is written while the use it
    /// reuses is still being read.
    #[test]
    fn reject_a_reuse_on_an_early_def() {
        let mut func = func_with_a_reuse();
        let (inst, j) = the_reuse(&func);

        let op = &mut func.insts[inst].operands_mut()[j];
        *op = Operand::new(Position::Early, op.kind(), op.constraint(), op.val());

        let actual = expect_invalid_with(&TestMachine::two_registers().build(), &func);
        assert!(
            matches!(
                actual,
                Error::InvalidReuse { inst: i, operand } if i == inst && operand == j
            ),
            "expected an `InvalidReuse`, got {actual:?}",
        );
    }

    /// A `Reuse` naming a late use is rejected: the use would be read after
    /// the definition overwrote it.
    #[test]
    fn reject_a_reuse_of_a_late_use() {
        let mut func = func_with_a_reuse();
        let (inst, j) = the_reuse(&func);
        let OperandConstraint::Reuse(target) = func.insts[inst].operands()[j].constraint() else {
            unreachable!("just found this operand by its `Reuse` constraint")
        };

        let op = &mut func.insts[inst].operands_mut()[target];
        *op = Operand::new(Position::Late, op.kind(), op.constraint(), op.val());

        let actual = expect_invalid_with(&TestMachine::two_registers().build(), &func);
        assert!(
            matches!(
                actual,
                Error::InvalidReuse { inst: i, operand } if i == inst && operand == j
            ),
            "expected an `InvalidReuse`, got {actual:?}",
        );
    }

    /// A `Reuse` naming a stack-constrained use is rejected: two values can
    /// only share a register.
    #[test]
    fn reject_a_reuse_of_a_stack_constrained_use() {
        let mut func = func_with_a_reuse();
        let (inst, j) = the_reuse(&func);
        let OperandConstraint::Reuse(target) = func.insts[inst].operands()[j].constraint() else {
            unreachable!("just found this operand by its `Reuse` constraint")
        };

        let op = &mut func.insts[inst].operands_mut()[target];
        *op = Operand::new(op.pos(), op.kind(), OperandConstraint::Stack, op.val());

        let actual = expect_invalid_with(&TestMachine::two_registers().build(), &func);
        assert!(
            matches!(
                actual,
                Error::InvalidReuse { inst: i, operand } if i == inst && operand == j
            ),
            "expected an `InvalidReuse`, got {actual:?}",
        );
    }

    /// A second `Reuse` naming a claimed operand is rejected: both definitions
    /// would want the one location.
    #[test]
    fn reject_a_reuse_of_a_claimed_target() {
        let mut func = func_with_a_reuse();
        let (inst, j) = the_reuse(&func);
        let reuse = func.insts[inst].operands()[j].constraint();

        // Copy the reuse onto a second definition, so two name one target.
        let val = Val::try_new(func.values.len()).unwrap();
        func.values
            .push(
                &mut OutputInner::<u32>::new(),
                ValData {
                    reg_class: TestMachine::BOTH_REGS_CLASS,
                    def: ValDef::InstResult { inst, i: 1 },
                    remat: 0,
                },
            )
            .unwrap();
        let operands = match &mut func.insts[inst] {
            InstData::Op { operands, .. } | InstData::Branch { operands, .. } => operands,
        };
        operands.push(Operand::new(Position::Late, DefUse::Def, reuse, val));
        let second = operands.len() - 1;

        let actual = expect_invalid_with(&TestMachine::two_registers().build(), &func);
        assert!(
            matches!(
                actual,
                Error::InvalidReuse { inst: i, operand } if i == inst && operand == second
            ),
            "expected an `InvalidReuse`, got {actual:?}",
        );
    }

    /// `fixup` is happy to tie a definition to a use whose value outlives the
    /// instruction: the allocator splits the survivor around the copy.
    #[test]
    fn fixup_keeps_a_reuse_of_a_surviving_value() {
        let mut input = TestInput::with_reuse_def(OperandConstraint::Any);
        let (inst, j) = the_reuse(&input.func);
        let target = match input.func.insts[inst].operands()[j].constraint() {
            OperandConstraint::Reuse(target) => target,
            c => panic!("`the_reuse` found a reuse, got {c:?}"),
        };
        let reused = input.func.insts[inst].operands()[target].val();

        // Read the reused value once more, from the terminator, so that it
        // outlives the instruction that wanted to overwrite it.
        let last = *input.func.blocks[Block::try_new(0).unwrap()]
            .insts
            .last()
            .unwrap();
        match &mut input.func.insts[last] {
            InstData::Op { operands, .. } | InstData::Branch { operands, .. } => operands,
        }
        .push(Operand::new(
            Position::Early,
            DefUse::Use,
            OperandConstraint::Any,
            reused,
        ));
        input.fixup();

        let kept = input
            .func
            .insts
            .iter()
            .flat_map(|(_inst, inst_data)| inst_data.operands())
            .any(|op| matches!(op.constraint(), OperandConstraint::Reuse(_)));
        assert!(
            kept,
            "`fixup` dropped a reuse of a value that outlives the instruction",
        );
    }

    /// Whatever the generator produced, `fixup` never leaves a `Reuse` in a
    /// shape the validator rejects.
    #[test]
    fn fixup_repairs_an_illegal_reuse() {
        for kind in [DefUse::Def, DefUse::Use] {
            for pos in [Position::Early, Position::Late] {
                let mut func = func_with_a_reuse();
                for (_inst, inst_data) in func.insts.iter_mut() {
                    for op in inst_data.operands_mut() {
                        *op = Operand::new(pos, kind, op.constraint(), op.val());
                    }
                }

                func.fixup();

                for (_inst, inst_data) in func.insts.iter() {
                    let operands = inst_data.operands();
                    for op in operands {
                        let OperandConstraint::Reuse(target) = op.constraint() else {
                            continue;
                        };
                        assert_eq!(op.kind(), DefUse::Def, "`fixup` left a reuse on a use");
                        assert_eq!(op.pos(), Position::Late, "`fixup` left an early reuse");
                        assert_eq!(
                            operands[target].kind(),
                            DefUse::Use,
                            "`fixup` left a reuse naming a def",
                        );
                        assert_eq!(
                            operands[target].pos(),
                            Position::Early,
                            "`fixup` left a reuse naming a late use",
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn reject_a_reuse_whose_operands_are_in_different_classes() {
        let mut func = func_with_a_reuse();

        let (inst, j) = func
            .insts
            .iter()
            .find_map(|(inst, inst_data)| {
                let j = inst_data
                    .operands()
                    .iter()
                    .position(|op| matches!(op.constraint(), OperandConstraint::Reuse(_)))?;
                Some((inst, j))
            })
            .expect("`func_with_a_reuse` has a reuse operand");

        let operands = func.insts[inst].operands();
        let OperandConstraint::Reuse(target) = operands[j].constraint() else {
            unreachable!("just found this operand by its `Reuse` constraint")
        };
        let (reusing, reused) = (operands[j].val(), operands[target].val());
        assert_ne!(reusing, reused);

        // `fixup` put both in one class; take the reusing operand's value out
        // of it.
        let machine = TestMachine::two_registers().build();
        func.values[reusing].reg_class = 1;

        let actual = expect_invalid_with(&machine, &func);
        assert!(
            matches!(
                actual,
                Error::ReuseRegClassMismatch { inst: i, operand } if i == inst && operand == j
            ),
            "expected a `ReuseRegClassMismatch`, got {actual:?}",
        );
    }

    /// An input function that delegates to a `TestFunction`, except that it
    /// claims `extra_values` more values than it has, and that asking it for
    /// `lie_about` by index gives `lie_with` instead, so that the two ways of
    /// reaching a value disagree.
    struct LyingValues<'f> {
        func: &'f TestFunction,
        lie_about: Option<Val>,
        lie_with: Val,
        extra_values: usize,
    }

    impl InputFunction for LyingValues<'_> {
        type InputBlock<'a>
            = TestBlock<'a>
        where
            Self: 'a;

        type InputInst<'a>
            = TestInst<'a>
        where
            Self: 'a;

        type InputValue<'a>
            = TestValue<'a>
        where
            Self: 'a;

        fn len_values(&self) -> usize {
            self.func.len_values() + self.extra_values
        }

        fn len_insts(&self) -> usize {
            self.func.len_insts()
        }

        fn inst(&self, inst: Inst) -> Self::InputInst<'_> {
            self.func.inst(inst)
        }

        type ValuesIter<'a>
            = TestValuesIter<'a>
        where
            Self: 'a;

        fn values(&self) -> Self::ValuesIter<'_> {
            self.func.values()
        }

        fn value(&self, val: Val) -> Self::InputValue<'_> {
            self.func.value(if self.lie_about == Some(val) {
                self.lie_with
            } else {
                val
            })
        }

        fn entry_block(&self) -> Block {
            self.func.entry_block()
        }

        fn len_blocks(&self) -> usize {
            self.func.len_blocks()
        }

        fn block(&self, block: Block) -> Self::InputBlock<'_> {
            self.func.block(block)
        }

        type BlocksIter<'a>
            = TestBlocksIter<'a>
        where
            Self: 'a;

        fn blocks(&self) -> Self::BlocksIter<'_> {
            self.func.blocks()
        }
    }

    #[test]
    fn reject_a_value_lookup_that_disagrees_with_the_values_iterator() {
        let func = valid_func(1, 2);
        assert!(func.len_values() >= 2);

        let lie_about = Val::try_new(0).unwrap();
        let lying = LyingValues {
            func: &func,
            lie_about: Some(lie_about),
            lie_with: Val::try_new(1).unwrap(),
            extra_values: 0,
        };

        assert_invalid!(&lying, Error::InconsistentVal { val } if val == lie_about);
    }

    #[test]
    fn reject_a_values_iterator_that_disagrees_with_len_values() {
        let func = valid_func(1, 1);
        let lying = LyingValues {
            func: &func,
            lie_about: None,
            lie_with: Val::try_new(0).unwrap(),
            extra_values: 1,
        };

        assert_invalid!(
            &lying,
            Error::InconsistentLen {
                method: "len_values",
                block: None,
            },
        );
    }

    /// An input function that delegates to a `TestFunction`, except that asking
    /// it for one particular instruction gives a different one, so that the two
    /// ways of reaching an instruction disagree.
    struct LyingLookup<'f> {
        func: &'f TestFunction,
        lie_about: Inst,
        lie_with: Inst,
    }

    impl InputFunction for LyingLookup<'_> {
        type InputBlock<'a>
            = TestBlock<'a>
        where
            Self: 'a;

        type InputInst<'a>
            = TestInst<'a>
        where
            Self: 'a;

        type InputValue<'a>
            = TestValue<'a>
        where
            Self: 'a;

        fn len_values(&self) -> usize {
            self.func.len_values()
        }

        fn len_insts(&self) -> usize {
            self.func.len_insts()
        }

        fn inst(&self, inst: Inst) -> Self::InputInst<'_> {
            self.func.inst(if inst == self.lie_about {
                self.lie_with
            } else {
                inst
            })
        }

        type ValuesIter<'a>
            = TestValuesIter<'a>
        where
            Self: 'a;

        fn values(&self) -> Self::ValuesIter<'_> {
            self.func.values()
        }

        fn value(&self, val: Val) -> Self::InputValue<'_> {
            self.func.value(val)
        }

        fn entry_block(&self) -> Block {
            self.func.entry_block()
        }

        fn len_blocks(&self) -> usize {
            self.func.len_blocks()
        }

        fn block(&self, block: Block) -> Self::InputBlock<'_> {
            self.func.block(block)
        }

        type BlocksIter<'a>
            = TestBlocksIter<'a>
        where
            Self: 'a;

        fn blocks(&self) -> Self::BlocksIter<'_> {
            self.func.blocks()
        }
    }

    #[test]
    fn reject_a_lookup_that_gives_an_instruction_from_another_block() {
        let func = valid_func(2, 1);
        let lie_about = func.blocks[Block::try_new(0).unwrap()].insts[0];
        let lie_with = func.blocks[Block::try_new(1).unwrap()].insts[0];

        let lying = LyingLookup {
            func: &func,
            lie_about,
            lie_with,
        };

        assert_invalid!(&lying, Error::InconsistentInst { inst: i } if i == lie_about);
    }

    #[test]
    fn reject_a_lookup_that_gives_another_instruction_from_the_same_block() {
        let func = valid_func(1, 2);
        let block = Block::try_new(0).unwrap();
        let lie_about = func.blocks[block].insts[0];
        let lie_with = func.blocks[block].insts[1];

        // Both instructions are in the same block, so it is the operands that
        // have to give the lie away. `ensure_unique_defs` is what makes them
        // differ, so check that they do rather than let this pass vacuously.
        assert!(
            func.inst(lie_about)
                .operands()
                .ne(func.inst(lie_with).operands()),
            "the two instructions must differ for this check to have any teeth",
        );

        let lying = LyingLookup {
            func: &func,
            lie_about,
            lie_with,
        };

        assert_invalid!(&lying, Error::InconsistentInst { inst: i } if i == lie_about);
    }
}
