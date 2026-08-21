//! Test utilities.

#![allow(missing_docs, reason = "internal test utilities")]

use crate::{
    Block, InputBlock, InputFunction, InputInst, Machine, MachineBuilder, Operand, Reg, RegClass,
    RegGroup, RegUnit, Val,
    dfs::{Dfs, DfsEvent},
    dominators::DominatorTree,
    entity::{
        Entity, EntityRepr, Inst, PrimaryMap, PrimaryMapKeys, Region, Scc, SccBlockIndex,
        SecondaryMap, SpillSlot,
    },
    input::{BlockFrequency, DefUse, Input, InputOptions, OperandConstraint, Position},
    live_ranges::{LiveBundle, LiveSpan, MAX_OPERANDS_PER_INST},
    output::OutputInner,
};
use alloc::{vec, vec::Vec};
use core::{
    fmt::{self, Display},
    hash::Hasher,
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

#[cfg(any(test, fuzz))]
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
}

#[derive(Clone, Default, Debug, Hash, Mutate)]
pub struct ValData {
    ty: Type,
    def: ValDef,
}

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
pub enum Type {
    #[default]
    I32,
    I64,
    F32,
    F64,
    V128,
    V256,
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

fn hash<T>(value: &T) -> u64
where
    T: core::hash::Hash,
{
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
    pub(crate) fn dominators(&self) -> &DominatorTree {
        &self.dominators
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
                        ty: Type::I32,
                        def: ValDef::InstResult {
                            inst: Inst::try_new(0).unwrap(),
                            i: 0,
                        },
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

            stack.extend(self.dominators.children(block).map(ScopeFrame::Enter));
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

        // Mint a fresh value for a definition site, keeping the type of
        // whichever old value used to be named there so that mutating a value's
        // type still means something.
        let mut fresh_val = |values: &mut PrimaryMap<Val, ValData>, old: Val, def: ValDef| -> Val {
            let old = Val::try_new(old.index() % num_old_values).unwrap();
            let ty = old_values[old].ty.clone();
            values.push(output, ValData { ty, def }).unwrap()
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

    /// Make every `Reuse` constraint name an operand that it is allowed to
    /// name: one that exists, and whose own constraint is not a `Reuse`.
    fn ensure_operand_constraints(&mut self) {
        for (_inst, inst_data) in self.insts.iter_mut() {
            let operands = inst_data.operands_mut();
            let num_operands = operands.len();

            // Where each operand's reuse points after wrapping, so that the
            // walk below can chase it without borrowing `operands` again.
            let targets: Vec<Option<usize>> = operands
                .iter()
                .map(|op| match op.constraint() {
                    OperandConstraint::Reuse(i) => Some(i % num_operands),
                    _ => None,
                })
                .collect();

            for i in 0..num_operands {
                let Some(mut target) = targets[i] else {
                    continue;
                };

                let mut steps = 0;
                while let Some(next) = targets[target] {
                    steps += 1;
                    if steps > num_operands {
                        // Every operand reuses another one, so there is no
                        // operand left for this one to legally name.
                        target = i;
                        break;
                    }
                    target = next;
                }

                let constraint = if target == i {
                    OperandConstraint::Any
                } else {
                    OperandConstraint::Reuse(target)
                };
                let op = &mut operands[i];
                *op = Operand::new(op.pos(), op.kind(), constraint, op.val());
            }
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
            stack.extend(dominators.children(block).map(ScopeFrame::Enter));
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
        = PrimaryMapKeys<Val>
    where
        Self: 'a;

    fn values(&self) -> Self::ValuesIter<'_> {
        self.values.keys()
    }

    fn remat_cost(&self, _val: Val) -> Option<crate::RematCost> {
        None
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
        self.func.dominators.idom(self.block)
    }

    fn dominates(&self, other: Block) -> bool {
        self.func.dominators.block_dominates(self.block, other)
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

    fn clobbers(&self) -> crate::RegSet {
        todo!()
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
}

#[derive(Clone, Debug, Default, Hash, Mutate)]
pub struct TestBank {
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
        let mut machine = TestMachine { banks: Vec::new() };
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

    /// The widest a generated register may be, in register units.
    const MAX_REG_UNITS: u8 = 2;

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
        };
        machine.fixup();
        machine
    }

    /// How many register classes this machine defines, which is the number of
    /// classes an operand may name.
    ///
    /// This counts only the classes described here, not the intersections that
    /// `MachineBuilder::finish` derives from them.
    pub fn num_classes(&self) -> usize {
        self.banks.iter().map(|bank| bank.classes.len()).sum()
    }

    /// Repair this description so that [`TestMachine::build`] cannot fail.
    pub fn fixup(&mut self) {
        self.banks.truncate(Self::MAX_BANKS);
        if self.banks.is_empty() {
            self.banks.push(TestBank::default());
        }

        for bank in &mut self.banks {
            // A bank needs a register that the allocator owns for
            // stack-to-stack moves.
            bank.regs.truncate(Self::MAX_REGS_PER_BANK);
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
            let reg_bank = builder.declare_reg_bank().unwrap();

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
            .proj(|TestMachine { banks }: &mut TestMachine| banks)
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
    pub machine: TestMachine,
    pub func: TestFunction,
}

impl Default for TestInput {
    fn default() -> Self {
        let mut input = TestInput {
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
    }

    /// A single-block input whose one value is defined by the first
    /// instruction and then used once per entry in `constraints`, one use per
    /// instruction, in that order.
    ///
    /// The machine is [`TestMachine::two_registers`], so `Reg(rc0)` and
    /// `Reg(rc1)` are the pair of constraints that conflict and `Reg(rc2)` is
    /// the one that can be met alongside either.
    pub fn with_use_constraints(constraints: &[OperandConstraint]) -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = Val::try_new(0).unwrap();
        let def = Inst::try_new(0).unwrap();

        func.values = PrimaryMap::new();
        func.values
            .push(
                &mut output,
                ValData {
                    ty: Type::default(),
                    def: ValDef::InstResult { inst: def, i: 0 },
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
                        OperandConstraint::Any,
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
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A two-block input that passes one value along an edge as a block
    /// argument, with a use of the argument constrained by `arg` and a use of
    /// the parameter it feeds constrained by `param`.
    ///
    /// This is the smallest function that has a block argument-to-parameter
    /// affinity for coalescing to find, and the constraints are the knob for
    /// deciding whether it may take it. The machine is
    /// [`TestMachine::two_registers`], so `Reg(rc0)` and `Reg(rc1)` are the
    /// pair that conflict.
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
                        ty: Type::default(),
                        def,
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
            // The definition, then a use that gives the argument's span its
            // constraint, then the branch that passes it along.
            op(Position::Late, DefUse::Def, OperandConstraint::Any, arg_val),
            op(Position::Early, DefUse::Use, arg, arg_val),
            InstData::Branch {
                operands: vec![],
                targets: vec![BlockCall {
                    target,
                    args: vec![arg_val],
                }],
            },
            // A use that gives the parameter's span its constraint, then a
            // terminator of the target block's own, so that
            // `ensure_terminators` does not take that use away.
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
        let options = InputOptions::default();
        f(&Input {
            options: &options,
            machine: &machine,
            func: &self.func,
        })
    }
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
                            machine.intersect_classes(a, b),
                            machine.intersect_classes(b, a),
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
        let mut output = OutputInner::<u32>::new();
        let machine = test_machine();
        let options = InputOptions::default();
        let input = Input {
            options: &options,
            machine: &machine,
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
            = PrimaryMapKeys<Val>
        where
            Self: 'a;

        fn values(&self) -> Self::ValuesIter<'_> {
            self.func.values()
        }

        fn remat_cost(&self, val: Val) -> Option<crate::RematCost> {
            self.func.remat_cost(val)
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
