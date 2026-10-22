//! Test utilities.

#![allow(missing_docs, reason = "internal test utilities")]

mod parallel_moves;

pub use parallel_moves::*;

use crate::{
    Block, InputBlock, InputFunction, InputInst, InputValue, Machine, MachineBuilder, Operand, Reg,
    RegClass, RegGroup, RegSet, RegUnit, Val,
    dfs::{Dfs, DfsEvent},
    dominators::DominatorTree,
    entity::{Entity, EntityRepr, Inst, PrimaryMap, Region, SecondaryMap},
    input::{
        BlockFrequency, DefUse, Input, InputOptions, MoveEliminationLevel, OperandConstraint,
        Position, RematCost,
    },
    live_ranges::{LiveBundle, LiveSpan, MAX_OPERANDS_PER_INST},
    output::OutputInner,
    spill_slot_allocation::{SpillSlot, SpillSlotSize},
    union_find::UnionFind,
    validation::{FixedOperandScratch, check_inst_fixed_operands},
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
    // Deliberately not uniform:
    //
    // * `Stack` is weighted up because it is the only constraint that
    //   `TestInput::fixup` never rewrites, and because an operand that demands
    //   memory is what drives spill slots, reloads, and the stack-resident
    //   bundle paths.
    //
    // * `Reg` is weighted *down* to pay for it: the only bundle the allocator
    //   gives up on is one that is already minimal and still wants a register,
    //   so fewer hard register demands per instruction is what keeps the skip
    //   rate affordable while the machines themselves get scarcer. Not below a
    //   sixth, though, since a `Reg` on a singleton class is the only way to
    //   pin an operand to one register.
    Ok(match ctx.rng().gen_index(20).unwrap() {
        0..6 => OperandConstraint::Any,
        6..9 => {
            let index = ctx
                .rng()
                .gen_index(RegClass::MAX_INCLUDING_DERIVED)
                .unwrap();
            OperandConstraint::Reg(RegClass::try_new(index).unwrap())
        }
        9..16 => OperandConstraint::Stack,
        _ => {
            let index = ctx.rng().gen_index(MAX_OPERANDS_PER_INST).unwrap();
            OperandConstraint::Reuse(index)
        }
    })
}

/// Generate a level of move elimination.
fn gen_move_elimination_level(ctx: &mut mutatis::Context) -> mutatis::Result<MoveEliminationLevel> {
    let i = ctx
        .rng()
        .gen_index(MoveEliminationLevel::ALL.len())
        .unwrap();
    Ok(MoveEliminationLevel::ALL[i])
}

/// Mutate one move-elimination level in place.
///
/// Doing less move elimination is the simpler test case, so shrinking walks
/// down towards `None`; a level that is already `None` has nowhere left to
/// shrink to.
fn mutate_move_elimination_level(
    ctx: &mut mutatis::Context,
    level: &mut MoveEliminationLevel,
) -> mutatis::Result<()> {
    *level = if ctx.shrink() {
        let simpler: &[MoveEliminationLevel] = match *level {
            MoveEliminationLevel::None => return Err(mutatis::error::Error::exhausted()),
            MoveEliminationLevel::Local => &[MoveEliminationLevel::None],
            MoveEliminationLevel::SinglePass => {
                &[MoveEliminationLevel::None, MoveEliminationLevel::Local]
            }
            MoveEliminationLevel::Global => &[
                MoveEliminationLevel::None,
                MoveEliminationLevel::Local,
                MoveEliminationLevel::SinglePass,
            ],
        };
        simpler[ctx.rng().gen_index(simpler.len()).unwrap()]
    } else {
        gen_move_elimination_level(ctx)?
    };
    Ok(())
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
        let old_index = operand.val().map(|val| val.index());
        if !mutations.shrink() || old_index.is_some() {
            mutations.mutation(|ctx| {
                let val = if ctx.shrink() {
                    let old_index = old_index.expect("only offered when there is a value");
                    if old_index == 0 {
                        None
                    } else {
                        Some(Val::<E>::try_new(ctx.rng().gen_usize() % old_index).unwrap())
                    }
                } else {
                    Some(EntityMutator::<Val<E>>::default().generate(ctx)?)
                };
                *operand = Operand::new(operand.pos(), operand.kind(), operand.constraint(), val);
                Ok(())
            })?;
        }

        if !mutations.shrink() && old_index.is_some() {
            mutations.mutation(|_ctx| {
                *operand = Operand::new(operand.pos(), operand.kind(), operand.constraint(), None);
                Ok(())
            })?;
        }

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
        // Mostly ordinary operands.
        let val = if ctx.rng().gen_usize() % 32 == 0 {
            None
        } else {
            Some(EntityMutator::<Val<E>>::default().generate(ctx)?)
        };
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
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
pub struct BlockCall {
    target: Block,
    args: Vec<Val>,
}

#[derive(Clone, Debug, Hash, Mutate)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
pub enum InstData {
    Op {
        operands: Vec<Operand>,
        clobbers: Vec<Reg>,
        side_effects: bool,
    },
    Branch {
        operands: Vec<Operand>,
        clobbers: Vec<Reg>,
        targets: Vec<BlockCall>,
    },
}

impl Default for InstData {
    fn default() -> Self {
        Self::Op {
            operands: vec![],
            clobbers: vec![],
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

    /// The registers this instruction destroys the contents of.
    ///
    /// A `Vec` rather than a `RegSet`, so that `Mutate` and `Deserialize` come
    /// free. `TestInput::fixup` keeps it canonical, so that the round trip
    /// through a set and back is the identity.
    fn clobbers(&self) -> &[Reg] {
        match self {
            InstData::Op { clobbers, .. } | InstData::Branch { clobbers, .. } => clobbers,
        }
    }

    /// Get mutable access to this instruction's clobbers.
    fn clobbers_mut(&mut self) -> &mut Vec<Reg> {
        match self {
            InstData::Op { clobbers, .. } | InstData::Branch { clobbers, .. } => clobbers,
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
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
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

/// The index in [`REMAT_COSTS`] of "not rematerializable".
const NO_REMAT: u8 = 0;

/// May `val` carry a rematerialization cost?
///
/// A rematerialization computes its value from nothing, into a single
/// register, so validation only accepts a cost on a value that occupies one
/// register and is defined by an instruction reading no operands. That rules
/// out block parameters: a parameter's definition is the argument its
/// predecessors pass.
fn can_remat(func: &TestFunction, machine: &Machine, val: Val) -> bool {
    let val_data = &func.values[val];

    let class = RegClass::try_new(usize::from(val_data.reg_class)).unwrap();
    if class.group_size(machine).unwrap_or(1) != 1 {
        return false;
    }

    match val_data.def {
        ValDef::BlockParam { .. } => false,
        ValDef::InstResult { inst, .. } => func.insts[inst]
            .operands()
            .iter()
            .all(|op| op.kind() != DefUse::Use),
    }
}

/// Where a value is defined.
#[derive(Clone, Debug, Hash, PartialEq, Eq, Mutate)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
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
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
pub struct BlockData {
    pub params: Vec<Val>,
    pub insts: Vec<Inst>,
    pub frequency: u8,
}

/// The block frequencies that a `TestFunction`'s blocks may take, indexed by
/// `BlockData::frequency`.
///
/// `NORMAL` comes first so that a default, unmutated block is neither hot nor
/// cold. Zero is below `COLD`, which an embedder may also report.
const BLOCK_FREQUENCIES: [BlockFrequency; 7] = [
    BlockFrequency::NORMAL,
    BlockFrequency::COLD,
    BlockFrequency::new(0.5),
    BlockFrequency::new(10.0),
    BlockFrequency::HOT,
    BlockFrequency::new(10_000.0),
    BlockFrequency::new(0.0),
];

#[derive(Clone, Hash)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
pub struct TestFunction {
    mutated: bool,
    values: PrimaryMap<Val, ValData>,
    blocks: PrimaryMap<Block, BlockData>,
    insts: PrimaryMap<Inst, InstData>,

    // The rest of these fields are derived state: `fixup` rebuilds them (and
    // `fixup` must be called after deserialization).
    #[cfg_attr(
        any(feature = "serialize", feature = "deserialize"),
        serde(skip, default = "empty_predecessors")
    )]
    predecessors: SecondaryMap<Block, Vec<Block>>,
    #[cfg_attr(
        any(feature = "serialize", feature = "deserialize"),
        serde(skip, default = "empty_inst_blocks")
    )]
    inst_blocks: SecondaryMap<Inst, Option<Block>>,
    #[cfg_attr(
        any(feature = "serialize", feature = "deserialize"),
        serde(skip, default = "empty_dominators")
    )]
    dominators: DominatorTree,
}

#[cfg(feature = "deserialize")]
fn empty_predecessors() -> SecondaryMap<Block, Vec<Block>> {
    SecondaryMap::new(Vec::new())
}

#[cfg(feature = "deserialize")]
fn empty_inst_blocks() -> SecondaryMap<Inst, Option<Block>> {
    SecondaryMap::new(None)
}

#[cfg(feature = "deserialize")]
fn empty_dominators() -> DominatorTree {
    DominatorTree::default()
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

    /// Repair this function until it is well formed: a terminated,
    /// fully-reachable control-flow graph in valid SSA form.
    ///
    /// Every pass below is idempotent, and none of the value-level passes
    /// changes the control-flow graph, so the dominator tree computed in the
    /// middle stays valid for the passes that follow it.
    pub fn fixup(&mut self) {
        let mut output = OutputInner::<u32>::new();
        self.ensure_non_empty(&mut output);
        self.ensure_val_less_operands_are_reads();
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

    /// Make every operand that names no value a use.
    fn ensure_val_less_operands_are_reads(&mut self) {
        for (_inst, inst_data) in self.insts.iter_mut() {
            for operand in inst_data.operands_mut() {
                if operand.val().is_none() && operand.kind() != DefUse::Use {
                    *operand = Operand::new(operand.pos(), DefUse::Use, operand.constraint(), None);
                }
            }
        }
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
                            Some(Val::try_new(0).unwrap()),
                        )],
                        clobbers: vec![],
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
                    clobbers,
                    targets: _,
                } = &mut self.insts[*inst]
                {
                    let operands = mem::take(operands);
                    let clobbers = mem::take(clobbers);
                    self.insts[*inst] = InstData::Op {
                        operands,
                        clobbers,
                        side_effects: false,
                    };
                }
            }

            match &mut self.insts[terminator] {
                InstData::Op {
                    operands, clobbers, ..
                } => {
                    let operands = mem::take(operands);
                    let clobbers = mem::take(clobbers);
                    self.insts[terminator] = InstData::Branch {
                        operands,
                        clobbers,
                        targets: vec![],
                    };
                }
                InstData::Branch {
                    operands: _,
                    clobbers: _,
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
                    clobbers: _,
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

        for (block, block_data) in self.blocks.iter() {
            let terminator = *block_data.insts.last().unwrap();
            // These are the same block calls that `successors` reads, so the
            // two cannot disagree about what the edges are. One entry per edge,
            // so a block that branches to the same target twice appears twice
            // in that target's predecessors.
            for call in self.insts[terminator].block_calls() {
                self.predecessors[call.target].push(block);
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

                // An operand naming no value reads nothing that has to be
                // in scope, so it is not a use for this purpose.
                let uses = inst_data
                    .operands()
                    .iter()
                    .filter(|op| op.kind() == DefUse::Use && op.val().is_some())
                    .count();
                if scope_len == 0 && uses > 0 {
                    needs_param = true;
                    break 'walk;
                }

                scope_len += inst_data
                    .operands()
                    .iter()
                    .filter(|op| op.kind() == DefUse::Def && op.val().is_some())
                    .count();

                // Block call arguments count as uses too, since
                // `ensure_block_call_arity` is about to give each one an
                // argument per target parameter. Counted after this
                // instruction's own definitions, because arguments are read
                // as control leaves the block.
                let call_args = inst_data
                    .block_calls()
                    .iter()
                    .map(|call| self.blocks[call.target].params.len())
                    .sum::<usize>();
                if scope_len == 0 && call_args > 0 {
                    needs_param = true;
                    break 'walk;
                }
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

        for (block, block_data) in self.blocks.iter_mut() {
            for (i, param) in block_data.params.iter_mut().enumerate() {
                *param = fresh_val(&mut self.values, *param, ValDef::BlockParam { block, i });
            }

            for inst in &block_data.insts {
                let inst = *inst;
                let mut i = 0;
                for op in self.insts[inst].operands_mut() {
                    if let (DefUse::Def, Some(val)) = (op.kind(), op.val()) {
                        op.set_val(Some(fresh_val(
                            &mut self.values,
                            val,
                            ValDef::InstResult { inst, i },
                        )));
                        i += 1;
                    }
                }
            }
        }
    }

    /// Make every block call pass exactly as many arguments as its target block
    /// has parameters.
    fn ensure_block_call_arity(&mut self) {
        for (_block, block_data) in self.blocks.iter() {
            for inst in &block_data.insts {
                for call in self.insts[*inst].block_calls_mut() {
                    let arity = self.blocks[call.target].params.len();
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
        let mut reusable = Vec::new();

        for (_inst, inst_data) in self.insts.iter_mut() {
            let operands = inst_data.operands_mut();

            reusable.clear();
            reusable.extend(operands.iter().enumerate().filter_map(|(i, op)| {
                // An operand naming no value has none to tie a definition to.
                let ok = op.kind() == DefUse::Use
                    && op.pos() == Position::Early
                    && op.constraint() != OperandConstraint::Stack
                    && op.val().is_some();
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
        let mut sets = UnionFind::<Val>::new();

        for (_block, block_data) in self.blocks.iter() {
            for inst in &block_data.insts {
                let inst_data = &self.insts[*inst];

                // Block-call arguments and block params must agree.
                for call in inst_data.block_calls() {
                    for (arg, param) in call.args.iter().zip(&self.blocks[call.target].params) {
                        sets.union(*arg, *param);
                    }
                }

                // Reuse operands must agree.
                let operands = inst_data.operands();
                for op in operands {
                    let OperandConstraint::Reuse(i) = op.constraint() else {
                        continue;
                    };
                    let (Some(val), Some(target)) = (op.val(), operands[i].val()) else {
                        continue;
                    };
                    sets.union(val, target);
                }
            }
        }

        let max_reg_classes = u8::try_from(MAX_REG_CLASSES).unwrap();
        for i in 0..self.values.len() {
            let val = Val::try_new(i).unwrap();
            let root = sets.find(val);
            debug_assert!(root.index() < self.values.len());
            let reg_class = self.values[root].reg_class % max_reg_classes;
            self.values[val].reg_class = reg_class;
        }
    }

    /// Rewrite every use whose value is not defined by a definition that
    /// dominates it.
    fn ensure_uses_dominated_by_defs(&mut self) {
        let entry = self.entry_block();
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
            scope.extend_from_slice(&self.blocks[block].params);

            for inst in &self.blocks[block].insts {
                let inst = *inst;

                for op in self.insts[inst].operands_mut() {
                    if let (DefUse::Use, Some(val)) = (op.kind(), op.val()) {
                        op.set_val(Some(in_scope(&scope, val)));
                    }
                }

                for op in self.insts[inst].operands() {
                    if let (DefUse::Def, Some(val)) = (op.kind(), op.val()) {
                        scope.push(val);
                    }
                }

                // Outgoing arguments are read as control leaves the block,
                // so they see the terminator's own definitions.
                for call in self.insts[inst].block_calls_mut() {
                    for arg in &mut call.args {
                        *arg = in_scope(&scope, *arg);
                    }
                }
            }

            // Every block is reachable, so this walk reaches every block.
            stack.extend(block.dom_children(&self.dominators).map(ScopeFrame::Enter));
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
                clobbers: _,
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

    fn clobbers(&self) -> RegSet {
        let mut set = RegSet::new();
        for &reg in self.func.insts[self.inst].clobbers() {
            set.insert(reg);
        }
        set
    }
}

/// A description of a machine, in a form that `mutatis` can generate and
/// mutate.
#[derive(Clone, Debug, Hash)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
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
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
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
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
pub struct TestGroup {
    /// Indices into the bank's `regs`, in the group's order.
    members: Vec<u8>,
}

#[derive(Clone, Debug, Default, Hash, Mutate)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
pub struct TestClass {
    members: TestClassMembers,

    /// Scaled into the `f32` spill cost that `define_reg_class` wants; an
    /// integer here so that `TestMachine` can derive `Hash`.
    spill_cost: u8,
}

/// What a class holds: either individual registers or whole register groups,
/// never a mix of the two.
#[derive(Clone, Debug, Hash, Mutate)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
pub enum TestClassMembers {
    /// Indices into the bank's registers, in preference order: `0..regs.len()`
    /// are the registers the allocator owns, and the
    /// `regs.len()..regs.len() + non_allocatable` after them the ones it does
    /// not.
    ///
    /// A class may hold either kind, which is how an operand pins a read to a
    /// register the allocator does not own.
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

    /// The class holding [`TestMachine::four_registers`]' first two
    /// registers.
    pub const FIRST_PAIR_CLASS: u8 = 0;

    /// The class holding [`TestMachine::four_registers`]' last two registers,
    /// and so nothing [`TestMachine::FIRST_PAIR_CLASS`] holds.
    pub const SECOND_PAIR_CLASS: u8 = 1;

    /// The class holding all four of [`TestMachine::four_registers`]'
    /// registers, and so the only one of its classes a value can belong to
    /// while still meeting either pair's constraint.
    pub const ALL_FOUR_REGS_CLASS: u8 = 2;

    /// A machine of one bank with four registers and three classes: `rc0`
    /// holds the first two registers, `rc1` the last two, and `rc2` all four.
    ///
    /// `rc0` and `rc1` are disjoint but neither names a single register, so an
    /// operand under one constrains its span rather than reserving a register.
    /// This is the machine for conflicting constraints without pinning.
    pub fn four_registers() -> Self {
        let pair = |i: u8| TestClass {
            members: TestClassMembers::Regs(vec![i, i + 1]),
            spill_cost: 0,
        };
        let mut machine = TestMachine {
            banks: vec![TestBank {
                log2_size: 3,
                regs: vec![1, 1, 1, 1],
                non_allocatable: 0,
                groups: Vec::new(),
                classes: vec![
                    pair(0),
                    pair(2),
                    TestClass {
                        members: TestClassMembers::Regs(vec![0, 1, 2, 3]),
                        spill_cost: 0,
                    },
                ],
            }],
            regs_per_bank: None,
        };
        machine.fixup();
        machine
    }

    /// The class holding [`TestMachine::overlapping_pairs`]' first two
    /// registers.
    pub const LOW_PAIR_CLASS: u8 = 0;

    /// The class holding [`TestMachine::overlapping_pairs`]' last two
    /// registers, which shares its first register with
    /// [`TestMachine::LOW_PAIR_CLASS`].
    pub const HIGH_PAIR_CLASS: u8 = 1;

    /// The class holding all three of [`TestMachine::overlapping_pairs`]'
    /// registers.
    pub const ALL_THREE_REGS_CLASS: u8 = 2;

    /// A machine of one bank with three registers and three classes: `rc0`
    /// holds the first two, `rc1` the last two, and `rc2` all three.
    ///
    /// `rc0` and `rc1` overlap in exactly one register without naming it
    /// alone, so neither is a fixed operand, but a span whose uses ask for
    /// both folds to the *derived* class `MachineBuilder::finish` adds for
    /// their intersection. That is the one shape a singleton constraint can
    /// still reach a bundle through.
    pub fn overlapping_pairs() -> Self {
        let pair = |i: u8| TestClass {
            members: TestClassMembers::Regs(vec![i, i + 1]),
            spill_cost: 0,
        };
        let mut machine = TestMachine {
            banks: vec![TestBank {
                log2_size: 3,
                regs: vec![1, 1, 1],
                non_allocatable: 0,
                groups: Vec::new(),
                classes: vec![
                    pair(0),
                    pair(1),
                    TestClass {
                        members: TestClassMembers::Regs(vec![0, 1, 2]),
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

    /// The class holding [`TestMachine::a_group_and_one_of_its_registers`]'s
    /// only register group, and so the way to pin an operand to the pair.
    pub const PAIRED_GROUP_CLASS: u8 = 0;

    /// The class holding that machine's first register alone, one of the two
    /// the group holds, and so the way to pin a scalar operand on top of it.
    pub const GROUPED_REG_CLASS: u8 = 1;

    /// The class holding both of that machine's registers one at a time, and
    /// so the class a value occupying just one of them belongs to.
    pub const UNGROUPED_REGS_CLASS: u8 = 2;

    /// A machine of one bank whose two registers form its only register
    /// group, with a class naming the first of them alone as well.
    ///
    /// `rc0` is the group and `rc1` is a register inside it, so two fixed
    /// operands here can claim one register while naming different classes,
    /// the only conflict other than naming the same register twice.
    pub fn a_group_and_one_of_its_registers() -> Self {
        let regs = |members| TestClass {
            members: TestClassMembers::Regs(members),
            spill_cost: 0,
        };
        let mut machine = TestMachine {
            banks: vec![TestBank {
                log2_size: 3,
                regs: vec![1, 1],
                non_allocatable: 0,
                groups: vec![TestGroup {
                    members: vec![0, 1],
                }],
                classes: vec![
                    TestClass {
                        members: TestClassMembers::Groups(vec![0]),
                        spill_cost: 0,
                    },
                    regs(vec![0]),
                    regs(vec![0, 1]),
                ],
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

    /// [`TestMachine::register_groups_in_two_orders`]' `rc0`: both of its
    /// groups, and so the class of a value that may go in either order.
    pub const EITHER_ORDER_CLASS: u8 = 0;

    /// [`TestMachine::register_groups_in_two_orders`]' `rc1`: the reversed
    /// group alone, and so the way to pin an operand to that order.
    pub const REVERSED_GROUP_CLASS: u8 = 1;

    /// A machine of one bank whose two registers form two groups in opposite
    /// orders: `(r0, r1)` and `(r1, r0)`.
    ///
    /// The two groups differ only in which piece of a value goes where, so a
    /// value in one order may not sit under a reservation of the other, even
    /// one held for that very value: see `PorousTo` in
    /// `region_allocation::assignments`.
    pub fn register_groups_in_two_orders() -> Self {
        let mut machine = TestMachine {
            banks: vec![TestBank {
                log2_size: 3,
                regs: vec![1, 1],
                non_allocatable: 0,
                groups: vec![
                    TestGroup {
                        members: vec![0, 1],
                    },
                    TestGroup {
                        members: vec![1, 0],
                    },
                ],
                classes: vec![
                    TestClass {
                        members: TestClassMembers::Groups(vec![0, 1]),
                        spill_cost: 0,
                    },
                    TestClass {
                        members: TestClassMembers::Groups(vec![1]),
                        spill_cost: 0,
                    },
                ],
            }],
            regs_per_bank: None,
        };
        machine.fixup();
        machine
    }

    /// [`TestMachine::with_a_non_allocatable_reg`]'s `rc0`: both of the
    /// registers the allocator owns, and nothing else, and so the only one of
    /// this machine's classes a value may belong to.
    pub const ALLOCATABLE_CLASS: u8 = 0;

    /// [`TestMachine::with_a_non_allocatable_reg`]'s `rc1`: its
    /// non-allocatable register alone, and so the way an operand demands that
    /// register.
    ///
    /// An operand pinned here names no value: `p` holds nothing the allocator
    /// is tracking.
    pub const PINNED_CLASS: u8 = 1;

    /// A machine of one bank with two registers the allocator owns, `r0` and
    /// `r1`, and one it does not, `p`.
    ///
    /// Its two classes are [`TestMachine::ALLOCATABLE_CLASS`] (`{r0, r1}`) and
    /// [`TestMachine::PINNED_CLASS`] (`{p}`). A class holding `p` alongside
    /// either of the others is not one a [`Machine`] can be built with, so
    /// these two are every class this bank's registers have between them.
    ///
    /// Only [`TestMachine::ALLOCATABLE_CLASS`] may hold a value, and
    /// [`TestMachine::PINNED_CLASS`] is nameable only by an operand naming no
    /// value.
    pub fn with_a_non_allocatable_reg() -> Self {
        let mut machine = TestMachine {
            banks: vec![TestBank {
                log2_size: 3,
                regs: vec![1, 1],
                non_allocatable: 1,
                groups: Vec::new(),
                classes: vec![
                    TestClass {
                        members: TestClassMembers::Regs(vec![0, 1]),
                        spill_cost: 0,
                    },
                    TestClass {
                        members: TestClassMembers::Regs(vec![2]),
                        spill_cost: 0,
                    },
                ],
            }],
            regs_per_bank: None,
        };
        machine.fixup();
        machine
    }

    /// The class `rc0` of [`TestMachine::two_aliasing_banks`]: bank 0's only
    /// register, two units wide.
    pub const WIDE_ALIAS_CLASS: u8 = 0;

    /// The class `rc1` of [`TestMachine::two_aliasing_banks`]: bank 1's only
    /// register, which sits inside bank 0's.
    pub const NARROW_ALIAS_CLASS: u8 = 1;

    /// Two banks of one register each, with bank 1's register sitting inside
    /// bank 0's.
    ///
    /// Units are numbered from zero in every bank, so bank 1's one-unit
    /// register covers the first of bank 0's two and the pair interfere.
    /// Neither bank holds anything else, so freeing either register evicts
    /// the other, and the two evictions cannot share a bracket.
    ///
    /// Both banks hold four-byte registers, so they share a spill slot pool.
    pub fn two_aliasing_banks() -> Self {
        let one_reg = |units, spill_cost| TestBank {
            log2_size: 2,
            regs: vec![units],
            non_allocatable: 0,
            groups: Vec::new(),
            classes: vec![TestClass {
                members: TestClassMembers::Regs(vec![0]),
                spill_cost,
            }],
        };
        let mut machine = TestMachine {
            banks: vec![one_reg(2, 29), one_reg(1, 41)],
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
        // Clamped here rather than trusted from the field, because
        // `set_regs_per_bank` is not the only writer: a deserialized
        // `TestMachine` carries whatever count it was encoded with, and the
        // register counts below feed `u8` conversions.
        self.regs_per_bank = self
            .regs_per_bank
            .map(|n| n.clamp(1, Self::MAX_REGS_PER_BANK_TARGET));

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
            let num_all_regs = num_regs + usize::from(bank.non_allocatable);

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
                        // Over every register in the bank, the ones the
                        // allocator does not own included: a class holds one of
                        // those when an operand pins a read to it.
                        for member in regs.iter_mut() {
                            *member %= u8::try_from(num_all_regs).unwrap();
                        }
                        dedupe_keeping_first(regs);
                        if regs.is_empty() {
                            regs.push(0);
                        }
                        // A class is wholly the allocator's or wholly the
                        // function's, so keep the members agreeing with the
                        // first one's kind and drop the rest, the same way one
                        // class holds groups of one size just below. Keyed on
                        // the first member, so that the generator can ask for
                        // either kind of class and gets the one it asked for.
                        let pinned = usize::from(regs[0]) >= num_regs;
                        regs.retain(|&member| (usize::from(member) >= num_regs) == pinned);

                        // And such a class holds exactly one register: it
                        // names the one register an operand reads, with
                        // nothing for the allocator to choose between. The
                        // first is the one the generator asked for first.
                        if pinned {
                            regs.truncate(1);
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
                        // register in. So is a class of registers the
                        // allocator does not own, which is not somewhere it
                        // could put a value anyway.
                        if self.regs_per_bank.is_some() && !pinned {
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

            let has_a_wholly_allocatable_class =
                bank.classes.iter().any(|class| match &class.members {
                    TestClassMembers::Regs(regs) => regs.iter().all(|&m| usize::from(m) < num_regs),
                    // A group holds only registers the allocator owns.
                    TestClassMembers::Groups(_) => true,
                });
            if !has_a_wholly_allocatable_class {
                // Every block parameter has to be in a class like this ---
                // a parameter arrives where the allocator puts it, so it may
                // not be in a class holding anywhere the allocator does not
                // own --- and so does every value that is ever defined, since
                // a class of nothing the allocator owns has nowhere to put
                // one. Narrow a class rather than adding one, so that the
                // number of classes stays the generator's to choose.
                let regs = bank
                    .classes
                    .iter_mut()
                    .find_map(|class| match &mut class.members {
                        TestClassMembers::Regs(regs) => Some(regs),
                        TestClassMembers::Groups(_) => None,
                    })
                    .expect("a bank whose every class held groups would already have one");
                regs.retain(|&m| usize::from(m) < num_regs);
                if regs.is_empty() {
                    regs.push(0);
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

            // The registers a class may name: the ones the allocator owns
            // first, then the ones it does not, matching how
            // `TestClassMembers::Regs` indices are numbered.
            let mut all_regs = regs.clone();
            for _ in 0..bank.non_allocatable {
                all_regs.push(builder.define_non_allocatable_reg(reg_bank).unwrap());
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
                        let members = members.iter().map(|&m| all_regs[usize::from(m)]);
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
        // Bias toward banks holding only one or two registers the allocator
        // owns, where spilling, eviction, and emergency slots are ordinary
        // rather than a rarity.
        mutations.mutation(|ctx| {
            let Some(index) = ctx.rng().gen_index(machine.banks.len()) else {
                return Ok(());
            };
            let target = if ctx.rng().gen_index(4).unwrap() == 0 {
                1
            } else {
                2
            };
            machine.banks[index].regs.truncate(target);
            machine.fixup();
            Ok(())
        })?;

        // Point a class at a register group.
        if !mutations.shrink() {
            mutations.mutation(|ctx| {
                let Some(index) = ctx.rng().gen_index(machine.banks.len()) else {
                    return Ok(());
                };
                let bank = &mut machine.banks[index];
                if bank.regs.len() < 2 || bank.classes.is_empty() {
                    return Ok(());
                }
                if bank.groups.is_empty() {
                    bank.groups.push(TestGroup {
                        members: vec![0, 1],
                    });
                }
                let class = ctx.rng().gen_index(bank.classes.len()).unwrap();
                bank.classes[class].members = TestClassMembers::Groups(vec![0]);
                machine.fixup();
                Ok(())
            })?;
        }

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
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
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

        let machine = self.machine.build();

        // An operand naming no value names a register the allocator does not
        // own, and nothing else: a read pinned to a class with no allocatable
        // member. Give every val-less operand that shape --- or, on a machine
        // where no class is wholly the function's own, give it a value
        // instead. `Val(0)` always exists once `ensure_non_empty` has run, and
        // `ensure_uses_dominated_by_defs` puts it in scope wherever it is
        // read; both run in `TestFunction::fixup` below, which is why this
        // repair comes first.
        let pinned_class = (0..num_classes)
            .map(|class| RegClass::try_new(class).unwrap())
            .find(|class| !class.has_an_allocatable_member(&machine));
        for (_inst, inst_data) in self.func.insts.iter_mut() {
            for operand in inst_data.operands_mut() {
                if operand.val().is_some() {
                    continue;
                }
                *operand = match pinned_class {
                    Some(class) => Operand::new(
                        operand.pos(),
                        DefUse::Use,
                        OperandConstraint::Reg(class),
                        None,
                    ),
                    None => Operand::new(
                        operand.pos(),
                        operand.kind(),
                        operand.constraint(),
                        Some(Val::try_new(0).unwrap()),
                    ),
                };
            }
        }

        self.func.fixup();

        // Where a class the allocator owns nothing in sends a value that would
        // otherwise belong to it: the next class the allocator does own,
        // wrapping around. A value goes wherever the allocator decides to put
        // it, so a class it owns nothing in is nowhere to put one.
        //
        // A pure function of the class index, so classes that
        // `TestFunction::ensure_reg_classes_agree` made equal stay equal.
        let value_class: Vec<u8> = (0..num_classes)
            .map(|class| {
                let found = (0..num_classes)
                    .map(|offset| (class + offset) % num_classes)
                    .find(|&candidate| {
                        RegClass::try_new(candidate)
                            .unwrap()
                            .has_an_allocatable_member(&machine)
                    })
                    .expect("`TestMachine::fixup` gives every bank one such class");
                u8::try_from(found).unwrap()
            })
            .collect();

        // One modulus applied uniformly, so the classes that
        // `TestFunction::ensure_reg_classes_agree` made equal stay equal.
        let num_classes_u8 = u8::try_from(num_classes).unwrap();
        for (_val, val_data) in self.func.values.iter_mut() {
            val_data.reg_class %= num_classes_u8;
            val_data.reg_class = value_class[usize::from(val_data.reg_class)];
        }

        let val_class = |values: &PrimaryMap<Val, ValData>, val| {
            RegClass::try_new(usize::from(values[val].reg_class)).unwrap()
        };

        // An operand names no value exactly when it is pinned to a class in
        // which the allocator owns nothing. One direction is the repair above,
        // and nothing in `TestFunction::fixup` moves an operand off the class
        // it put there; the other is an operand that *does* name a value being
        // pinned there, which the subset repair below also covers.
        //
        // An operand constraint must name a subset of its value's register
        // class. Every value's class holds nothing but registers the allocator
        // owns, by the remap above, so falling back to it repairs both at
        // once: a class is a subset of itself, and one holding a register the
        // allocator owns is not one it owns nothing in.
        for (_inst, inst_data) in self.func.insts.iter_mut() {
            for operand in inst_data.operands_mut() {
                let OperandConstraint::Reg(class) = operand.constraint() else {
                    continue;
                };
                let Some(val) = operand.val() else {
                    debug_assert_eq!(operand.kind(), DefUse::Use);
                    debug_assert!(
                        !class.has_an_allocatable_member(&machine),
                        "an operand naming no value is pinned to a class the allocator \
                         owns nothing in",
                    );
                    continue;
                };
                let val_class = val_class(&self.func.values, val);
                if class.intersect(&machine, val_class) == Some(class) {
                    continue;
                }
                *operand = Operand::new(
                    operand.pos(),
                    operand.kind(),
                    OperandConstraint::Reg(val_class),
                    Some(val),
                );
            }
        }

        // A clobber names a register directly, so the class remaps above do
        // not reach it. Canonical order matters because `TestInst::clobbers`
        // turns the list into a set, and `write_fuzz_corpus` asserts the round
        // trip is byte-identical.
        let num_registers = machine.num_registers();
        for (_inst, inst_data) in self.func.insts.iter_mut() {
            let clobbers = inst_data.clobbers_mut();
            for reg in clobbers.iter_mut() {
                *reg = Reg::try_new(reg.index() % num_registers).unwrap();
            }
            clobbers.retain(|reg| reg.is_allocatable(&machine));
            clobbers.sort_unstable();
            clobbers.dedup();
        }

        // Two fixed operands of one instruction may not name one register at
        // one time, since each holds its register outright. Nor may a clobber
        // and a fixed operand that wants the clobbered register in the late
        // half.
        //
        // Relax the last operand that could be *making* something fixed rather
        // than the one the check names: `reuse_aware_constraint` can resolve an
        // operand to a singleton through a sibling read or a `Reuse` tie, so
        // relaxing the named operand need not change its answer. Every such
        // origin is a singleton `Reg` or a `Reuse`, so clearing them one at a
        // time terminates with nothing resolving to a singleton.
        let insts: Vec<Inst> = self.func.insts.iter().map(|(inst, _)| inst).collect();
        let mut scratch = FixedOperandScratch::default();
        for inst in insts {
            loop {
                let num_operands = self.func.insts[inst].operands().len();
                if check_inst_fixed_operands(&self.func, &machine, &mut scratch, inst, num_operands)
                    .is_ok()
                {
                    break;
                }
                let operands = self.func.insts[inst].operands_mut();
                let relax = operands.iter().rposition(|operand| {
                    // An operand naming no value reads a register the
                    // allocator does not own, for which `Any` is not even a
                    // legal constraint.
                    operand.val().is_some()
                        && match operand.constraint() {
                            OperandConstraint::Reg(class) => class.is_fixed_reg(&machine),
                            OperandConstraint::Reuse(_) => true,
                            OperandConstraint::Any | OperandConstraint::Stack => false,
                        }
                });
                let Some(i) = relax else {
                    // Nothing left to relax, so the clobbers are party to the
                    // conflict. Dropping them settles it and creates no new
                    // one.
                    let clobbers = self.func.insts[inst].clobbers_mut();
                    assert!(
                        !clobbers.is_empty(),
                        "a conflict with no clobbers needs an operand that fixes something",
                    );
                    clobbers.clear();
                    continue;
                };
                let operand = operands[i];
                operands[i] = Operand::new(
                    operand.pos(),
                    operand.kind(),
                    OperandConstraint::Any,
                    operand.val(),
                );
            }
        }

        // Only a value a `Remat` could actually stand in for may carry a
        // rematerialization cost. This comes last: it reads the definition
        // sites `TestFunction::fixup` settled and the classes the remap above
        // settled.
        let cannot: Vec<Val> = self
            .func
            .values
            .iter()
            .filter(|(val, val_data)| {
                val_data.remat % u8::try_from(REMAT_COSTS.len()).unwrap() != NO_REMAT
                    && !can_remat(&self.func, &machine, *val)
            })
            .map(|(val, _)| val)
            .collect();
        for val in cannot {
            self.func.values[val].remat = NO_REMAT;
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
                        Some(val),
                    )],
                    clobbers: vec![],
                    side_effects: true,
                },
            )
            .unwrap();
        for &constraint in constraints {
            func.insts
                .push(
                    &mut output,
                    InstData::Op {
                        operands: vec![Operand::new(
                            Position::Early,
                            DefUse::Use,
                            constraint,
                            Some(val),
                        )],
                        clobbers: vec![],
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
                    clobbers: vec![],
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

    /// An input that needs more spill-slot group members than a `u8` entity
    /// representation can index, so that spill slot allocation bails with
    /// `EntityReprTooSmall` and `run_dispatch` retries under a wider one.
    pub fn with_more_spill_slot_groups_than_a_u8_can_index() -> Self {
        /// Enough live-at-once values to push `group_members` past 254.
        const NUM_VALS: usize = 128;

        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        // One value per definition, each pinned to the register group.
        func.values = PrimaryMap::new();
        for i in 0..NUM_VALS {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::GROUP_CLASS,
                        def: ValDef::InstResult {
                            inst: Inst::try_new(i / 2).unwrap(),
                            i: i % 2,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        // Two values per instruction, so that `NUM_VALS` values fit in half as
        // many instructions and the function stays inside what a `u8` can
        // index even though its spill slot groups do not.
        func.insts = PrimaryMap::new();
        for pair in (0..NUM_VALS).step_by(2) {
            func.insts
                .push(
                    &mut output,
                    InstData::Op {
                        operands: (pair..pair + 2)
                            .map(|i| {
                                Operand::new(
                                    Position::Late,
                                    DefUse::Def,
                                    OperandConstraint::Any,
                                    Some(Val::try_new(i).unwrap()),
                                )
                            })
                            .collect(),
                        clobbers: vec![],
                        side_effects: true,
                    },
                )
                .unwrap();
        }

        // A self-loop, so that the values defined in the body are live across
        // the back edge and the loop body is walked with all of them needing
        // slots at once.
        let body = Block::try_new(1).unwrap();
        func.insts
            .push(
                &mut output,
                InstData::Branch {
                    operands: vec![],
                    clobbers: vec![],
                    targets: vec![BlockCall {
                        target: body,
                        args: vec![],
                    }],
                },
            )
            .unwrap();
        let entry_term = func.insts.len() - 1;

        func.blocks = PrimaryMap::new();
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: vec![],
                    insts: vec![Inst::try_new(entry_term).unwrap()],
                    frequency: 0,
                },
            )
            .unwrap();
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: vec![],
                    insts: (0..entry_term).map(|i| Inst::try_new(i).unwrap()).collect(),
                    frequency: 0,
                },
            )
            .unwrap();

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::one_register_group(),
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
                Some(val),
            )],
            clobbers: vec![],
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
                        Some(first),
                    ),
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(r1),
                        Some(second),
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the reads.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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

    /// A single-block input on [`TestMachine::two_registers`] whose one
    /// instruction reads a value twice (once pinned to `r0`, once
    /// unconstrained) and ties a definition to the unconstrained read, which is
    /// then itself read from `r1`.
    pub fn with_a_reuse_of_a_pinned_read() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let first = Val::try_new(0).unwrap();
        let second = Val::try_new(1).unwrap();
        let r0 = RegClass::try_new(usize::from(TestMachine::FIRST_REG_CLASS)).unwrap();
        let r1 = RegClass::try_new(usize::from(TestMachine::SECOND_REG_CLASS)).unwrap();

        func.values = PrimaryMap::new();
        for (inst, i) in [(0, 0), (1, 2)] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def: ValDef::InstResult {
                            inst: Inst::try_new(inst).unwrap(),
                            i,
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
                    Some(first),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(r0),
                        Some(first),
                    ),
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        Some(first),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(1),
                        Some(second),
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Late,
                    DefUse::Use,
                    OperandConstraint::Reg(r1),
                    Some(second),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the reads.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        Self::single_block(TestMachine::two_registers(), func, output)
    }

    /// A single-block input on [`TestMachine::with_a_non_allocatable_reg`]
    /// whose first instruction reads `p` --- naming the register and no value
    /// at all --- and defines a value that a later instruction reads.
    ///
    /// This is the only way anything may name a register the allocator does
    /// not own, and the shape a client uses for an instruction that reads the
    /// stack pointer or a flags register.
    pub fn with_a_val_less_read_of_a_non_allocatable_reg() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = Val::try_new(0).unwrap();
        let pinned = RegClass::try_new(TestMachine::PINNED_CLASS.into()).unwrap();

        func.values = PrimaryMap::new();
        func.values
            .push(
                &mut output,
                ValData {
                    // Nothing but registers the allocator owns: no value may
                    // belong to a class holding `p`.
                    reg_class: TestMachine::ALLOCATABLE_CLASS,
                    def: ValDef::InstResult {
                        inst: Inst::try_new(0).unwrap(),
                        i: 0,
                    },
                    remat: 0,
                },
            )
            .unwrap();

        func.insts = PrimaryMap::new();
        for inst_data in [
            InstData::Op {
                operands: vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(pinned),
                        None,
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Any,
                        Some(val),
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Any,
                    Some(val),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the reads.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        Self::single_block(TestMachine::with_a_non_allocatable_reg(), func, output)
    }

    /// Wrap `func`'s instructions in one block, in order, and fix the result
    /// up into a valid [`TestInput`] on `machine`.
    fn single_block(
        machine: TestMachine,
        mut func: TestFunction,
        mut output: OutputInner<u32>,
    ) -> Self {
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
                Some(val),
            )],
            clobbers: vec![],
            side_effects: true,
        };
        let reads = |constraint: fn(RegClass) -> OperandConstraint| InstData::Op {
            operands: vec![
                Operand::new(
                    Position::Early,
                    DefUse::Use,
                    constraint(wide_regs),
                    Some(wide),
                ),
                Operand::new(
                    Position::Early,
                    DefUse::Use,
                    constraint(narrow_regs),
                    Some(narrow),
                ),
            ],
            clobbers: vec![],
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
                clobbers: vec![],
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

    /// One value spilled in the entry block and reloaded past a diamond: a
    /// stack-constrained read puts it on the stack, both arms leave it alone,
    /// and a register-constrained read in the merge block brings it back. The
    /// reload is redundant, but only a reader who looks past the merge block
    /// can tell.
    pub fn with_a_value_reloaded_past_a_diamond() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = Val::try_new(0).unwrap();
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();
        let block = |i| Block::try_new(i).unwrap();
        let merge = block(3);

        func.values = PrimaryMap::new();
        func.values
            .push(
                &mut output,
                ValData {
                    reg_class: TestMachine::BOTH_REGS_CLASS,
                    def: ValDef::InstResult {
                        inst: Inst::try_new(0).unwrap(),
                        i: 0,
                    },
                    remat: 0,
                },
            )
            .unwrap();

        let op = |pos, kind, constraint| InstData::Op {
            operands: vec![Operand::new(pos, kind, constraint, Some(val))],
            clobbers: vec![],
            side_effects: true,
        };
        let branch = |targets: &[Block]| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: targets
                .iter()
                .map(|&target| BlockCall {
                    target,
                    args: Vec::new(),
                })
                .collect(),
        };

        func.insts = PrimaryMap::new();
        for inst_data in [
            // `block0`: define the value in a register --- pinned, so the
            // definition does not land on the stack and make the store free ---
            // read it on the stack, and fork.
            op(Position::Late, DefUse::Def, OperandConstraint::Reg(class)),
            op(Position::Early, DefUse::Use, OperandConstraint::Stack),
            branch(&[block(1), block(2)]),
            // `block1` and `block2`: a way to the merge, touching nothing.
            branch(&[merge]),
            branch(&[merge]),
            // `block3`: read it in a register again, asking for the reload.
            op(Position::Early, DefUse::Use, OperandConstraint::Reg(class)),
            // A terminator of its own, so `ensure_terminators` leaves the read
            // alone.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        for (insts, params) in [
            (vec![inst(0), inst(1), inst(2)], vec![]),
            (vec![inst(3)], vec![]),
            (vec![inst(4)], vec![]),
            (vec![inst(5), inst(6)], vec![]),
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params,
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// One value spilled across a clobber of every register in the entry block,
    /// which then forks, and read in a register first thing on each arm: each
    /// arm reloads it into the same register, which is the shape
    /// demanded-move hoisting merges into one reload before the fork.
    ///
    /// `arms` is how many arms the fork has, at least two.
    pub fn with_a_value_reloaded_on_every_arm(arms: usize) -> Self {
        assert!(arms >= 2);
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = Val::try_new(0).unwrap();
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();
        let block = |i| Block::try_new(i).unwrap();

        func.values = PrimaryMap::new();
        func.values
            .push(
                &mut output,
                ValData {
                    reg_class: TestMachine::BOTH_REGS_CLASS,
                    def: ValDef::InstResult {
                        inst: Inst::try_new(0).unwrap(),
                        i: 0,
                    },
                    remat: 0,
                },
            )
            .unwrap();

        let op = |pos, kind, constraint| InstData::Op {
            operands: vec![Operand::new(pos, kind, constraint, Some(val))],
            clobbers: vec![],
            side_effects: true,
        };
        let terminator = || InstData::Op {
            operands: vec![],
            clobbers: vec![],
            side_effects: true,
        };

        func.insts = PrimaryMap::new();
        let mut insts = vec![
            // `block0`: define the value in a register, clobber both
            // registers so that it can only cross on the stack, and fork.
            op(Position::Late, DefUse::Def, OperandConstraint::Reg(class)),
            InstData::Op {
                operands: vec![],
                clobbers: vec![
                    crate::Reg::try_new(0).unwrap(),
                    crate::Reg::try_new(1).unwrap(),
                ],
                side_effects: true,
            },
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: (1..=arms)
                    .map(|i| BlockCall {
                        target: block(i),
                        args: Vec::new(),
                    })
                    .collect(),
            },
        ];
        // Each arm: read it in a register, and return.
        for _ in 0..arms {
            insts.push(op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(class),
            ));
            insts.push(terminator());
        }
        for inst_data in insts {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: vec![],
                    insts: vec![inst(0), inst(1), inst(2)],
                    frequency: 0,
                },
            )
            .unwrap();
        for i in 0..arms {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts: vec![inst(3 + 2 * i), inst(4 + 2 * i)],
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A join whose terminator is its only instruction, and which forks to two
    /// arms that each first reload a spilled value into the register the
    /// join's parameter arrives in. The parameter is read only past a clobber,
    /// so it is spilled as it arrives.
    ///
    /// ```text
    /// block0: inst0  late def v0 (reg)
    ///         inst1  clobber both registers      // v0 crosses on the stack
    ///         inst2  late def v1 (rc0)           // pinned to r0
    ///         inst3  --> block1, block2
    /// block1: inst4  --> block3(v1)
    /// block2: inst5  --> block3(v1)
    /// block3(v2 in r0):
    ///         inst6  --> block4, block5          // the join's only instruction
    /// block4: inst7  early use v0 (rc0)
    ///         inst8  clobber both registers
    ///         inst9  early use v2 (rc0), return
    /// block5: the same as block4
    /// ```
    ///
    /// A move into `r0` hoisted before `block3`'s terminator would sit in the
    /// same gap the parameter arrives in, which `Output::block_param_allocs`
    /// promises holds it once that gap's edits have run.
    pub fn with_a_reload_demanded_where_a_parameter_arrives() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let v = |i| Val::try_new(i).unwrap();
        let block = |i| Block::try_new(i).unwrap();
        let inst = |i| Inst::try_new(i).unwrap();
        let first = RegClass::try_new(0).unwrap();
        let both = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();

        func.values = PrimaryMap::new();
        for (class, def) in [
            (
                TestMachine::BOTH_REGS_CLASS,
                ValDef::InstResult {
                    inst: inst(0),
                    i: 0,
                },
            ),
            (
                0,
                ValDef::InstResult {
                    inst: inst(2),
                    i: 0,
                },
            ),
            (
                0,
                ValDef::BlockParam {
                    block: block(3),
                    i: 0,
                },
            ),
        ] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: class,
                        def,
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let op = |operands: Vec<Operand>| InstData::Op {
            operands,
            clobbers: vec![],
            side_effects: true,
        };
        let branch = |targets: Vec<(Block, Vec<Val>)>| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: targets
                .into_iter()
                .map(|(target, args)| BlockCall { target, args })
                .collect(),
        };
        let use_ = |val, class| {
            Operand::new(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(class),
                Some(val),
            )
        };
        let clobber = || InstData::Op {
            operands: vec![],
            clobbers: vec![
                crate::Reg::try_new(0).unwrap(),
                crate::Reg::try_new(1).unwrap(),
            ],
            side_effects: true,
        };

        func.insts = PrimaryMap::new();
        for inst_data in [
            // `block0`
            op(vec![Operand::new(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Reg(both),
                Some(v(0)),
            )]),
            clobber(),
            op(vec![Operand::new(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Reg(first),
                Some(v(1)),
            )]),
            branch(vec![(block(1), vec![]), (block(2), vec![])]),
            // `block1` and `block2`
            branch(vec![(block(3), vec![v(1)])]),
            branch(vec![(block(3), vec![v(1)])]),
            // `block3`
            branch(vec![(block(4), vec![]), (block(5), vec![])]),
            // `block4` and `block5`
            op(vec![use_(v(0), first)]),
            clobber(),
            op(vec![use_(v(2), first)]),
            op(vec![use_(v(0), first)]),
            clobber(),
            op(vec![use_(v(2), first)]),
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        func.blocks = PrimaryMap::new();
        for (insts, params) in [
            (vec![inst(0), inst(1), inst(2), inst(3)], vec![]),
            (vec![inst(4)], vec![]),
            (vec![inst(5)], vec![]),
            (vec![inst(6)], vec![v(2)]),
            (vec![inst(7), inst(8), inst(9)], vec![]),
            (vec![inst(10), inst(11), inst(12)], vec![]),
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params,
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
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
                    Some(defined),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![
                    Operand::new(Position::Early, DefUse::Use, use_constraint, Some(defined)),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(0),
                        Some(tied),
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the tied instruction.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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
                    Some(defined),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        Some(defined),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(0),
                        Some(tied),
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            // The read that makes the tied use's value a survivor.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Any,
                    Some(defined),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the later read.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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
                    Some(defined),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![
                    // The plain read, at the same point as the tied one.
                    Operand::new(Position::Early, DefUse::Use, plain_read, Some(defined)),
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        Some(defined),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(1),
                        Some(tied),
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            // The read that makes the tied use's value a survivor.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Any,
                    Some(defined),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the later read.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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

    /// A single-block input in which each of `num_values` values belongs to
    /// `reg_class` and is defined by the instruction of the same index, the
    /// instructions carry `operands` in order, and the block ends with a
    /// terminator of its own so that `ensure_terminators` does not rewrite the
    /// reads before it.
    ///
    /// `reg_class` has to be a class `machine` has allocatable registers in,
    /// since every value here needs somewhere to live.
    fn defining_values_in_order(
        machine: TestMachine,
        reg_class: u8,
        num_values: usize,
        operands: Vec<Vec<Operand>>,
    ) -> Self {
        let clobbers = vec![Vec::new(); operands.len()];
        Self::defining_values_in_order_with_clobbers(
            machine, reg_class, num_values, operands, clobbers,
        )
    }

    /// As [`Self::defining_values_in_order`], but each instruction also
    /// clobbers the registers of the entry of `clobbers` with its index.
    fn defining_values_in_order_with_clobbers(
        machine: TestMachine,
        reg_class: u8,
        num_values: usize,
        operands: Vec<Vec<Operand>>,
        clobbers: Vec<Vec<Reg>>,
    ) -> Self {
        assert_eq!(operands.len(), clobbers.len());
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        func.values = PrimaryMap::new();
        for i in 0..num_values {
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

        let written = operands.clone();
        let written_clobbers = clobbers.clone();
        func.insts = PrimaryMap::new();
        let bodies = operands
            .into_iter()
            .zip(clobbers)
            .chain(core::iter::once((Vec::new(), Vec::new())));
        for (operands, clobbers) in bodies {
            func.insts
                .push(
                    &mut output,
                    InstData::Op {
                        operands,
                        clobbers,
                        side_effects: true,
                    },
                )
                .unwrap();
        }

        let mut input = Self::single_block(machine, func, output);

        // `fixup` relaxes an instruction whose fixed operands conflict, and
        // several of these fixtures exist to *be* that conflict, so put the
        // operands back exactly as written. Same for the clobbers, which
        // `fixup` drops wholesale when nothing else can give.
        for (i, (operands, clobbers)) in written.into_iter().zip(written_clobbers).enumerate() {
            let inst = Inst::try_new(i).unwrap();
            let written = input.func.insts[inst].operands_mut();
            assert_eq!(written.len(), operands.len());
            written.clone_from_slice(&operands);
            *input.func.insts[inst].clobbers_mut() = clobbers;
        }
        input
    }

    /// A single-block input on [`TestMachine::two_registers`] in which each of
    /// `num_values` values is defined by the instruction of the same index and
    /// the instructions carry `operands` in order.
    fn around_an_overwritten_read(num_values: usize, operands: Vec<Vec<Operand>>) -> Self {
        Self::defining_values_in_order(
            TestMachine::two_registers(),
            TestMachine::BOTH_REGS_CLASS,
            num_values,
            operands,
        )
    }

    /// A single-block input whose early read is pinned to the one register
    /// that its own instruction's late definition overwrites, and whose value
    /// survives that instruction.
    pub fn with_a_read_overwritten_by_a_fixed_def() -> Self {
        let defined = Val::try_new(0).unwrap();
        let clobbering = Val::try_new(1).unwrap();
        let first_reg = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();

        Self::around_an_overwritten_read(
            2,
            vec![
                vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    Some(defined),
                )],
                vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(first_reg),
                        Some(defined),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reg(first_reg),
                        Some(clobbering),
                    ),
                ],
                // The read that makes the pinned read's value a survivor.
                vec![Operand::new(
                    Position::Late,
                    DefUse::Use,
                    OperandConstraint::Any,
                    Some(defined),
                )],
            ],
        )
    }

    /// Like `with_a_read_overwritten_by_a_fixed_def`, but nothing reads the
    /// value again, so it dies at its pinned read.
    ///
    /// The control for the split: there is no later use to carry the value to,
    /// so its span simply ends where the definition takes the register, and
    /// construction has nothing to split. This allocated before the split
    /// existed and must keep allocating, with one span and no copy.
    pub fn with_a_dying_read_overwritten_by_a_fixed_def() -> Self {
        let defined = Val::try_new(0).unwrap();
        let clobbering = Val::try_new(1).unwrap();
        let first_reg = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();

        Self::around_an_overwritten_read(
            2,
            vec![
                vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    Some(defined),
                )],
                vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(first_reg),
                        Some(defined),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reg(first_reg),
                        Some(clobbering),
                    ),
                ],
            ],
        )
    }

    /// Like `with_a_read_overwritten_by_a_fixed_def`, but the overwriting
    /// instruction reads the survivor *twice*, both times pinned to the
    /// register it overwrites.
    ///
    /// Both reads deliver the same value to the same register over the same
    /// half-instruction, so they are one reservation and not two, which keeps
    /// reservation building from conflicting with itself.
    pub fn with_two_reads_overwritten_by_a_fixed_def() -> Self {
        let defined = Val::try_new(0).unwrap();
        let clobbering = Val::try_new(1).unwrap();
        let first_reg = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();
        let pinned_read = || {
            Operand::new(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(first_reg),
                Some(defined),
            )
        };

        Self::around_an_overwritten_read(
            2,
            vec![
                vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    Some(defined),
                )],
                vec![
                    pinned_read(),
                    pinned_read(),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reg(first_reg),
                        Some(clobbering),
                    ),
                ],
                vec![Operand::new(
                    Position::Late,
                    DefUse::Use,
                    OperandConstraint::Any,
                    Some(defined),
                )],
            ],
        )
    }

    /// A value *defined* into a pinned register, then read from that same
    /// register by an instruction whose tied definition overwrites it, and
    /// read once more after that.
    pub fn with_a_fixed_def_before_a_reuse_of_its_pinned_read() -> Self {
        let defined = Val::try_new(0).unwrap();
        let tied = Val::try_new(1).unwrap();
        let second_reg = RegClass::try_new(TestMachine::SECOND_REG_CLASS.into()).unwrap();

        Self::around_an_overwritten_read(
            2,
            vec![
                vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Reg(second_reg),
                    Some(defined),
                )],
                vec![
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(1),
                        Some(tied),
                    ),
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(second_reg),
                        Some(defined),
                    ),
                ],
                // The read that makes the value a survivor, so the piece
                // taking over from the definition has somewhere to be.
                vec![Operand::new(
                    Position::Late,
                    DefUse::Use,
                    OperandConstraint::Any,
                    Some(defined),
                )],
            ],
        )
    }

    /// Like `with_a_read_overwritten_by_a_fixed_def`, but the second operand
    /// *reads* `r0` late instead of defining it.
    ///
    /// Unsatisfiable, and must stay so: `r0` has to hold one value at the
    /// instruction's early point and a different one at its late point, and no
    /// move may be placed between the two halves of an instruction.
    pub fn with_a_late_read_conflicting_with_an_early_read() -> Self {
        let defined = Val::try_new(0).unwrap();
        let conflicting = Val::try_new(1).unwrap();
        let first_reg = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();

        Self::around_an_overwritten_read(
            2,
            vec![
                vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    Some(defined),
                )],
                vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    Some(conflicting),
                )],
                vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(first_reg),
                        Some(defined),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Use,
                        OperandConstraint::Reg(first_reg),
                        Some(conflicting),
                    ),
                ],
                vec![Operand::new(
                    Position::Late,
                    DefUse::Use,
                    OperandConstraint::Any,
                    Some(defined),
                )],
            ],
        )
    }

    /// Like `with_a_read_overwritten_by_a_fixed_def`, but the survivor is
    /// *defined* into `r0` early rather than read from it.
    ///
    /// Unsatisfiable, and must stay so: the instruction itself writes the
    /// value into `r0` at its early point, where the allocator cannot put it
    /// anywhere else, and overwrites `r0` at its late point with no gap
    /// between the two in which to move the value out.
    pub fn with_an_early_def_overwritten_by_a_late_def() -> Self {
        let defined = Val::try_new(0).unwrap();
        let clobbering = Val::try_new(1).unwrap();
        let first_reg = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();

        Self::around_an_overwritten_read(
            2,
            vec![
                vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Def,
                        OperandConstraint::Reg(first_reg),
                        Some(defined),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reg(first_reg),
                        Some(clobbering),
                    ),
                ],
                vec![Operand::new(
                    Position::Late,
                    DefUse::Use,
                    OperandConstraint::Any,
                    Some(defined),
                )],
            ],
        )
    }

    /// Two *different* values read from the one register at one point, with a
    /// definition overwriting it.
    ///
    /// Unsatisfiable, and must stay so: both reads claim `r0` over the early
    /// half. Validation names the two operands rather than letting it surface
    /// later as running out of registers.
    pub fn with_two_values_read_from_one_register() -> Self {
        let first = Val::try_new(0).unwrap();
        let second = Val::try_new(1).unwrap();
        let clobbering = Val::try_new(2).unwrap();
        let first_reg = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();
        let pinned_read = |val| {
            Operand::new(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(first_reg),
                Some(val),
            )
        };
        let later_read = |val| {
            Operand::new(
                Position::Late,
                DefUse::Use,
                OperandConstraint::Any,
                Some(val),
            )
        };

        Self::around_an_overwritten_read(
            3,
            vec![
                vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    Some(first),
                )],
                vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    Some(second),
                )],
                vec![
                    pinned_read(first),
                    pinned_read(second),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reg(first_reg),
                        Some(clobbering),
                    ),
                ],
                vec![later_read(first), later_read(second)],
            ],
        )
    }

    /// A definition tied to a read that names one register, whose own only
    /// other read wants it on the stack, on [`TestMachine::two_registers`].
    pub fn with_a_pinned_reuse_tie_read_on_the_stack() -> Self {
        let carried = Val::try_new(0).unwrap();
        let untied = Val::try_new(1).unwrap();
        let tied = Val::try_new(2).unwrap();
        let first = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();
        let both = RegClass::try_new(TestMachine::BOTH_REGS_CLASS.into()).unwrap();
        let def = |val| {
            Operand::new(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Any,
                Some(val),
            )
        };
        let reuse_def = |val| {
            Operand::new(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Reuse(0),
                Some(val),
            )
        };
        let read =
            |val, constraint| Operand::new(Position::Early, DefUse::Use, constraint, Some(val));

        Self::defining_values_in_order(
            TestMachine::two_registers(),
            TestMachine::BOTH_REGS_CLASS,
            3,
            vec![
                vec![def(carried)],
                // An ordinary tie, which puts a register floor under
                // `carried`: a definition cannot reuse a stack slot.
                vec![read(carried, OperandConstraint::Any), reuse_def(untied)],
                // The tie whose target names one register, beside a wider
                // read of the same value at the same point, which keeps its
                // piece in a register once the tie stops asking for one.
                vec![
                    read(carried, OperandConstraint::Reg(first)),
                    reuse_def(tied),
                    read(carried, OperandConstraint::Reg(both)),
                ],
                // The read that asks for the tied definition's value on the
                // stack, which nothing now stops it from getting.
                vec![
                    read(tied, OperandConstraint::Stack),
                    read(untied, OperandConstraint::Any),
                ],
            ],
        )
    }

    /// A value read twice at one point under two classes that overlap in
    /// exactly one register, on [`TestMachine::overlapping_pairs`].
    pub fn with_a_value_read_under_overlapping_classes() -> Self {
        let pinned = Val::try_new(0).unwrap();
        let first = Val::try_new(1).unwrap();
        let second = Val::try_new(2).unwrap();
        let low = RegClass::try_new(TestMachine::LOW_PAIR_CLASS.into()).unwrap();
        let high = RegClass::try_new(TestMachine::HIGH_PAIR_CLASS.into()).unwrap();
        let def = |val| {
            Operand::new(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Any,
                Some(val),
            )
        };
        let read = |val, class| {
            Operand::new(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(class),
                Some(val),
            )
        };
        let plain_read = |val| {
            Operand::new(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Any,
                Some(val),
            )
        };

        Self::defining_values_in_order(
            TestMachine::overlapping_pairs(),
            TestMachine::ALL_THREE_REGS_CLASS,
            3,
            vec![
                vec![def(pinned)],
                vec![def(first)],
                vec![def(second)],
                // The two reads whose classes leave exactly one register
                // between them.
                vec![read(pinned, low), read(pinned, high)],
                // The reads that keep the other two values live across it.
                vec![plain_read(first), plain_read(second)],
            ],
        )
    }

    /// A value defined and never read, on a machine whose two registers are
    /// both spoken for across its definition.
    pub fn with_a_def_only_value_under_pressure() -> Self {
        let first = Val::try_new(0).unwrap();
        let second = Val::try_new(1).unwrap();
        let unread = Val::try_new(2).unwrap();
        let r0 = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();
        let r1 = RegClass::try_new(TestMachine::SECOND_REG_CLASS.into()).unwrap();
        let def = |val| {
            Operand::new(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Any,
                Some(val),
            )
        };

        Self::around_an_overwritten_read(
            3,
            vec![
                vec![def(first)],
                vec![def(second)],
                // The definition no one consumes, made while both registers
                // are still carrying values that are read below.
                vec![def(unread)],
                vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(r0),
                        Some(first),
                    ),
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(r1),
                        Some(second),
                    ),
                ],
            ],
        )
    }

    /// A value read from memory on a machine with a single allocatable
    /// register, which another value holds across that read.
    pub fn with_a_stack_constrained_value_under_pressure() -> Self {
        let mut machine = TestMachine::two_registers();
        machine.set_regs_per_bank(1);

        let spilled = Val::try_new(0).unwrap();
        let resident = Val::try_new(1).unwrap();
        let both = RegClass::try_new(TestMachine::BOTH_REGS_CLASS.into()).unwrap();
        let def = |val| {
            Operand::new(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Any,
                Some(val),
            )
        };

        Self::defining_values_in_order(
            machine,
            TestMachine::BOTH_REGS_CLASS,
            2,
            vec![
                vec![def(spilled)],
                vec![def(resident)],
                vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Stack,
                        Some(spilled),
                    ),
                    // The one register the machine has, held by something
                    // else, so the read above cannot quietly be given it.
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(both),
                        Some(resident),
                    ),
                ],
                // Read back into that same register, so the value really does
                // make the round trip through memory.
                vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Reg(both),
                    Some(spilled),
                )],
            ],
        )
    }

    /// Three values that each need a register *group*, on a machine with two
    /// groups to go around.
    pub fn with_three_values_needing_two_register_groups() -> Self {
        let carried = Val::try_new(0).unwrap();
        let first = Val::try_new(1).unwrap();
        let second = Val::try_new(2).unwrap();
        let groups = RegClass::try_new(TestMachine::EITHER_GROUP_CLASS.into()).unwrap();
        let def = |val| {
            Operand::new(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Any,
                Some(val),
            )
        };
        let read = |val| {
            Operand::new(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(groups),
                Some(val),
            )
        };

        Self::defining_values_in_order(
            TestMachine::groups_and_registers(),
            TestMachine::EITHER_GROUP_CLASS,
            3,
            vec![
                vec![def(carried)],
                vec![def(first)],
                vec![def(second)],
                // Both of these take a group while `carried` is still live,
                // which is one group more than the bank has.
                vec![read(first)],
                vec![read(second)],
                vec![read(carried)],
            ],
        )
    }

    /// One value read twice at one instruction, once out of each of the
    /// machine's two registers, and read again afterwards.
    ///
    /// Satisfiable only because neither read constrains the value: it lives in
    /// one register of its own and a move delivers it into the other. No
    /// single assignment satisfies both reads, so this is the shape that says
    /// a fixed operand is not a constraint.
    pub fn with_one_value_read_from_two_registers() -> Self {
        let defined = Val::try_new(0).unwrap();
        let first_reg = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();
        let second_reg = RegClass::try_new(TestMachine::SECOND_REG_CLASS.into()).unwrap();
        let pinned_read = |class| {
            Operand::new(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(class),
                Some(defined),
            )
        };

        Self::around_an_overwritten_read(
            1,
            vec![
                vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    Some(defined),
                )],
                vec![pinned_read(first_reg), pinned_read(second_reg)],
                vec![Operand::new(
                    Position::Late,
                    DefUse::Use,
                    OperandConstraint::Any,
                    Some(defined),
                )],
            ],
        )
    }

    /// A definition pinned to `r0` whose value is never read, beside a value
    /// that is live across it.
    pub fn with_a_clobber_beside_a_live_through_value() -> Self {
        let survivor = Val::try_new(0).unwrap();
        let clobbered = Val::try_new(1).unwrap();
        let first_reg = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();

        Self::around_an_overwritten_read(
            2,
            vec![
                vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    Some(survivor),
                )],
                vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Reg(first_reg),
                    Some(clobbered),
                )],
                vec![Operand::new(
                    Position::Late,
                    DefUse::Use,
                    OperandConstraint::Any,
                    Some(survivor),
                )],
            ],
        )
    }

    /// A value read in the early half of an instruction whose *late* half is
    /// full, and which survives the instruction.
    pub fn with_an_early_read_under_a_full_late_half() -> Self {
        let carried = Val::try_new(0).unwrap();
        let both_regs = RegClass::try_new(TestMachine::BOTH_REGS_CLASS.into()).unwrap();
        let first_reg = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();
        let second_reg = RegClass::try_new(TestMachine::SECOND_REG_CLASS.into()).unwrap();

        Self::around_an_overwritten_read(
            3,
            vec![
                vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    Some(carried),
                )],
                vec![
                    // Constrained to the whole class rather than to one
                    // register, so that it constrains its bundle instead of
                    // becoming a reservation.
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(both_regs),
                        Some(carried),
                    ),
                    // These two take both registers over the late half.
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reg(first_reg),
                        Some(Val::try_new(1).unwrap()),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reg(second_reg),
                        Some(Val::try_new(2).unwrap()),
                    ),
                ],
                // Makes the value a survivor, so its span reaches past the
                // half it is read in.
                vec![Operand::new(
                    Position::Late,
                    DefUse::Use,
                    OperandConstraint::Any,
                    Some(carried),
                )],
            ],
        )
    }

    /// An instruction that clobbers every allocatable register, beside a
    /// value whose only operand on it is an *early* read.
    ///
    /// The read holds the early half and the clobbers the late one, so the
    /// input is allocatable.
    ///
    /// The read *dies* here, which is what makes this a test of the clobbers.
    pub fn with_an_early_read_beside_a_clobber_of_every_register() -> Self {
        let read = Val::try_new(0).unwrap();
        let both = RegClass::try_new(TestMachine::BOTH_REGS_CLASS.into()).unwrap();
        let regs = [Reg::try_new(0).unwrap(), Reg::try_new(1).unwrap()];

        Self::defining_values_in_order_with_clobbers(
            TestMachine::two_registers(),
            TestMachine::BOTH_REGS_CLASS,
            1,
            vec![
                vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    Some(read),
                )],
                // In a register, or the allocator sidesteps the clobbers by
                // leaving the value on the stack.
                vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Reg(both),
                    Some(read),
                )],
            ],
            vec![Vec::new(), Vec::from(regs)],
        )
    }

    /// A value reloaded into a register, clobbered out of it, and read in a
    /// register again.
    ///
    /// The second reload is only redundant if the clobber did not happen, so
    /// `redundant_move_elimination` has to account for clobbers to keep it.
    pub fn with_a_reload_clobbered_before_its_next_read() -> Self {
        let read = Val::try_new(0).unwrap();
        let both = RegClass::try_new(TestMachine::BOTH_REGS_CLASS.into()).unwrap();
        let regs = vec![Reg::try_new(0).unwrap(), Reg::try_new(1).unwrap()];

        let in_a_reg =
            |pos, kind| Operand::new(pos, kind, OperandConstraint::Reg(both), Some(read));

        Self::defining_values_in_order_with_clobbers(
            TestMachine::two_registers(),
            TestMachine::BOTH_REGS_CLASS,
            1,
            vec![
                vec![in_a_reg(Position::Late, DefUse::Def)],
                // Forces the spill the reloads below undo.
                vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Stack,
                    Some(read),
                )],
                vec![in_a_reg(Position::Early, DefUse::Use)],
                // Destroys whatever register that read landed in.
                vec![],
                vec![in_a_reg(Position::Early, DefUse::Use)],
            ],
            vec![Vec::new(), Vec::new(), Vec::new(), regs, Vec::new()],
        )
    }

    /// A block whose only instruction is a terminator that carries no operands
    /// but *does* clobber, branching to a merge block that takes a parameter.
    ///
    /// Exercises `terminator_leaves_the_gap_free`, where the operand count
    /// alone says the departure gap is usable and the clobbers say it is not.
    /// `move_generation::edge_position` and
    /// `checker::departs_from_its_first_gap` both consult it and must agree.
    ///
    /// The merge has two predecessors so that the checker pins the parameter
    /// against an arrival state rather than skipping the check.
    pub fn with_a_clobbering_terminator_before_a_merge() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let first = Val::try_new(0).unwrap();
        let second = Val::try_new(1).unwrap();
        let param = Val::try_new(2).unwrap();
        let merge = Block::try_new(3).unwrap();
        let both = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();
        let r0 = Reg::try_new(0).unwrap();

        func.values = PrimaryMap::new();
        for def in [
            ValDef::InstResult {
                inst: Inst::try_new(0).unwrap(),
                i: 0,
            },
            ValDef::InstResult {
                inst: Inst::try_new(3).unwrap(),
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
            operands: vec![Operand::new(pos, kind, constraint, Some(val))],
            clobbers: vec![],
            side_effects: true,
        };
        let call = |target, args: &[Val]| BlockCall {
            target,
            args: args.to_vec(),
        };

        func.insts = PrimaryMap::new();
        for inst in [
            // `block0`: branch two ways, giving the merge two predecessors.
            op(Position::Late, DefUse::Def, OperandConstraint::Any, first),
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(both),
                first,
            ),
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: vec![
                    call(Block::try_new(1).unwrap(), &[]),
                    call(Block::try_new(2).unwrap(), &[]),
                ],
            },
            // `block1`: the merge's other predecessor.
            op(Position::Late, DefUse::Def, OperandConstraint::Any, second),
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: vec![call(merge, &[second])],
            },
            // `block2`: the block under test, one clobbering terminator.
            InstData::Branch {
                operands: vec![],
                clobbers: vec![r0],
                targets: vec![call(merge, &[first])],
            },
            // `block3`: read the parameter from a register.
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(both),
                param,
            ),
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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
            func.blocks.push(&mut output, block).unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();

        // `fixup` drops clobbers to resolve a conflict, and the clobber is
        // the point here.
        *input.func.insts[inst(5)].clobbers_mut() = vec![r0];
        input
    }

    /// A value defined into `r0` by a block's *terminator*, and read under
    /// `read` in the block it branches to.
    pub fn with_a_fixed_def_on_a_terminator(read: OperandConstraint) -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let defined = Val::try_new(0).unwrap();
        let target = Block::try_new(1).unwrap();
        let first_reg = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();

        func.values = PrimaryMap::new();
        func.values
            .push(
                &mut output,
                ValData {
                    reg_class: TestMachine::BOTH_REGS_CLASS,
                    def: ValDef::InstResult {
                        inst: Inst::try_new(0).unwrap(),
                        i: 0,
                    },
                    remat: 0,
                },
            )
            .unwrap();

        func.insts = PrimaryMap::new();
        for inst in [
            // The terminator that defines the value, into the register it
            // names and nowhere else.
            InstData::Branch {
                operands: vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Reg(first_reg),
                    Some(defined),
                )],
                clobbers: vec![],
                targets: vec![BlockCall {
                    target,
                    args: vec![],
                }],
            },
            // The read, and then a terminator of the block's own so that
            // `ensure_terminators` does not take the read away.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    read,
                    Some(defined),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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
                insts: vec![inst(0)],
                frequency: 0,
            },
            BlockData {
                params: vec![],
                insts: vec![inst(1), inst(2)],
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

    /// A terminator that passes a value it defines itself along one of its own
    /// out-edges, which is Cranelift's `try_call`'s shape.
    pub fn with_a_terminator_passing_its_own_result() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let defined = Val::try_new(0).unwrap();
        let param = Val::try_new(1).unwrap();
        let target = Block::try_new(1).unwrap();

        func.values = PrimaryMap::new();
        // The terminator's result, and the parameter it feeds.
        for def in [
            ValDef::InstResult {
                inst: Inst::try_new(0).unwrap(),
                i: 0,
            },
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

        func.insts = PrimaryMap::new();
        for inst in [
            // The terminator, defining the value and passing it onwards.
            InstData::Branch {
                operands: vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    Some(defined),
                )],
                clobbers: vec![],
                targets: vec![BlockCall {
                    target,
                    args: vec![defined],
                }],
            },
            // A read of the parameter, plus a terminator so that
            // `ensure_terminators` does not take the read away.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Any,
                    Some(param),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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
                insts: vec![inst(0)],
                frequency: 0,
            },
            BlockData {
                params: vec![param],
                insts: vec![inst(1), inst(2)],
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

    /// A definition pinned to a register at the first instruction of a loop
    /// body, beside a read of another value pinned to that same register.
    pub fn with_a_fixed_def_spilled_beside_a_fixed_read() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let read = Val::try_new(0).unwrap();
        let defined = Val::try_new(1).unwrap();
        let first_reg = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();

        // Both values can only ever be in `r0`, which is what keeps the
        // register contended all the way around the loop.
        func.values = PrimaryMap::new();
        for inst in [0usize, 4] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::FIRST_REG_CLASS,
                        def: ValDef::InstResult {
                            inst: Inst::try_new(inst).unwrap(),
                            i: 0,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let block = |b: usize| Block::try_new(b).unwrap();
        let branch = |target: usize| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: vec![BlockCall {
                target: block(target),
                args: vec![],
            }],
        };
        let op = |operands: Vec<Operand>| InstData::Op {
            operands,
            clobbers: vec![],
            side_effects: true,
        };

        func.insts = PrimaryMap::new();
        for inst in [
            // The value the loop body reads from the register, defined
            // before the loop and live through all of it.
            op(vec![Operand::new(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Any,
                Some(read),
            )]),
            branch(2),
            // The loop's other block, whose read gives the body's value a
            // second span and so a split between spans.
            op(vec![Operand::new(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Any,
                Some(defined),
            )]),
            branch(2),
            // The loop body: the pinned definition beside the pinned read,
            // then a read of the definition, then back around.
            op(vec![
                Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Reg(first_reg),
                    Some(defined),
                ),
                Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Reg(first_reg),
                    Some(read),
                ),
            ]),
            op(vec![Operand::new(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Any,
                Some(defined),
            )]),
            branch(1),
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i: usize| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        for insts in [
            vec![inst(0), inst(1)],
            vec![inst(2), inst(3)],
            vec![inst(4), inst(5), inst(6)],
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A value we always recompute, pinned to both registers at once by the
    /// first instruction of a block that nothing delivers it to.
    ///
    /// ```ignore
    /// block0: inst0  early def v0 (reg)
    ///         inst1  --> block1, block2
    /// block1: inst2  early def v1 (reg)      // v0 is live through here, but
    ///         inst3  early def v2 (reg)      // never mentioned, and v1 and v2
    ///         inst4  early use v1, use v2    // want both registers
    ///         inst5  --> block3
    /// block2: inst6  returns
    /// block3: inst7  early use v0 in r0,     // one pinned read per register,
    ///                early use v0 in r1,     // at the block's very start,
    ///                early use v0 (reg)      // and one that just wants one
    ///         inst8  returns
    /// ```
    ///
    /// The crowded block means the piece crossing it is worth no location at
    /// all, so nothing delivers `block3`'s piece either: only `resolve`'s
    /// recomputation fills it, and that goes *after* the gap's moves. The
    /// piece takes one reserved register and the other reservation still has
    /// to be filled, so this is where a reservation arrival must name no
    /// source at all: the source it records is the one the piece's own
    /// destination then finds, and a piece sourced from itself is never
    /// filled.
    pub fn with_a_recomputed_value_pinned_at_a_block_start() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = |i| Val::try_new(i).unwrap();
        let block = |i| Block::try_new(i).unwrap();
        let inst = |i| Inst::try_new(i).unwrap();
        let reg = OperandConstraint::Reg(
            RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap(),
        );
        let first_reg = OperandConstraint::Reg(
            RegClass::try_new(usize::from(TestMachine::FIRST_REG_CLASS)).unwrap(),
        );
        let second_reg = OperandConstraint::Reg(
            RegClass::try_new(usize::from(TestMachine::SECOND_REG_CLASS)).unwrap(),
        );

        // `v0`, carried past the crowded block, and the two values that crowd
        // it.
        func.values = PrimaryMap::new();
        for i in [0, 2, 3] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def: ValDef::InstResult {
                            inst: inst(i),
                            i: 0,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let operand =
            |kind, constraint, v| Operand::new(Position::Early, kind, constraint, Some(v));
        let def = |v| InstData::Op {
            operands: vec![operand(DefUse::Def, reg, v)],
            clobbers: vec![],
            side_effects: true,
        };
        let branch = |targets: &[usize]| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: targets
                .iter()
                .map(|&t| BlockCall {
                    target: block(t),
                    args: vec![],
                })
                .collect(),
        };

        func.insts = PrimaryMap::new();
        for inst_data in [
            // `block0` defines the value.
            def(val(0)),
            branch(&[1, 2]),
            // `block1` never mentions it, and wants both registers itself.
            def(val(1)),
            def(val(2)),
            InstData::Op {
                operands: vec![
                    operand(DefUse::Use, reg, val(1)),
                    operand(DefUse::Use, reg, val(2)),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            branch(&[3]),
            // `block2` is the other way out of `block0`.
            branch(&[]),
            // `block3` reads it at its very first point, pinned to each of
            // the two registers and free to pick one of them.
            InstData::Op {
                operands: vec![
                    operand(DefUse::Use, first_reg, val(0)),
                    operand(DefUse::Use, second_reg, val(0)),
                    operand(DefUse::Use, reg, val(0)),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            branch(&[]),
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        func.blocks = PrimaryMap::new();
        for insts in [
            vec![inst(0), inst(1)],
            vec![inst(2), inst(3), inst(4), inst(5)],
            vec![inst(6)],
            vec![inst(7), inst(8)],
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input.set_remat_costs(Some(RematCost::AlwaysRemat));
        input
    }

    /// A value reloaded into one register group at the very instruction where
    /// a fixed read holds the other order of those same two registers for it.
    pub fn with_a_reload_under_a_reversed_group_reservation() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = Val::try_new(0).unwrap();
        let either_order = RegClass::try_new(TestMachine::EITHER_ORDER_CLASS.into()).unwrap();
        let reversed = RegClass::try_new(TestMachine::REVERSED_GROUP_CLASS.into()).unwrap();

        func.values = PrimaryMap::new();
        func.values
            .push(
                &mut output,
                ValData {
                    reg_class: TestMachine::EITHER_ORDER_CLASS,
                    def: ValDef::InstResult {
                        inst: Inst::try_new(0).unwrap(),
                        i: 0,
                    },
                    remat: 0,
                },
            )
            .unwrap();

        let read = |constraint| Operand::new(Position::Early, DefUse::Use, constraint, Some(val));

        func.insts = PrimaryMap::new();
        for operands in [
            // Defined in whichever group the allocator likes.
            vec![Operand::new(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Any,
                Some(val),
            )],
            // Read on the stack, which spills it.
            vec![read(OperandConstraint::Stack)],
            // Read back in either order, which reloads it, beside a read
            // pinned to the reversed order, which holds both registers.
            vec![
                read(OperandConstraint::Reg(either_order)),
                read(OperandConstraint::Reg(reversed)),
            ],
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the reads.
            Vec::new(),
        ] {
            func.insts
                .push(
                    &mut output,
                    InstData::Op {
                        operands,
                        clobbers: vec![],
                        side_effects: true,
                    },
                )
                .unwrap();
        }

        Self::single_block(TestMachine::register_groups_in_two_orders(), func, output)
    }

    /// A read pinned to a register group beside a read pinned to one of that
    /// group's own registers.
    ///
    /// Unsatisfiable, and must stay so: the group holds `r0` and `r1`, the
    /// other read names `r0`, and the two deliver different values. This is
    /// the conflict two fixed operands can have without naming the same
    /// class, which is why the check counts register *units*.
    pub fn with_a_group_read_overlapping_a_fixed_read() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let grouped = Val::try_new(0).unwrap();
        let scalar = Val::try_new(1).unwrap();
        let group = RegClass::try_new(TestMachine::PAIRED_GROUP_CLASS.into()).unwrap();
        let in_the_group = RegClass::try_new(TestMachine::GROUPED_REG_CLASS.into()).unwrap();

        func.values = PrimaryMap::new();
        for (i, reg_class) in [
            TestMachine::PAIRED_GROUP_CLASS,
            TestMachine::UNGROUPED_REGS_CLASS,
        ]
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

        let def = |val| InstData::Op {
            operands: vec![Operand::new(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Any,
                Some(val),
            )],
            clobbers: vec![],
            side_effects: true,
        };
        let read = |class, val| {
            Operand::new(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(class),
                Some(val),
            )
        };
        let operands = vec![read(group, grouped), read(in_the_group, scalar)];

        func.insts = PrimaryMap::new();
        for inst in [
            def(grouped),
            def(scalar),
            InstData::Op {
                operands: operands.clone(),
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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
                    params: vec![],
                    insts: vec![inst(0), inst(1), inst(2), inst(3)],
                    frequency: 0,
                },
            )
            .unwrap();

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::a_group_and_one_of_its_registers(),
            func,
        };
        input.fixup();

        // `fixup` relaxes conflicting fixed operands; this fixture exists to
        // *be* that conflict, so put the two reads back as written.
        let written = input.func.insts[inst(2)].operands_mut();
        assert_eq!(written.len(), operands.len());
        written.clone_from_slice(&operands);
        input
    }

    /// Like `with_two_reads_and_a_reuse_of_a_surviving_value`, but with an
    /// *earlier* read pinned to `r0` and the tie pinned to `r1`.
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
                    Some(defined),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            // The pinned read, on an instruction of its own so that it is not
            // part of the tie's run.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Reg(first_reg),
                    Some(defined),
                )],
                clobbers: vec![],
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
                        Some(defined),
                    ),
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        Some(defined),
                    ),
                    // The tie's target, which the pinned read cannot share a
                    // register with.
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(second_reg),
                        Some(defined),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(2),
                        Some(tied),
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            // The read that makes the tied use's value a survivor.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Any,
                    Some(defined),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the later read.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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

    /// The mirror image of `with_a_pinned_read_before_a_reuse_that_reads_twice`:
    /// the tie names the *unpinned* read, and the sibling beside it is the one
    /// pinned to `r1`, while an earlier read is pinned to the disjoint `r0`.
    pub fn with_a_pinned_read_before_a_reuse_of_an_unpinned_read() -> Self {
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
                    Some(defined),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            // The pinned read, on an instruction of its own so that it is not
            // part of the tie's run, and so that its piece is already claimed
            // for `r0` by the time the tie's point is reached.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Reg(first_reg),
                    Some(defined),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![
                    // The tie's target, demanding nothing of its own.
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        Some(defined),
                    ),
                    // The sibling at the same point that pins the run to `r1`,
                    // which the earlier read's `r0` cannot satisfy.
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(second_reg),
                        Some(defined),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(0),
                        Some(tied),
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the reads.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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

    /// A tie whose target *dies* at it, but whose piece an earlier read has
    /// already pinned to `r1`, while the definition tied to it is read from the
    /// disjoint `r0`.
    pub fn with_a_pinned_read_before_a_reuse_of_a_dying_value() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let defined = Val::try_new(0).unwrap();
        let tied = Val::try_new(1).unwrap();

        let first_reg = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();
        let second_reg = RegClass::try_new(TestMachine::SECOND_REG_CLASS.into()).unwrap();
        let both_regs = RegClass::try_new(TestMachine::BOTH_REGS_CLASS.into()).unwrap();

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
                    Some(defined),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            // The read that pins the piece to `r1`, on an instruction of its
            // own so that it is not part of the tie's run.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Reg(second_reg),
                    Some(defined),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![
                    // The tie's target, under a class holding both registers,
                    // and the value's last read.
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(both_regs),
                        Some(defined),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(0),
                        Some(tied),
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            // The tied definition wants `r0`, which the pinned read's `r1`
            // cannot satisfy.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Reg(first_reg),
                    Some(tied),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the reads.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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
                    Some(defined),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
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
                        Some(defined),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(0),
                        Some(tied),
                    ),
                ],
                clobbers: vec![],
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
                        Some(defined),
                    ),
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        Some(tied),
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the reads.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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
                    Some(defined),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        Some(defined),
                    ),
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        Some(defined),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(0),
                        Some(first_tied),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(1),
                        Some(second_tied),
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            // The read that makes the tied value a survivor, if it has one.
            InstData::Op {
                operands: if survives {
                    vec![Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        Some(defined),
                    )]
                } else {
                    vec![]
                },
                clobbers: vec![],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the read.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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

    /// Turn off every move-elimination pass.
    ///
    /// For a test that needs a particular edit to survive into the output,
    /// typically so it can perturb it and watch the checker object. Elimination
    /// is generally *right* to drop such an edit.
    pub fn disable_move_elimination(&mut self) {
        self.options.redundant_move_elimination_level = MoveEliminationLevel::None;
        self.options.dead_move_elimination_level = MoveEliminationLevel::None;
        self.options.hoist_demanded_moves = false;
    }

    /// Report `remat` for every value in this function that may legally carry
    /// it; the rest keep no cost at all.
    ///
    /// See [`can_remat`]: a block parameter, or a value that occupies a
    /// register group, cannot be rematerialized whatever a caller asks for,
    /// and validation rejects an input that claims otherwise.
    pub fn set_remat_costs(&mut self, remat: Option<RematCost>) {
        let index = REMAT_COSTS
            .iter()
            .position(|r| *r == remat)
            .expect("not a remat cost a `TestFunction` can report");
        let index = u8::try_from(index).unwrap();

        let machine = self.machine.build();
        let vals: Vec<Val> = self.func.values.iter().map(|(val, _)| val).collect();
        for val in vals {
            self.func.values[val].remat = if can_remat(&self.func, &machine, val) {
                index
            } else {
                NO_REMAT
            };
        }
    }

    /// A two-block input passing one value along an edge as a block argument,
    /// the argument's use constrained by `arg` and the parameter's by `param`:
    /// the smallest function with an argument-to-parameter affinity to find. On
    /// [`TestMachine::two_registers`], `Reg(rc2)` and `Stack` conflict; `rc0`
    /// and `rc1` are singletons, so they are fixed operands and constrain
    /// nothing.
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
            operands: vec![Operand::new(pos, kind, constraint, Some(val))],
            clobbers: vec![],
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
                clobbers: vec![],
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
                clobbers: vec![],
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

    /// A value recomputed at a read, and another value spilled and reloaded
    /// after it: a rematerialization at an earlier position than a move.
    ///
    /// ```ignore
    /// block0: inst0  late def v0 (any)              // v0 is always recomputed
    ///         inst1  mentions nothing               // the gap in v0's live range
    ///         inst2  early use v0, late def v1      // v0 recomputed here
    ///         inst3  early use v1 (stack)           // v1 lands in a slot
    ///         inst4  early use v1 (reg)             // and is reloaded out of it
    ///         inst5  terminator
    /// ```
    ///
    /// The instruction that mentions nothing is what leaves a gap between two
    /// of v0's spans, so the read after it has nothing to receive the value
    /// from and is filled by a rematerialization. v1 is read on the stack and
    /// then in a register, so it is reloaded, and its definition reads an
    /// operand, so no remat cost of [`TestInput::set_remat_costs`] lands on it
    /// and that reload stays a move. The rematerialization comes at the earlier
    /// position of the two, which is the only shape in which the index a move
    /// is emitted with is not the index it ends up at.
    pub fn with_a_recomputed_read_before_a_spill_and_a_reload() -> Self {
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let recomputed = Val::try_new(0).unwrap();
        let spilled = Val::try_new(1).unwrap();

        func.values = PrimaryMap::new();
        for i in [0, 2] {
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

        let op = |pos, kind, constraint, val| InstData::Op {
            operands: vec![Operand::new(pos, kind, constraint, Some(val))],
            clobbers: vec![],
            side_effects: true,
        };
        let nothing = || InstData::Op {
            operands: vec![],
            clobbers: vec![],
            side_effects: true,
        };

        func.insts = PrimaryMap::new();
        for inst in [
            op(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Any,
                recomputed,
            ),
            nothing(),
            InstData::Op {
                operands: vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        Some(recomputed),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Any,
                        Some(spilled),
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Stack,
                spilled,
            ),
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(class),
                spilled,
            ),
            nothing(),
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        func.blocks = PrimaryMap::new();
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: vec![],
                    insts: (0..6).map(|i| Inst::try_new(i).unwrap()).collect(),
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
        input.set_remat_costs(Some(RematCost::AlwaysRemat));
        input
    }

    /// Three values wanting a register at a point where only two of them can
    /// have one, the odd one out being recomputable and read in a hot block.
    ///
    /// ```ignore
    /// block0: inst0  late def v0 (any)                // v0 is recomputable
    ///         inst1  early use v0, late def v1 (any)  // v1's definition reads
    ///         inst2  early use v1, late def v2 (any)  // an operand, and so
    ///         inst3  --> block1                       // does v2's, so neither
    /// block1: inst4  late def v3 (any)                // of them is
    ///         inst5  early use v3 (any)               // recomputable; v3 is
    ///         inst6  --> block2
    /// block2: inst7  early use v1 (any)
    ///         inst8  early use v2 (any)
    ///         inst9  returns
    /// ```
    ///
    /// `block1` runs a hundred times as often as its neighbours, and v1 and v2
    /// hold both registers across it while paying only what their uses in the
    /// cooler blocks are worth. v3 is minimal, but its use is worth a hot stack
    /// access -- far more -- so it can take a register from one of them.
    pub fn with_a_recomputed_read_under_pressure() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = |i| Val::try_new(i).unwrap();
        let block = |i| Block::try_new(i).unwrap();
        let inst = |i| Inst::try_new(i).unwrap();
        let any = OperandConstraint::Any;

        func.values = PrimaryMap::new();
        for def in [0, 1, 2, 4] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def: ValDef::InstResult {
                            inst: inst(def),
                            i: 0,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let def = |v| InstData::Op {
            operands: vec![Operand::new(Position::Late, DefUse::Def, any, Some(val(v)))],
            clobbers: vec![],
            side_effects: true,
        };
        let read = |v| InstData::Op {
            operands: vec![Operand::new(
                Position::Early,
                DefUse::Use,
                any,
                Some(val(v)),
            )],
            clobbers: vec![],
            side_effects: true,
        };
        // A read that has to be in a register, so the value it reads holds one
        // all the way from its definition, over the hot block in between.
        let read_in_a_register = |v| InstData::Op {
            operands: vec![Operand::new(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(
                    RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap(),
                ),
                Some(val(v)),
            )],
            clobbers: vec![],
            side_effects: true,
        };
        // A definition that reads an operand, so its value gets no remat cost.
        let read_and_def = |read, defined| InstData::Op {
            operands: vec![
                Operand::new(Position::Early, DefUse::Use, any, Some(val(read))),
                Operand::new(Position::Late, DefUse::Def, any, Some(val(defined))),
            ],
            clobbers: vec![],
            side_effects: true,
        };
        let branch = |target| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: vec![BlockCall {
                target: block(target),
                args: vec![],
            }],
        };

        func.insts = PrimaryMap::new();
        for inst_data in [
            def(0),
            read_and_def(0, 1),
            read_and_def(1, 2),
            branch(1),
            def(3),
            read(3),
            branch(2),
            read_in_a_register(1),
            read_in_a_register(2),
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: vec![],
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        func.blocks = PrimaryMap::new();
        for insts in [
            vec![inst(0), inst(1), inst(2), inst(3)],
            vec![inst(4), inst(5), inst(6)],
            vec![inst(7), inst(8), inst(9)],
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input.set_remat_costs(Some(RematCost::AlwaysRemat));
        input.set_block_frequency(block(1), BlockFrequency::HOT);
        input
    }

    /// A read that must be in a register, at a point where every register is
    /// held by a value that would rather keep one but does not need one.
    ///
    /// ```ignore
    /// block0: inst0  late def v0 (any)
    ///         inst1  late def v1 (any)
    ///         inst2  late def v2 (any)
    ///         inst3  early use v2 (reg)   // minimal: nowhere left to split
    ///         inst4  --> block1
    /// block1: inst5  early use v0 (any)   // a hundred times as often as
    ///         inst6  early use v1 (any)   // block0, so neither of these is
    ///         inst7  returns              // cheap enough to evict
    /// ```
    ///
    /// v0 and v1 hold both registers across inst3, and their hot reads make
    /// them dearer than v2, which is as cheap as a bundle gets. Spill weight
    /// alone would leave v2 with nothing to buy a register with, because
    /// eviction only takes a victim strictly cheaper than the bundle being
    /// placed and there is nothing cheaper than minimal. But v2 is pinned to a
    /// register and v0 and v1 are not -- they are free to live on the stack at
    /// every one of their uses -- so the function does fit on the machine, and
    /// eviction has to weigh how stuck a bundle is ahead of what it is worth.
    pub fn with_a_minimal_register_read_among_stackable_values() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = |i| Val::try_new(i).unwrap();
        let block = |i| Block::try_new(i).unwrap();
        let inst = |i| Inst::try_new(i).unwrap();
        let any = OperandConstraint::Any;
        let reg =
            OperandConstraint::Reg(RegClass::try_new(TestMachine::BOTH_REGS_CLASS.into()).unwrap());

        func.values = PrimaryMap::new();
        for def in [0, 1, 2] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def: ValDef::InstResult {
                            inst: inst(def),
                            i: 0,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let def = |v| InstData::Op {
            operands: vec![Operand::new(Position::Late, DefUse::Def, any, Some(val(v)))],
            clobbers: vec![],
            side_effects: true,
        };
        let read = |v, constraint| InstData::Op {
            operands: vec![Operand::new(
                Position::Early,
                DefUse::Use,
                constraint,
                Some(val(v)),
            )],
            clobbers: vec![],
            side_effects: true,
        };

        func.insts = PrimaryMap::new();
        for inst_data in [
            def(0),
            def(1),
            def(2),
            read(2, reg),
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: vec![BlockCall {
                    target: block(1),
                    args: vec![],
                }],
            },
            read(0, any),
            read(1, any),
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: vec![],
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        func.blocks = PrimaryMap::new();
        for insts in [
            vec![inst(0), inst(1), inst(2), inst(3), inst(4)],
            vec![inst(5), inst(6), inst(7)],
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input.set_block_frequency(block(1), BlockFrequency::HOT);
        input
    }

    /// A chain of four blocks defining one value in the first and reading it in
    /// two of the others, so that it is live across all of them and every block
    /// after the definition holds it differently: read at its first point and
    /// live out of it, never mentioned at all, and read only below its entry.
    ///
    /// ```ignore
    /// block0: inst0  late def v0
    ///         inst1  --> block1
    /// block1: inst2  early use v0      // read at the block's first point
    ///         inst3  --> block2
    /// block2: inst4                    // never mentioned
    ///         inst5  --> block3
    /// block3: inst6                    // live-in, read only below
    ///         inst7  early use v0
    ///         inst8  --> returns
    /// ```
    ///
    /// Nothing passes the value as a block-call argument, so every block after
    /// the first is free to hold it wherever it likes.
    pub fn with_a_value_read_in_two_distant_blocks() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = Val::try_new(0).unwrap();

        func.values = PrimaryMap::new();
        func.values
            .push(
                &mut output,
                ValData {
                    reg_class: TestMachine::BOTH_REGS_CLASS,
                    def: ValDef::InstResult {
                        inst: Inst::try_new(0).unwrap(),
                        i: 0,
                    },
                    remat: 0,
                },
            )
            .unwrap();

        let block = |i| Block::try_new(i).unwrap();
        let branch = |target| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: vec![BlockCall {
                target: block(target),
                args: vec![],
            }],
        };
        let read = || InstData::Op {
            operands: vec![Operand::new(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Any,
                Some(val),
            )],
            clobbers: vec![],
            side_effects: true,
        };
        let nothing = || InstData::Op {
            operands: vec![],
            clobbers: vec![],
            side_effects: true,
        };

        func.insts = PrimaryMap::new();
        for inst_data in [
            // `block0` defines the value.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    Some(val),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            branch(1),
            // `block1` reads it at its very first point.
            read(),
            branch(2),
            // `block2` never mentions it.
            nothing(),
            branch(3),
            // `block3` reads it, but not until its second instruction.
            nothing(),
            read(),
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: vec![],
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        for insts in [
            vec![inst(0), inst(1)],
            vec![inst(2), inst(3)],
            vec![inst(4), inst(5)],
            vec![inst(6), inst(7), inst(8)],
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A value defined in one block, read in a much later one both in a
    /// register and on the stack, with a block in between that never mentions
    /// it and needs every register for itself.
    ///
    /// ```ignore
    /// block0: inst0  early def v0 (reg)
    ///         inst1  --> block1, block2
    /// block1: inst2  early def v1 (reg)      // v0 is live through here, but
    ///         inst3  early def v2 (reg)      // never mentioned, and v1 and v2
    ///         inst4  early use v1, use v2    // want both registers
    ///         inst5  --> block3
    /// block2: inst6  returns
    /// block3: inst7  early use v0 (reg)
    ///         inst8  early use v0 (stack)    // forces a spill slot for v0
    ///         inst9  returns
    /// ```
    ///
    /// The stack read gives the value a slot and so a store to place, and the
    /// crowded block in between means anything the value is presumed to be
    /// holding across it is really holding something else. Give the value a
    /// remat cost and the two together are what a spill site outside the
    /// defining block would get wrong.
    pub fn with_a_value_read_on_the_stack_past_a_crowded_block() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = |i| Val::try_new(i).unwrap();
        let block = |i| Block::try_new(i).unwrap();
        let inst = |i| Inst::try_new(i).unwrap();
        let reg = OperandConstraint::Reg(
            RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap(),
        );

        func.values = PrimaryMap::new();
        for def_inst in [0, 2, 3] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def: ValDef::InstResult {
                            inst: inst(def_inst),
                            i: 0,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let operand =
            |kind, constraint, v| Operand::new(Position::Early, kind, constraint, Some(v));
        let def = |v| InstData::Op {
            operands: vec![operand(DefUse::Def, reg, v)],
            clobbers: vec![],
            side_effects: true,
        };
        let read = |constraint, v| InstData::Op {
            operands: vec![operand(DefUse::Use, constraint, v)],
            clobbers: vec![],
            side_effects: true,
        };
        let branch = |targets: &[usize]| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: targets
                .iter()
                .map(|&t| BlockCall {
                    target: block(t),
                    args: vec![],
                })
                .collect(),
        };

        func.insts = PrimaryMap::new();
        for inst_data in [
            // `block0` defines the value.
            def(val(0)),
            branch(&[1, 2]),
            // `block1` never mentions it, and wants both registers itself.
            def(val(1)),
            def(val(2)),
            InstData::Op {
                operands: vec![
                    operand(DefUse::Use, reg, val(1)),
                    operand(DefUse::Use, reg, val(2)),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            branch(&[3]),
            // `block2` is the other way out of `block0`.
            branch(&[]),
            // `block3` reads the value twice, the second time on the stack.
            read(reg, val(0)),
            read(OperandConstraint::Stack, val(0)),
            branch(&[]),
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        func.blocks = PrimaryMap::new();
        for insts in [
            vec![inst(0), inst(1)],
            vec![inst(2), inst(3), inst(4), inst(5)],
            vec![inst(6)],
            vec![inst(7), inst(8), inst(9)],
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A value whose piece across the rest of its defining block holds it
    /// nowhere, wanted in a register in the block right after -- where it
    /// arrives from that piece -- and then read on the stack, which gives it a
    /// slot and so a store to place.
    ///
    /// ```ignore
    /// block0: inst0  late def v0 (any)     // v0 and v1 share a class of one
    ///         inst1  late def v1 (rc0)     // register, so v0 is nowhere from
    ///                --> block1, block2    // inst1 to the end of the block
    /// block1: inst2  early use v0 (rc0)    // v0 arrives from nowhere here
    ///         inst3  late use v0 (stack)   // and this asks it a slot of
    ///                --> block2            // its own, and so a store
    /// block2: inst4  returns
    /// ```
    ///
    /// `block1` has the one predecessor, so its edge's moves and anything
    /// stored at its start share a position, and the recomputation that puts
    /// the value in a register runs after all of them. Give the value a remat
    /// cost and a store placed at `block1`'s start reads a register that does
    /// not hold the value yet.
    ///
    /// `block0` branches two ways so that the walk up the dominator tree stops
    /// at `block1`: from a defining block with this block as its only
    /// successor it would push the store up there anyway, and hide the bug.
    pub fn with_a_value_stored_where_it_arrives_from_nowhere() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = |i| Val::try_new(i).unwrap();
        let block = |i| Block::try_new(i).unwrap();
        let inst = |i| Inst::try_new(i).unwrap();
        let one_reg = RegClass::try_new(usize::from(TestMachine::FIRST_REG_CLASS)).unwrap();

        // Both values belong to the class of that one register, so the second
        // definition leaves the first value with nowhere to be.
        func.values = PrimaryMap::new();
        for def_inst in [0, 1] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::FIRST_REG_CLASS,
                        def: ValDef::InstResult {
                            inst: inst(def_inst),
                            i: 0,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let operand = |pos, kind, constraint, v| Operand::new(pos, kind, constraint, Some(v));
        let branch = |operands: Vec<Operand>, targets: &[usize]| InstData::Branch {
            operands,
            clobbers: vec![],
            targets: targets
                .iter()
                .map(|&t| BlockCall {
                    target: block(t),
                    args: vec![],
                })
                .collect(),
        };

        func.insts = PrimaryMap::new();
        for inst_data in [
            // `block0` defines the value, and then the register it could be in.
            InstData::Op {
                operands: vec![operand(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    val(0),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            branch(
                vec![operand(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Reg(one_reg),
                    val(1),
                )],
                &[1, 2],
            ),
            // `block1` wants the value in that register, and then on the stack.
            InstData::Op {
                operands: vec![operand(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Reg(one_reg),
                    val(0),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            branch(
                vec![operand(
                    Position::Late,
                    DefUse::Use,
                    OperandConstraint::Stack,
                    val(0),
                )],
                &[2],
            ),
            // `block2` is only somewhere for `block1` to end.
            branch(vec![], &[]),
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        func.blocks = PrimaryMap::new();
        for insts in [
            vec![inst(0), inst(1)],
            vec![inst(2), inst(3)],
            vec![inst(4)],
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A value defined in one block and wanted in a much later one, with a
    /// block in between that never mentions it and needs every register for
    /// itself, so the piece crossing that block has no uses of its own.
    ///
    /// `passed_to_the_successor` says how the later block gets the value: as a
    /// block-call argument from the crowded block, or by reading it itself.
    ///
    /// ```ignore
    /// block0: inst0  early def v0 (reg)
    ///         inst1  --> block1, block2
    /// block1: inst2  early def v1 (reg)      // hot: v0 is live through here,
    ///         inst3  early def v2 (reg)      // but never mentioned, and v1
    ///         inst4  early use v1, use v2    // and v2 want both registers
    ///         inst5  --> block3              // passing v0 along, or not
    /// block2: inst6  returns
    /// block3: inst7  early use v0 (reg)      // or of block3's parameter
    ///         inst8  returns
    /// ```
    ///
    /// Give the value a remat cost and the crossing piece is worth no location
    /// at all -- unless `block1` passes it along, which makes it the source
    /// half of an edge move, and a move needs a real place to read from.
    /// `block1` is hot so that the crossing piece is the one that loses its
    /// register.
    pub fn with_a_value_carried_past_a_crowded_block(passed_to_the_successor: bool) -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = |i| Val::try_new(i).unwrap();
        let block = |i| Block::try_new(i).unwrap();
        let inst = |i| Inst::try_new(i).unwrap();
        let reg = OperandConstraint::Reg(
            RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap(),
        );

        // `v0`, carried past the crowded block; the two values that crowd it;
        // and `block3`'s parameter when `v0` is passed along.
        func.values = PrimaryMap::new();
        for def in [
            ValDef::InstResult {
                inst: inst(0),
                i: 0,
            },
            ValDef::InstResult {
                inst: inst(2),
                i: 0,
            },
            ValDef::InstResult {
                inst: inst(3),
                i: 0,
            },
        ]
        .into_iter()
        .chain(passed_to_the_successor.then_some(ValDef::BlockParam {
            block: block(3),
            i: 0,
        })) {
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

        let operand =
            |kind, constraint, v| Operand::new(Position::Early, kind, constraint, Some(v));
        let def = |v| InstData::Op {
            operands: vec![operand(DefUse::Def, reg, v)],
            clobbers: vec![],
            side_effects: true,
        };
        let read = |v| InstData::Op {
            operands: vec![operand(DefUse::Use, reg, v)],
            clobbers: vec![],
            side_effects: true,
        };
        let branch = |targets: &[usize], args: Vec<Val<u32>>| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: targets
                .iter()
                .map(|&t| BlockCall {
                    target: block(t),
                    args: args.clone(),
                })
                .collect(),
        };

        // The value `block3` reads: its own parameter, or `v0` itself.
        let read_val = if passed_to_the_successor {
            val(3)
        } else {
            val(0)
        };
        let args = if passed_to_the_successor {
            vec![val(0)]
        } else {
            vec![]
        };

        func.insts = PrimaryMap::new();
        for inst_data in [
            // `block0` defines the value.
            def(val(0)),
            branch(&[1, 2], vec![]),
            // `block1` never mentions it, and wants both registers itself.
            def(val(1)),
            def(val(2)),
            InstData::Op {
                operands: vec![
                    operand(DefUse::Use, reg, val(1)),
                    operand(DefUse::Use, reg, val(2)),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            branch(&[3], args),
            // `block2` is the other way out of `block0`.
            branch(&[], vec![]),
            // `block3` is where the value is finally wanted.
            read(read_val),
            branch(&[], vec![]),
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        func.blocks = PrimaryMap::new();
        for (params, insts) in [
            (vec![], vec![inst(0), inst(1)]),
            (vec![], vec![inst(2), inst(3), inst(4), inst(5)]),
            (vec![], vec![inst(6)]),
            (
                if passed_to_the_successor {
                    vec![val(3)]
                } else {
                    vec![]
                },
                vec![inst(7), inst(8)],
            ),
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params,
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input.set_block_frequency(block(1), BlockFrequency::HOT);
        input
    }

    /// A single block holding two values whose *slot* lifetimes do not overlap,
    /// although the values are live at the same time.
    ///
    /// `v0` goes to the stack, is read back, then lives in a register with
    /// nothing able to read its slot again; `v1` takes the stack during that
    /// tail, so one slot serves both. Both are read at the end, so their live
    /// ranges genuinely overlap and only a slot-aware range sees the saving.
    pub fn with_two_staggered_spilled_values() -> Self {
        // Four registers, so the reloaded tail can stay in one. With two, the
        // tail returns to the stack and the slot never comes free.
        let reg_class = RegClass::try_new(usize::from(TestMachine::ALL_FOUR_REGS_CLASS)).unwrap();
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = |i| Val::try_new(i).unwrap();
        let inst = |i| Inst::try_new(i).unwrap();
        let reg = OperandConstraint::Reg(reg_class);
        let stack = OperandConstraint::Stack;

        func.values = PrimaryMap::new();
        for i in [0, 3] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::ALL_FOUR_REGS_CLASS,
                        def: ValDef::InstResult {
                            inst: inst(i),
                            i: 0,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let operand =
            |kind, constraint, v| Operand::new(Position::Early, kind, constraint, Some(v));
        let op = |operands: Vec<Operand>| InstData::Op {
            operands,
            clobbers: vec![],
            side_effects: true,
        };

        func.insts = PrimaryMap::new();
        for inst_data in [
            op(vec![operand(DefUse::Def, stack, val(0))]),
            op(vec![operand(DefUse::Use, stack, val(0))]),
            // `v0`'s last slot read, so the slot is free from here on.
            op(vec![operand(DefUse::Use, reg, val(0))]),
            // `v1` takes the slot `v0` has finished with.
            op(vec![operand(DefUse::Def, stack, val(1))]),
            op(vec![operand(DefUse::Use, stack, val(1))]),
            // Both are still live here, so their live ranges overlap even
            // though their slot lifetimes do not.
            op(vec![operand(DefUse::Use, reg, val(0))]),
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: vec![],
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
                    insts: (0..7).map(inst).collect(),
                    frequency: 0,
                },
            )
            .unwrap();

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::four_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// An input with a critical edge that really needs an edit: `block0`
    /// branches to `block1` or `block2` and `block1` falls through to `block2`,
    /// so `block0`'s edge joins two successors to two predecessors. Its two
    /// predecessors pass their values from disjoint kinds of location, the
    /// stack and a register, and the parameter is read in a register, so only
    /// `block0`'s edge needs a move and only an edge block can hold it.
    ///
    /// The two have to disagree about something the allocator still hears: a
    /// fixed operand holds its register outright instead of constraining the
    /// value, so pinning the predecessors to different registers would no
    /// longer keep them apart.
    pub fn with_a_critical_edge() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let first = Val::try_new(0).unwrap();
        let param = Val::try_new(1).unwrap();
        let second = Val::try_new(2).unwrap();
        let merge = Block::try_new(2).unwrap();
        let both = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();

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
            operands: vec![Operand::new(pos, kind, constraint, Some(val))],
            clobbers: vec![],
            side_effects: true,
        };
        let call = |target, args: &[Val]| BlockCall {
            target,
            args: args.to_vec(),
        };

        func.insts = PrimaryMap::new();
        for inst in [
            // `block0`: define a value on the stack and branch two ways,
            // passing it along the edge straight to the merge.
            op(Position::Late, DefUse::Def, OperandConstraint::Any, first),
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Stack,
                first,
            ),
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: vec![call(Block::try_new(1).unwrap(), &[]), call(merge, &[first])],
            },
            // `block1`: pass a value of its own in a register instead, giving
            // the merge its second predecessor.
            op(Position::Late, DefUse::Def, OperandConstraint::Any, second),
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(both),
                second,
            ),
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: vec![call(merge, &[second])],
            },
            // `block2`: read the parameter from a register, where `block1`'s
            // value already is.
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(both),
                param,
            ),
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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

    /// A value read in two sibling loops, with a block of their parent's
    /// between them, and after both. The second loop pins a definition to
    /// `r0` while the value is live, so the value can only have `r1` there.
    /// The first loop holds nothing else and so could take either register,
    /// but only `r1` avoids a move on the way into or out of one of the loops.
    ///
    /// Region allocation visits the second loop first. The loops share no
    /// edge, so what the second one chose reaches the first only through the
    /// block between them.
    pub fn with_a_value_read_in_two_sibling_loops() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = |i: usize| Val::try_new(i).unwrap();
        let inst = |i: usize| Inst::try_new(i).unwrap();
        let block = |i: usize| Block::try_new(i).unwrap();
        let first_reg = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();

        // `v0` is the carried value; `v1` is the pinned definition.
        func.values = PrimaryMap::new();
        for def in [
            ValDef::InstResult {
                inst: inst(0),
                i: 0,
            },
            ValDef::InstResult {
                inst: inst(6),
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

        let read = || {
            Operand::new(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Any,
                Some(val(0)),
            )
        };
        let jump = |targets: &[usize]| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: targets
                .iter()
                .map(|&target| BlockCall {
                    target: block(target),
                    args: vec![],
                })
                .collect(),
        };

        func.insts = PrimaryMap::new();
        for inst_data in [
            // `block0`: define the carried value.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    Some(val(0)),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            jump(&[1]),
            // `block1` and `block2`: the first loop.
            InstData::Op {
                operands: vec![read()],
                clobbers: vec![],
                side_effects: true,
            },
            jump(&[2]),
            jump(&[1, 3]),
            // `block3`: between the loops, in their parent.
            jump(&[4]),
            // `block4` and `block5`: the second loop, with the pinned
            // definition.
            InstData::Op {
                operands: vec![
                    read(),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reg(first_reg),
                        Some(val(1)),
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            jump(&[5]),
            jump(&[4, 6]),
            // `block6`: the read after both loops.
            InstData::Branch {
                operands: vec![read()],
                clobbers: vec![],
                targets: vec![],
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        func.blocks = PrimaryMap::new();
        for insts in [
            vec![inst(0), inst(1)],
            vec![inst(2), inst(3)],
            vec![inst(4)],
            vec![inst(5)],
            vec![inst(6), inst(7)],
            vec![inst(8)],
            vec![inst(9)],
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A value live through a loop that never reads it, where only the middle
    /// of the loop is short of registers: `v0` is defined in `block0` and read
    /// in `block4`, the loop is `block1` to `block3`, and `block2` alone keeps
    /// both registers of the machine busy with `v1` and `v2`.
    pub fn with_a_value_live_through_a_busy_loop() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = |i: usize| Val::try_new(i).unwrap();
        let inst = |i: usize| Inst::try_new(i).unwrap();
        let block = |i: usize| Block::try_new(i).unwrap();
        let reg =
            OperandConstraint::Reg(RegClass::try_new(TestMachine::BOTH_REGS_CLASS.into()).unwrap());

        func.values = PrimaryMap::new();
        for (inst_index, i) in [(0, 0), (3, 0), (3, 1)] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def: ValDef::InstResult {
                            inst: inst(inst_index),
                            i,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let jump = |targets: &[usize]| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: targets
                .iter()
                .map(|&target| BlockCall {
                    target: block(target),
                    args: vec![],
                })
                .collect(),
        };

        func.insts = PrimaryMap::new();
        for inst_data in [
            // `block0`: define the value carried through the loop.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Any,
                    Some(val(0)),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            jump(&[1]),
            // `block1`: the loop header, with a register to spare.
            jump(&[2]),
            // `block2`: fill both registers, and read them.
            InstData::Op {
                operands: vec![
                    Operand::new(Position::Late, DefUse::Def, reg, Some(val(1))),
                    Operand::new(Position::Late, DefUse::Def, reg, Some(val(2))),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Branch {
                operands: vec![
                    Operand::new(Position::Early, DefUse::Use, reg, Some(val(1))),
                    Operand::new(Position::Early, DefUse::Use, reg, Some(val(2))),
                ],
                clobbers: vec![],
                targets: vec![BlockCall {
                    target: block(3),
                    args: vec![],
                }],
            },
            // `block3`: the latch, with a register to spare too.
            jump(&[1, 4]),
            // `block4`: the one read of `v0`, past the loop.
            InstData::Branch {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Any,
                    Some(val(0)),
                )],
                clobbers: vec![],
                targets: vec![],
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        func.blocks = PrimaryMap::new();
        for insts in [
            vec![inst(0), inst(1)],
            vec![inst(2)],
            vec![inst(3), inst(4)],
            vec![inst(5)],
            vec![inst(6)],
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A value that dies in a register a later block clobbers, so that the
    /// move carrying it into that register at the top of the block between is
    /// overwritten before anything reads it.
    ///
    /// `v1` lives in `r1` across `block0` and is spilled there, because it is
    /// read at the end of `block2` from `r0`. `block1` moves it into `r0`, but
    /// `block2` clobbers `r0` and then reloads `v1` into it, so the move is
    /// dead, and only a pass that looks past `block1` can tell.
    pub fn with_a_register_move_overwritten_in_a_later_block() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = |i: usize| Val::try_new(i).unwrap();
        let inst = |i: usize| Inst::try_new(i).unwrap();
        let block = |i: usize| Block::try_new(i).unwrap();
        let reg = |i: usize| Reg::try_new(i).unwrap();
        let first_reg = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();

        func.values = PrimaryMap::new();
        for (reg_class, def, remat) in [
            (
                TestMachine::BOTH_REGS_CLASS,
                ValDef::BlockParam {
                    block: block(0),
                    i: 0,
                },
                NO_REMAT,
            ),
            (
                TestMachine::BOTH_REGS_CLASS,
                ValDef::InstResult {
                    inst: inst(1),
                    i: 0,
                },
                NO_REMAT,
            ),
            (
                TestMachine::FIRST_REG_CLASS,
                ValDef::InstResult {
                    inst: inst(2),
                    i: 0,
                },
                NO_REMAT,
            ),
            // Always rematerialized, so it holds no register across `block1`.
            (
                TestMachine::BOTH_REGS_CLASS,
                ValDef::InstResult {
                    inst: inst(4),
                    i: 0,
                },
                1,
            ),
            (
                TestMachine::BOTH_REGS_CLASS,
                ValDef::InstResult {
                    inst: inst(7),
                    i: 0,
                },
                NO_REMAT,
            ),
        ] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class,
                        def,
                        remat,
                    },
                )
                .unwrap();
        }

        let any = |pos, kind, v| Operand::new(pos, kind, OperandConstraint::Any, Some(val(v)));
        let op = |operands, clobbers, side_effects| InstData::Op {
            operands,
            clobbers,
            side_effects,
        };
        let jump = |target| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: vec![BlockCall {
                target: block(target),
                args: vec![],
            }],
        };

        func.insts = PrimaryMap::new();
        for inst_data in [
            // `block0`
            op(
                vec![any(Position::Early, DefUse::Use, 0)],
                vec![reg(1)],
                true,
            ),
            op(vec![any(Position::Late, DefUse::Def, 1)], vec![], true),
            op(
                vec![
                    any(Position::Early, DefUse::Def, 2),
                    any(Position::Late, DefUse::Use, 1),
                ],
                vec![],
                true,
            ),
            jump(1),
            // `block1`
            op(vec![any(Position::Late, DefUse::Def, 3)], vec![], true),
            op(vec![], vec![], false),
            jump(2),
            // `block2`: clobber `r0`, then read `v1` from it.
            op(
                vec![any(Position::Late, DefUse::Def, 4)],
                vec![reg(0)],
                false,
            ),
            InstData::Branch {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Reg(first_reg),
                    Some(val(1)),
                )],
                clobbers: vec![],
                targets: vec![],
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        func.blocks = PrimaryMap::new();
        for (params, insts) in [
            (vec![val(0)], vec![inst(0), inst(1), inst(2), inst(3)]),
            (vec![], vec![inst(4), inst(5), inst(6)]),
            (vec![], vec![inst(7), inst(8)]),
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params,
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut machine = TestMachine::two_registers();
        // Two units for `r0`, which is what tips the allocator into putting
        // `v1` in `r1` first.
        machine.banks[0].regs = vec![2, 1];
        machine.fixup();

        let mut input = TestInput {
            options: InputOptions::default(),
            machine,
            func,
        };
        input.fixup();
        input
    }

    /// A loop carrying an entry parameter read only after the loop, on a path
    /// where it has been spilled.
    pub fn with_a_looping_value_read_only_after_the_loop() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = |i: usize| Val::try_new(i).unwrap();
        let inst = |i: usize| Inst::try_new(i).unwrap();
        let block = |i: usize| Block::try_new(i).unwrap();

        // `v0` is the entry parameter; the rest keep the registers busy.
        func.values = PrimaryMap::new();
        for def in [
            ValDef::BlockParam {
                block: block(0),
                i: 0,
            },
            ValDef::InstResult {
                inst: inst(0),
                i: 0,
            },
            ValDef::InstResult {
                inst: inst(0),
                i: 1,
            },
            ValDef::InstResult {
                inst: inst(1),
                i: 0,
            },
            ValDef::InstResult {
                inst: inst(2),
                i: 0,
            },
            ValDef::InstResult {
                inst: inst(2),
                i: 1,
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

        let def = |pos, val| Operand::new(pos, DefUse::Def, OperandConstraint::Any, Some(val));
        let call = |target, args: &[Val]| BlockCall {
            target: block(target),
            args: args.to_vec(),
        };

        func.insts = PrimaryMap::new();
        for inst_data in [
            // `block0`: define two values, then fork into and past the loop.
            InstData::Branch {
                operands: vec![def(Position::Late, val(1)), def(Position::Late, val(2))],
                clobbers: vec![],
                targets: vec![call(1, &[]), call(2, &[]), call(3, &[])],
            },
            // `block1`: another definition, then the loop's second block.
            InstData::Branch {
                operands: vec![def(Position::Late, val(3))],
                clobbers: vec![],
                targets: vec![call(2, &[])],
            },
            // `block2`: two more definitions, at both halves of the
            // instruction, and the back edge.
            InstData::Op {
                operands: vec![def(Position::Late, val(4)), def(Position::Early, val(5))],
                clobbers: vec![],
                side_effects: false,
            },
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: vec![call(0, &[val(2)])],
            },
            // `block3`: the one read of `v0`, past the loop.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
                side_effects: false,
            },
            InstData::Branch {
                operands: vec![Operand::new(
                    Position::Late,
                    DefUse::Use,
                    OperandConstraint::Any,
                    Some(val(0)),
                )],
                clobbers: vec![],
                targets: vec![],
            },
        ] {
            func.insts.push(&mut output, inst_data).unwrap();
        }

        func.blocks = PrimaryMap::new();
        for (params, insts, frequency) in [
            (vec![val(0)], vec![inst(0)], 1),
            (vec![], vec![inst(1)], 0),
            (vec![], vec![inst(2), inst(3)], 0),
            (vec![], vec![inst(4), inst(5)], 0),
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params,
                        insts,
                        frequency,
                    },
                )
                .unwrap();
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
            operands: vec![Operand::new(pos, kind, constraint, Some(val))],
            clobbers: vec![],
            side_effects: true,
        };
        let branch = |target, args| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: vec![BlockCall { target, args }],
        };

        func.insts = PrimaryMap::new();
        for inst in [
            // block0: define the value and fork.
            op(Position::Late, DefUse::Def, OperandConstraint::Any, arg_val),
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
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
                clobbers: vec![],
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

    /// A straight-line chain of `links` blocks, each taking one parameter and
    /// passing it straight on to the next.
    pub fn with_a_parameter_chain(links: usize) -> Self {
        assert!(links >= 1);

        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let block = |i: usize| Block::try_new(i).unwrap();
        let inst = |i: usize| Inst::try_new(i).unwrap();
        let val = |i: usize| Val::try_new(i).unwrap();
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();

        // `v0` is defined in the entry block; `v1..=vlinks` are the parameters
        // of `block1..=blocklinks`.
        func.values = PrimaryMap::new();
        func.values
            .push(
                &mut output,
                ValData {
                    reg_class: TestMachine::BOTH_REGS_CLASS,
                    def: ValDef::InstResult {
                        inst: inst(0),
                        i: 0,
                    },
                    remat: 0,
                },
            )
            .unwrap();
        for i in 1..=links {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def: ValDef::BlockParam {
                            block: block(i),
                            i: 0,
                        },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let branch = |target, arg| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: vec![BlockCall {
                target,
                args: vec![arg],
            }],
        };

        // `block0` defines the value and hands it on; each `blocki` passes its
        // parameter along. The last reads its parameter in a register, then
        // ends in an instruction of its own so `ensure_terminators` leaves the
        // read alone.
        func.insts = PrimaryMap::new();
        func.insts
            .push(
                &mut output,
                InstData::Op {
                    operands: vec![Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reg(class),
                        Some(val(0)),
                    )],
                    clobbers: vec![],
                    side_effects: true,
                },
            )
            .unwrap();
        for i in 0..links {
            func.insts
                .push(&mut output, branch(block(i + 1), val(i)))
                .unwrap();
        }
        for inst_data in [
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Reg(class),
                    Some(val(links)),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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
        for i in 1..links {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![val(i)],
                        insts: vec![inst(i + 1)],
                        frequency: 0,
                    },
                )
                .unwrap();
        }
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: vec![val(links)],
                    insts: vec![inst(links + 1), inst(links + 2)],
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

    /// A read pinned to `r1` sharing a point with the reuse target it follows.
    ///
    /// `v0` is read twice at `inst1`'s early half, unconstrained and then
    /// pinned to `r1`. The tie names the first, so the pinned read cannot join
    /// its span and has no say in where the definition goes; the earlier read
    /// pinned to `r0` is what makes the two disagree if it is let speak.
    ///
    /// The mirror of [`TestInput::with_a_reuse_of_a_pinned_read`], where the
    /// tie names the second read; see
    /// `checker::tests::a_reuse_lands_where_its_target_is_read_when_the_tie_comes_first`.
    pub fn with_a_pinned_read_after_a_reuse_target() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let inst = |i: usize| Inst::try_new(i).unwrap();
        let val = |i: usize| Val::try_new(i).unwrap();
        let first = RegClass::try_new(usize::from(TestMachine::FIRST_REG_CLASS)).unwrap();
        let second = RegClass::try_new(usize::from(TestMachine::SECOND_REG_CLASS)).unwrap();

        func.values = PrimaryMap::new();
        func.values
            .push(
                &mut output,
                ValData {
                    reg_class: TestMachine::BOTH_REGS_CLASS,
                    def: ValDef::BlockParam {
                        block: Block::try_new(0).unwrap(),
                        i: 0,
                    },
                    remat: 0,
                },
            )
            .unwrap();
        func.values
            .push(
                &mut output,
                ValData {
                    reg_class: TestMachine::BOTH_REGS_CLASS,
                    def: ValDef::InstResult {
                        inst: inst(1),
                        i: 0,
                    },
                    remat: 0,
                },
            )
            .unwrap();

        func.insts = PrimaryMap::new();
        for inst_data in [
            // The read that makes `rc0` look like the place to be.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Late,
                    DefUse::Use,
                    OperandConstraint::Reg(first),
                    Some(val(0)),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            // The tie, and the sibling read that contradicts it.
            InstData::Op {
                operands: vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        Some(val(0)),
                    ),
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(second),
                        Some(val(0)),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(0),
                        Some(val(1)),
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            // A terminator of its own, so `ensure_terminators` leaves the tied
            // instruction alone.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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
                    params: vec![val(0)],
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

    /// An input with a move placed just before a block's terminator.
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
    /// which is the one shape that lets move generation host that move on the
    /// predecessor's terminator rather than splitting the edge. The move goes
    /// immediately before that terminator, never after it.
    pub fn with_a_move_before_an_unconditional_branch() -> Self {
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
            operands: vec![Operand::new(pos, kind, constraint, Some(val))],
            clobbers: vec![],
            side_effects: true,
        };
        let branch = |target, args| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
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
                clobbers: vec![],
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
                clobbers: vec![],
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

    /// A loop around a switch with `arms` two-block arms, and `vals` values
    /// live through all of it. Hot arms make each arm's merge join two
    /// multi-span sets, one surrounding the other.
    pub fn with_a_loop_around_a_wide_switch(arms: usize, vals: usize) -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let block = |i| Block::try_new(i).unwrap();
        let header = block(1);
        let latch = block(2 + 2 * arms);
        let exit = block(3 + 2 * arms);
        let jump = |targets: Vec<Block>| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: targets
                .into_iter()
                .map(|target| BlockCall {
                    target,
                    args: Vec::new(),
                })
                .collect(),
        };

        func.values = PrimaryMap::new();
        func.insts = PrimaryMap::new();
        let mut blocks: Vec<Vec<Inst>> = vec![];
        let push = |func: &mut TestFunction, output: &mut OutputInner<u32>, inst_data| {
            func.insts.push(output, inst_data).unwrap()
        };

        let mut entry = vec![];
        for v in 0..vals {
            let inst = Inst::try_new(v).unwrap();
            let val = Val::try_new(v).unwrap();
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def: ValDef::InstResult { inst, i: 0 },
                        remat: 0,
                    },
                )
                .unwrap();
            entry.push(push(
                &mut func,
                &mut output,
                InstData::Op {
                    operands: vec![Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Any,
                        Some(val),
                    )],
                    clobbers: vec![],
                    side_effects: true,
                },
            ));
        }
        entry.push(push(&mut func, &mut output, jump(vec![header])));
        blocks.push(entry);

        blocks.push(vec![push(
            &mut func,
            &mut output,
            jump((0..arms).map(|i| block(2 + 2 * i)).collect()),
        )]);
        for i in 0..arms {
            let bottom = block(3 + 2 * i);
            blocks.push(vec![push(&mut func, &mut output, jump(vec![bottom]))]);
            blocks.push(vec![push(&mut func, &mut output, jump(vec![latch]))]);
        }
        blocks.push(vec![push(&mut func, &mut output, jump(vec![header, exit]))]);
        blocks.push(vec![
            push(
                &mut func,
                &mut output,
                InstData::Op {
                    operands: (0..vals)
                        .map(|v| {
                            Operand::new(
                                Position::Early,
                                DefUse::Use,
                                OperandConstraint::Any,
                                Some(Val::try_new(v).unwrap()),
                            )
                        })
                        .collect(),
                    clobbers: vec![],
                    side_effects: true,
                },
            ),
            push(
                &mut func,
                &mut output,
                InstData::Op {
                    operands: vec![],
                    clobbers: vec![],
                    side_effects: true,
                },
            ),
        ]);

        func.blocks = PrimaryMap::new();
        for insts in blocks {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        for i in 2..=2 + 2 * arms {
            input.set_block_frequency(block(i), BlockFrequency::HOT);
        }
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
                        Some(param),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Any,
                        Some(next),
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
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
                    Some(param),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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
                        Some(param),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(0),
                        Some(clobber),
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            // And read it there again afterwards, so it comes back.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Reg(pinned),
                    Some(param),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
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

    /// A value defined in a loop and read off the stack past it, where the
    /// block the walk leaves the loop into is itself a legal store site.
    ///
    /// `block0` branches into the loop `block1 -> block1`, which defines the
    /// value, and on to `block2`, which reads it in a register and then off
    /// the stack. `block2` is the loop exit and the value is live in a
    /// register at its top, so the walk out of the loop stops there for an
    /// edge store, and a store placed inside `block2` instead would sit
    /// outside the defining loop; see
    /// `first_legal_placement_up_dom_tree`.
    pub fn with_a_value_defined_in_a_loop_and_read_past_its_exit() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = Val::try_new(0).unwrap();
        let block = |i| Block::try_new(i).unwrap();
        let class = RegClass::try_new(TestMachine::BOTH_REGS_CLASS.into()).unwrap();

        func.values = PrimaryMap::new();
        func.values
            .push(
                &mut output,
                ValData {
                    reg_class: TestMachine::BOTH_REGS_CLASS,
                    def: ValDef::InstResult {
                        inst: Inst::try_new(1).unwrap(),
                        i: 0,
                    },
                    remat: 0,
                },
            )
            .unwrap();

        let op = |pos, kind, constraint| InstData::Op {
            operands: vec![Operand::new(pos, kind, constraint, Some(val))],
            clobbers: vec![],
            side_effects: true,
        };
        let branch = |targets: &[usize]| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: targets
                .iter()
                .map(|&t| BlockCall {
                    target: block(t),
                    args: vec![],
                })
                .collect(),
        };

        func.insts = PrimaryMap::new();
        for inst in [
            // block0: enter the loop.
            branch(&[1]),
            // block1, the loop: define the value and either go around again or
            // leave. The back edge is what makes this a region of its own.
            op(Position::Late, DefUse::Def, OperandConstraint::Any),
            branch(&[1, 2]),
            // block2, the exit: read the value in a register, which makes this
            // a legal store site, then read it off the stack, which is what
            // asks for a store at all.
            op(Position::Early, DefUse::Use, OperandConstraint::Reg(class)),
            op(Position::Early, DefUse::Use, OperandConstraint::Stack),
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        for insts in [
            vec![inst(0)],
            vec![inst(1), inst(2)],
            vec![inst(3), inst(4)],
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A recomputable value whose one read is pinned to a register, beside two
    /// defs that take both of the machine's registers at that same point.
    ///
    /// Nothing is left for the read, so the bundle narrows to its early half
    /// and the carrier it leaves behind loses the use that wanted a register.
    /// That carrier is recomputable, and placing it decides between the stack
    /// and recomputing it; see `split_into_minimal_or_spill`.
    pub fn with_a_recomputable_value_read_under_full_pressure() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = |i| Val::try_new(i).unwrap();
        let both = RegClass::try_new(TestMachine::BOTH_REGS_CLASS.into()).unwrap();
        let first = RegClass::try_new(TestMachine::FIRST_REG_CLASS.into()).unwrap();
        let second = RegClass::try_new(TestMachine::SECOND_REG_CLASS.into()).unwrap();

        // `v0` is the recomputable one, defined first and read twice; `v1` and
        // `v2` are each pinned to one of the two registers.
        func.values = PrimaryMap::new();
        for (inst, i, remat) in [(0usize, 0usize, 2u8), (1, 1, 0), (1, 2, 0)] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: TestMachine::BOTH_REGS_CLASS,
                        def: ValDef::InstResult {
                            inst: Inst::try_new(inst).unwrap(),
                            i,
                        },
                        remat,
                    },
                )
                .unwrap();
        }

        let op = |operands: Vec<Operand>| InstData::Op {
            operands,
            clobbers: vec![],
            side_effects: true,
        };

        func.insts = PrimaryMap::new();
        for inst in [
            op(vec![Operand::new(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Any,
                Some(val(0)),
            )]),
            // The early read of `v0` wants a register at the same point as the
            // two defs that take every register the machine has.
            op(vec![
                Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Reg(both),
                    Some(val(0)),
                ),
                Operand::new(
                    Position::Late,
                    DefUse::Def,
                    OperandConstraint::Reg(first),
                    Some(val(1)),
                ),
                Operand::new(
                    Position::Early,
                    DefUse::Def,
                    OperandConstraint::Reg(second),
                    Some(val(2)),
                ),
            ]),
            // A later read, so `v0` stays live past the crowded point and has
            // a carrier span to place.
            op(vec![Operand::new(
                Position::Late,
                DefUse::Use,
                OperandConstraint::Any,
                Some(val(0)),
            )]),
            op(vec![]),
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        func.blocks
            .push(
                &mut output,
                BlockData {
                    params: vec![],
                    insts: vec![inst(0), inst(1), inst(2), inst(3)],
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

    /// A value defined outside a loop that spends part of its live range on
    /// the stack inside it: `block0` defines the value and conditionally
    /// enters the loop `block1 <-> block2`, which reads the value in a
    /// register and then off the stack.
    pub fn with_a_value_spilled_inside_a_loop() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = Val::try_new(0).unwrap();
        let block = |i| Block::try_new(i).unwrap();
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();

        func.values = PrimaryMap::new();
        func.values
            .push(
                &mut output,
                ValData {
                    reg_class: TestMachine::BOTH_REGS_CLASS,
                    def: ValDef::InstResult {
                        inst: Inst::try_new(0).unwrap(),
                        i: 0,
                    },
                    remat: 0,
                },
            )
            .unwrap();

        let op = |pos, kind, constraint| InstData::Op {
            operands: vec![Operand::new(pos, kind, constraint, Some(val))],
            clobbers: vec![],
            side_effects: true,
        };
        let branch = |targets: &[usize]| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: targets
                .iter()
                .map(|&t| BlockCall {
                    target: block(t),
                    args: vec![],
                })
                .collect(),
        };

        func.insts = PrimaryMap::new();
        for inst in [
            // block0: define the value, then conditionally enter the loop. The
            // second successor is what stops the single-successor hoist.
            op(Position::Late, DefUse::Def, OperandConstraint::Any),
            branch(&[1, 3]),
            // block1, the loop header: read the value in a register, so it is
            // live in a register at the header's entry and the header is a
            // legal spill placement.
            op(Position::Early, DefUse::Use, OperandConstraint::Reg(class)),
            branch(&[2, 3]),
            // block2, the loop body: read the value off the stack, which is
            // what puts it on the stack in the first place, then take the back
            // edge.
            op(Position::Early, DefUse::Use, OperandConstraint::Stack),
            branch(&[1]),
            // block3: the loop exit. `ensure_terminators` turns this into the
            // block's return.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        for insts in [
            vec![inst(0), inst(1)],
            vec![inst(2), inst(3)],
            vec![inst(4), inst(5)],
            vec![inst(6)],
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A value read on the stack only on a cold arm: `block0` defines it,
    /// `block1` reads it in a register and branches to the cold `block2`,
    /// which reads it off the stack, or to `block3`, which does not touch it.
    ///
    /// `block1` is the first legal spill block above the cold read, so a
    /// store placed there would run on the hot path too.
    pub fn with_a_value_read_on_the_stack_on_a_cold_arm() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = Val::try_new(0).unwrap();
        let block = |i| Block::try_new(i).unwrap();
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();

        func.values = PrimaryMap::new();
        func.values
            .push(
                &mut output,
                ValData {
                    reg_class: TestMachine::BOTH_REGS_CLASS,
                    def: ValDef::InstResult {
                        inst: Inst::try_new(0).unwrap(),
                        i: 0,
                    },
                    remat: 0,
                },
            )
            .unwrap();

        let op = |pos, kind, constraint| InstData::Op {
            operands: vec![Operand::new(pos, kind, constraint, Some(val))],
            clobbers: vec![],
            side_effects: true,
        };
        let branch = |targets: &[usize]| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: targets
                .iter()
                .map(|&t| BlockCall {
                    target: block(t),
                    args: vec![],
                })
                .collect(),
        };
        let ret = || InstData::Op {
            operands: vec![],
            clobbers: vec![],
            side_effects: true,
        };

        func.insts = PrimaryMap::new();
        for inst in [
            // block0: define the value. Two successors, so the single-successor
            // hoist cannot carry a store from `block1` up here.
            op(Position::Late, DefUse::Def, OperandConstraint::Any),
            branch(&[1, 3]),
            // block1: read the value in a register, which makes this block a
            // legal spill placement, then fork.
            op(Position::Early, DefUse::Use, OperandConstraint::Reg(class)),
            branch(&[2, 3]),
            // block2, cold: read the value off the stack.
            op(Position::Early, DefUse::Use, OperandConstraint::Stack),
            ret(),
            // block3.
            ret(),
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        for (insts, frequency) in [
            (vec![inst(0), inst(1)], 0),
            (vec![inst(2), inst(3)], 0),
            (vec![inst(4), inst(5)], 1),
            (vec![inst(6)], 0),
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts,
                        frequency,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A loop that defines a value and reads it in a register every iteration,
    /// and an exit that reads it off the stack.
    ///
    /// `block1` heads the loop, defines the value and reads it in a register,
    /// then branches to the exit `block2` or the latch `block3`. Every block is
    /// equally frequent, so only the loop says the exit runs less often than
    /// `block1`.
    pub fn with_a_value_read_on_the_stack_after_a_loop_exit() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = Val::try_new(0).unwrap();
        let block = |i| Block::try_new(i).unwrap();
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();

        func.values = PrimaryMap::new();
        func.values
            .push(
                &mut output,
                ValData {
                    reg_class: TestMachine::BOTH_REGS_CLASS,
                    def: ValDef::InstResult {
                        inst: Inst::try_new(1).unwrap(),
                        i: 0,
                    },
                    remat: 0,
                },
            )
            .unwrap();

        let op = |pos, kind, constraint| InstData::Op {
            operands: vec![Operand::new(pos, kind, constraint, Some(val))],
            clobbers: vec![],
            side_effects: true,
        };
        let branch = |targets: &[usize]| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: targets
                .iter()
                .map(|&t| BlockCall {
                    target: block(t),
                    args: vec![],
                })
                .collect(),
        };
        let ret = || InstData::Op {
            operands: vec![],
            clobbers: vec![],
            side_effects: true,
        };

        func.insts = PrimaryMap::new();
        for inst in [
            // block0
            branch(&[1]),
            // block1, the loop header: define the value and read it in a
            // register, then exit or go on.
            op(Position::Late, DefUse::Def, OperandConstraint::Any),
            op(Position::Early, DefUse::Use, OperandConstraint::Reg(class)),
            branch(&[2, 3]),
            // block2, the exit: read the value off the stack.
            op(Position::Early, DefUse::Use, OperandConstraint::Stack),
            ret(),
            // block3, the latch.
            branch(&[1]),
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        for insts in [
            vec![inst(0)],
            vec![inst(1), inst(2), inst(3)],
            vec![inst(4), inst(5)],
            vec![inst(6)],
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A value defined before a loop, read in a register inside it, and read
    /// off the stack after the loop exits.
    ///
    /// `block0` defines the value and reads it in a register; `block1` heads
    /// the loop and reads it in a register too, then branches to the exit
    /// `block2` or the latch `block3`. The exit runs as often as `block0`, so
    /// the store belongs in `block0` rather than on the exit edge: both run
    /// once per call, and `block0` dominates every later read.
    pub fn with_a_value_from_before_a_loop_read_on_the_stack_after_it() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = Val::try_new(0).unwrap();
        let block = |i| Block::try_new(i).unwrap();
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();

        func.values = PrimaryMap::new();
        func.values
            .push(
                &mut output,
                ValData {
                    reg_class: TestMachine::BOTH_REGS_CLASS,
                    def: ValDef::InstResult {
                        inst: Inst::try_new(0).unwrap(),
                        i: 0,
                    },
                    remat: 0,
                },
            )
            .unwrap();

        let op = |pos, kind, constraint| InstData::Op {
            operands: vec![Operand::new(pos, kind, constraint, Some(val))],
            clobbers: vec![],
            side_effects: true,
        };
        let branch = |targets: &[usize]| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: targets
                .iter()
                .map(|&t| BlockCall {
                    target: block(t),
                    args: vec![],
                })
                .collect(),
        };
        let ret = || InstData::Op {
            operands: vec![],
            clobbers: vec![],
            side_effects: true,
        };

        func.insts = PrimaryMap::new();
        for inst in [
            // block0: define the value and read it in a register.
            op(Position::Late, DefUse::Def, OperandConstraint::Any),
            op(Position::Early, DefUse::Use, OperandConstraint::Reg(class)),
            branch(&[1]),
            // block1, the loop header: read the value in a register, which
            // makes this block a legal spill placement, then exit or go on.
            op(Position::Early, DefUse::Use, OperandConstraint::Reg(class)),
            branch(&[2, 3]),
            // block2, the exit: read the value off the stack.
            op(Position::Early, DefUse::Use, OperandConstraint::Stack),
            ret(),
            // block3, the latch.
            branch(&[1]),
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        for insts in [
            vec![inst(0), inst(1), inst(2)],
            vec![inst(3), inst(4)],
            vec![inst(5), inst(6)],
            vec![inst(7)],
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A loop nest: `block0` defines a value outside both loops, `block1`
    /// heads the outer loop and defines a second value, and `block2 <-> block3`
    /// is the inner loop, which reads both values off the stack.
    ///
    /// The two loops are a single strongly-connected component but must be
    /// separate regions, so that the inner loop holds neither value's spill.
    pub fn with_a_nested_loop() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let outside = Val::try_new(0).unwrap();
        let outer = Val::try_new(1).unwrap();
        let block = |i| Block::try_new(i).unwrap();
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();

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

        let op = |pos, kind, constraint, val| InstData::Op {
            operands: vec![Operand::new(pos, kind, constraint, Some(val))],
            clobbers: vec![],
            side_effects: true,
        };
        let branch = |targets: &[usize]| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: targets
                .iter()
                .map(|&t| BlockCall {
                    target: block(t),
                    args: vec![],
                })
                .collect(),
        };

        func.insts = PrimaryMap::new();
        for inst in [
            // block0 defines the value that lives outside both loops. The
            // second successor stops the single-successor hoist.
            op(Position::Late, DefUse::Def, OperandConstraint::Any, outside),
            branch(&[1, 5]),
            // block1, the outer loop header, defines a value that lives in the
            // outer loop.
            op(Position::Late, DefUse::Def, OperandConstraint::Any, outer),
            branch(&[2, 5]),
            // Reading the outer value in a register here keeps the outer loop
            // header from being its only legal spill placement.
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(class),
                outside,
            ),
            branch(&[3, 4]),
            // Reading both values off the stack is what spills them. Those
            // spills must land outside the inner loop: in `block1` for the
            // outer value, `block0` for the outside one.
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Stack,
                outer,
            ),
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Stack,
                outside,
            ),
            branch(&[2]),
            // block4 takes the outer loop's back edge; reading the outer value
            // in a register keeps it live around that edge.
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(class),
                outer,
            ),
            branch(&[1]),
            // block5, the outer loop's exit.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        for insts in [
            vec![inst(0), inst(1)],
            vec![inst(2), inst(3)],
            vec![inst(4), inst(5)],
            vec![inst(6), inst(7), inst(8)],
            vec![inst(9), inst(10)],
            vec![inst(11)],
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// An irreducible loop: `block0` branches into either half of the cycle
    /// `block1 <-> block2`, so the cycle has two entries and neither dominates
    /// the other.
    ///
    /// No natural loop describes such a cycle, but it still has to end up in
    /// one region: allocating half of a cycle independently of the other half
    /// would be wrong.
    pub fn with_an_irreducible_loop() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = Val::try_new(0).unwrap();
        let block = |i| Block::try_new(i).unwrap();
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();

        func.values = PrimaryMap::new();
        func.values
            .push(
                &mut output,
                ValData {
                    reg_class: TestMachine::BOTH_REGS_CLASS,
                    def: ValDef::InstResult {
                        inst: Inst::try_new(0).unwrap(),
                        i: 0,
                    },
                    remat: 0,
                },
            )
            .unwrap();

        let op = |pos, kind, constraint| InstData::Op {
            operands: vec![Operand::new(pos, kind, constraint, Some(val))],
            clobbers: vec![],
            side_effects: true,
        };
        let branch = |targets: &[usize]| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets: targets
                .iter()
                .map(|&t| BlockCall {
                    target: block(t),
                    args: vec![],
                })
                .collect(),
        };

        func.insts = PrimaryMap::new();
        for inst in [
            // Branching into either half of the cycle is what makes it
            // irreducible.
            op(Position::Late, DefUse::Def, OperandConstraint::Any),
            branch(&[1, 2]),
            // block1, one of the two entries.
            op(Position::Early, DefUse::Use, OperandConstraint::Reg(class)),
            branch(&[2, 3]),
            // block2, the other entry, closes the cycle back to `block1`.
            op(Position::Early, DefUse::Use, OperandConstraint::Stack),
            branch(&[1, 3]),
            // block3, the cycle's exit.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
                side_effects: true,
            },
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        for insts in [
            vec![inst(0), inst(1)],
            vec![inst(2), inst(3)],
            vec![inst(4), inst(5)],
            vec![inst(6)],
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params: vec![],
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

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
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        Some(first),
                    ),
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        Some(second),
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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
                            Some(Val::try_new(i).unwrap()),
                        )
                    })
                    .collect(),
                clobbers: vec![],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the reads.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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
                        Some(param),
                    ),
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Stack,
                        Some(param),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Use,
                        OperandConstraint::Reg(narrow),
                        Some(param),
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Stack,
                    Some(param),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            // Give the block a terminator of its own, so that
            // `ensure_terminators` does not rewrite the reads.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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
            operands: vec![Operand::new(pos, kind, constraint, Some(val))],
            clobbers: vec![],
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
                clobbers: vec![],
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
                clobbers: vec![],
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

    /// A join whose spilled parameter has two equally weighted claims on its
    /// slot: the slot one of its arguments is already in, and its class's slot,
    /// which it shares with an argument not colored yet.
    ///
    /// `block2` is entered from `block0` and `block1`, which pass `v0` to all
    /// three of its parameters, and from `block3`, which passes `v6`. `block2`
    /// branches to `block3` with `v4`, defined in `block2`, for both of
    /// `block3`'s parameters.
    pub fn with_a_param_torn_between_a_vote_and_its_class() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let inst = |i| Inst::try_new(i).unwrap();
        let block = |b| Block::try_new(b).unwrap();
        let val = |v| Val::try_new(v).unwrap();

        func.values = PrimaryMap::new();
        for def in [
            ValDef::BlockParam {
                block: block(0),
                i: 0,
            },
            ValDef::BlockParam {
                block: block(2),
                i: 0,
            },
            ValDef::BlockParam {
                block: block(2),
                i: 1,
            },
            ValDef::BlockParam {
                block: block(2),
                i: 2,
            },
            ValDef::InstResult {
                inst: inst(7),
                i: 0,
            },
            ValDef::InstResult {
                inst: inst(7),
                i: 1,
            },
            ValDef::BlockParam {
                block: block(3),
                i: 0,
            },
            ValDef::BlockParam {
                block: block(3),
                i: 1,
            },
            ValDef::InstResult {
                inst: inst(9),
                i: 0,
            },
        ] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: 0,
                        def,
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let r0 = Reg::try_new(0).unwrap();
        let reg = OperandConstraint::Reg(RegClass::try_new(0).unwrap());
        let operand = |pos, kind, constraint, v| Operand::new(pos, kind, constraint, Some(val(v)));
        let call = |b, args: &[usize]| BlockCall {
            target: block(b),
            args: args.iter().map(|&v| val(v)).collect(),
        };
        let op = |operands, clobbers, side_effects| InstData::Op {
            operands,
            clobbers,
            side_effects,
        };
        let branch = |operands, clobbers, targets| InstData::Branch {
            operands,
            clobbers,
            targets,
        };
        use DefUse::{Def, Use};
        use OperandConstraint::{Any, Stack};
        use Position::{Early, Late};

        func.insts = PrimaryMap::new();
        for data in [
            // block0
            op(vec![operand(Late, Use, Any, 0)], vec![r0], false),
            op(vec![], vec![], true),
            op(vec![], vec![], false),
            branch(
                vec![operand(Early, Use, Any, 0)],
                vec![r0],
                vec![call(2, &[0, 0, 0])],
            ),
            // block1
            op(
                vec![
                    operand(Early, Use, reg, 0),
                    operand(Early, Use, Stack, 0),
                    operand(Early, Use, Stack, 0),
                ],
                vec![],
                true,
            ),
            op(vec![operand(Late, Use, Stack, 0)], vec![r0], false),
            branch(vec![], vec![r0], vec![call(2, &[0, 0, 0])]),
            // block2
            op(
                vec![operand(Early, Def, Any, 4), operand(Late, Def, Any, 5)],
                vec![],
                false,
            ),
            branch(
                vec![operand(Early, Use, Stack, 2)],
                vec![r0],
                vec![call(1, &[]), call(3, &[4, 4])],
            ),
            // block3
            op(
                vec![
                    operand(Late, Use, reg, 0),
                    operand(Early, Use, Stack, 0),
                    operand(Early, Def, Stack, 8),
                ],
                vec![],
                true,
            ),
            branch(
                vec![operand(Early, Use, Any, 0)],
                vec![r0],
                vec![call(2, &[6, 6, 6])],
            ),
        ] {
            func.insts.push(&mut output, data).unwrap();
        }

        func.blocks = PrimaryMap::new();
        for (params, insts) in [
            (vec![val(0)], vec![inst(0), inst(1), inst(2), inst(3)]),
            (vec![], vec![inst(4), inst(5), inst(6)]),
            (vec![val(1), val(2), val(3)], vec![inst(7), inst(8)]),
            (vec![val(6), val(7)], vec![inst(9), inst(10)]),
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params,
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut machine = TestMachine {
            banks: vec![TestBank {
                log2_size: 0,
                regs: vec![1],
                non_allocatable: 0,
                groups: Vec::new(),
                classes: vec![TestClass {
                    members: TestClassMembers::Regs(vec![0]),
                    spill_cost: 0,
                }],
            }],
            regs_per_bank: None,
        };
        machine.fixup();

        let mut input = TestInput {
            options: InputOptions {
                validate_input: false,
                ..InputOptions::default()
            },
            machine,
            func,
        };
        input.fixup();
        input
    }

    /// A loop whose header takes two spilled parameters, where coloring them in
    /// order lets the first take the slot the second needs more.
    ///
    /// `block0` passes `v2` and `v1` to `block1`'s `v3` and `v4`, and the back
    /// edge passes `v4` to both. `v2` stays live through `block1`, so its slot
    /// is taken there, and `v3`, colored first, would take `v1`'s free slot,
    /// the one `v4` shares with its entry argument.
    pub fn with_two_params_competing_for_a_slot() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let inst = |i| Inst::try_new(i).unwrap();
        let block = |b| Block::try_new(b).unwrap();
        let val = |v| Val::try_new(v).unwrap();

        func.values = PrimaryMap::new();
        for def in [
            ValDef::BlockParam {
                block: block(0),
                i: 0,
            },
            ValDef::InstResult {
                inst: inst(1),
                i: 0,
            },
            ValDef::InstResult {
                inst: inst(4),
                i: 0,
            },
            ValDef::BlockParam {
                block: block(1),
                i: 0,
            },
            ValDef::BlockParam {
                block: block(1),
                i: 1,
            },
        ] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class: 0,
                        def,
                        remat: 0,
                    },
                )
                .unwrap();
        }

        let operand = |pos, kind, constraint, v| Operand::new(pos, kind, constraint, Some(val(v)));
        let reg = OperandConstraint::Reg(RegClass::try_new(0).unwrap());
        let call = |b, args: &[usize]| BlockCall {
            target: block(b),
            args: args.iter().map(|&v| val(v)).collect(),
        };
        let nop = || InstData::Op {
            operands: vec![],
            clobbers: vec![],
            side_effects: false,
        };

        func.insts = PrimaryMap::new();
        for data in [
            // block0
            InstData::Op {
                operands: vec![operand(
                    Position::Late,
                    DefUse::Use,
                    OperandConstraint::Any,
                    0,
                )],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![operand(
                    Position::Early,
                    DefUse::Def,
                    OperandConstraint::Any,
                    1,
                )],
                clobbers: vec![],
                side_effects: true,
            },
            nop(),
            nop(),
            InstData::Branch {
                operands: vec![
                    operand(Position::Late, DefUse::Def, OperandConstraint::Any, 2),
                    operand(Position::Early, DefUse::Use, reg, 0),
                ],
                clobbers: vec![],
                targets: vec![call(1, &[2, 1]), call(2, &[])],
            },
            // block1
            InstData::Op {
                operands: vec![
                    operand(Position::Late, DefUse::Use, OperandConstraint::Stack, 0),
                    operand(Position::Early, DefUse::Use, OperandConstraint::Stack, 3),
                    operand(Position::Early, DefUse::Use, reg, 0),
                ],
                clobbers: vec![],
                side_effects: false,
            },
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: vec![call(1, &[4, 4]), call(0, &[2])],
            },
            // block2
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: vec![],
            },
        ] {
            func.insts.push(&mut output, data).unwrap();
        }

        func.blocks = PrimaryMap::new();
        for (params, insts) in [
            (
                vec![val(0)],
                vec![inst(0), inst(1), inst(2), inst(3), inst(4)],
            ),
            (vec![val(3), val(4)], vec![inst(5), inst(6)]),
            (vec![], vec![inst(7)]),
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params,
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut machine = TestMachine {
            banks: vec![TestBank {
                log2_size: 0,
                regs: vec![1],
                non_allocatable: 0,
                groups: Vec::new(),
                classes: vec![TestClass {
                    members: TestClassMembers::Regs(vec![0]),
                    spill_cost: 0,
                }],
            }],
            regs_per_bank: Some(1),
        };
        machine.fixup();

        let mut input = TestInput {
            options: InputOptions {
                dead_move_elimination_level: crate::MoveEliminationLevel::Local,
                eliminate_dead_register_moves: false,
                hoist_demanded_moves: false,
                ..InputOptions::default()
            },
            machine,
            func,
        };
        input.fixup();
        input
    }

    /// Two predecessors each pass a spilled argument to one spilled block
    /// parameter.
    ///
    /// `block1` spills a second value while its argument is live, and that is
    /// the slot coloring `block2` would hand its argument first, so the two
    /// arguments land in different slots unless their shared parameter pulls
    /// them together.
    pub fn with_two_stack_args_to_one_stack_param() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let inst = |i| Inst::try_new(i).unwrap();
        let block = |b| Block::try_new(b).unwrap();
        let val = |v| Val::try_new(v).unwrap();
        let (arg1, temp, arg2, param) = (val(0), val(1), val(2), val(3));

        func.values = PrimaryMap::new();
        for def in [
            ValDef::InstResult {
                inst: inst(1),
                i: 0,
            },
            ValDef::InstResult {
                inst: inst(2),
                i: 0,
            },
            ValDef::InstResult {
                inst: inst(5),
                i: 0,
            },
            ValDef::BlockParam {
                block: block(3),
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

        let def = |val| InstData::Op {
            operands: vec![Operand::new(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Any,
                Some(val),
            )],
            clobbers: vec![],
            side_effects: true,
        };
        let stack_uses = |vals: &[Val]| InstData::Op {
            operands: vals
                .iter()
                .map(|&val| {
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Stack,
                        Some(val),
                    )
                })
                .collect(),
            clobbers: vec![],
            side_effects: true,
        };
        let branch = |targets: Vec<BlockCall>| InstData::Branch {
            operands: vec![],
            clobbers: vec![],
            targets,
        };

        func.insts = PrimaryMap::new();
        for data in [
            // block0
            branch(vec![
                BlockCall {
                    target: block(1),
                    args: vec![],
                },
                BlockCall {
                    target: block(2),
                    args: vec![],
                },
            ]),
            // block1
            def(arg1),
            def(temp),
            stack_uses(&[arg1, temp]),
            branch(vec![BlockCall {
                target: block(3),
                args: vec![arg1],
            }]),
            // block2
            def(arg2),
            stack_uses(&[arg2]),
            branch(vec![BlockCall {
                target: block(3),
                args: vec![arg2],
            }]),
            // block3, with a terminator of its own so that
            // `ensure_terminators` does not take the use away.
            stack_uses(&[param]),
            stack_uses(&[]),
        ] {
            func.insts.push(&mut output, data).unwrap();
        }

        func.blocks = PrimaryMap::new();
        for (params, insts) in [
            (vec![], vec![inst(0)]),
            (vec![], vec![inst(1), inst(2), inst(3), inst(4)]),
            (vec![], vec![inst(5), inst(6), inst(7)]),
            (vec![param], vec![inst(8), inst(9)]),
        ] {
            func.blocks
                .push(
                    &mut output,
                    BlockData {
                        params,
                        insts,
                        frequency: 0,
                    },
                )
                .unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_registers(),
            func,
        };
        input.fixup();
        input
    }

    /// A move from one spill slot to another with nowhere to stage it.
    pub fn with_a_stack_to_stack_move_and_no_free_register() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let arg_val = Val::try_new(0).unwrap();
        let resident_val = Val::try_new(1).unwrap();
        let param_val = Val::try_new(2).unwrap();
        let target = Block::try_new(1).unwrap();
        let both = RegClass::try_new(TestMachine::BOTH_REGS_CLASS.into()).unwrap();

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

        let operand = |pos, kind, constraint, val| Operand::new(pos, kind, constraint, Some(val));
        let op = |pos, kind, constraint, val| InstData::Op {
            operands: vec![operand(pos, kind, constraint, val)],
            clobbers: vec![],
            side_effects: true,
        };

        func.insts = PrimaryMap::new();
        for inst in [
            // block0: define the argument and the resident value, read the
            // argument off the stack so that it is there at the branch, and
            // pass it along. The branch's read of the resident value pins it
            // to the register on this side of the edge.
            op(Position::Late, DefUse::Def, OperandConstraint::Any, arg_val),
            op(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Any,
                resident_val,
            ),
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Stack,
                arg_val,
            ),
            InstData::Branch {
                operands: vec![operand(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Reg(both),
                    resident_val,
                )],
                clobbers: vec![],
                targets: vec![BlockCall {
                    target,
                    args: vec![arg_val],
                }],
            },
            // block1: the parameter off the stack beside the resident value
            // back in the register, pinning it there on this side of the edge
            // too. Then the argument off the stack again, so that it is still
            // live and cannot share the parameter's slot.
            InstData::Op {
                operands: vec![
                    operand(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Stack,
                        param_val,
                    ),
                    operand(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Reg(both),
                        resident_val,
                    ),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            op(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Stack,
                arg_val,
            ),
            // A terminator of the block's own, so that `ensure_terminators`
            // does not take the reads away.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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
                insts: vec![inst(0), inst(1), inst(2), inst(3)],
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

        let mut machine = TestMachine::two_registers();
        machine.set_regs_per_bank(1);

        let mut input = TestInput {
            options: InputOptions::default(),
            machine,
            func,
        };
        input.fixup();
        input
    }

    /// A cycle of moves from one spill slot to another with nothing free to
    /// break it with.
    pub fn with_a_cycle_of_stack_moves_and_no_free_register() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let resident_val = Val::try_new(0).unwrap();
        let first_val = Val::try_new(1).unwrap();
        let second_val = Val::try_new(2).unwrap();
        let first_param = Val::try_new(3).unwrap();
        let second_param = Val::try_new(4).unwrap();
        let header = Block::try_new(1).unwrap();
        let both = RegClass::try_new(TestMachine::BOTH_REGS_CLASS.into()).unwrap();

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
                inst: Inst::try_new(2).unwrap(),
                i: 0,
            },
            ValDef::BlockParam {
                block: header,
                i: 0,
            },
            ValDef::BlockParam {
                block: header,
                i: 1,
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

        let operand = |pos, kind, constraint, val| Operand::new(pos, kind, constraint, Some(val));
        let op = |pos, kind, constraint, val| InstData::Op {
            operands: vec![operand(pos, kind, constraint, val)],
            clobbers: vec![],
            side_effects: true,
        };
        let stack_use = |val| operand(Position::Early, DefUse::Use, OperandConstraint::Stack, val);
        let reg_use = |val| {
            operand(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(both),
                val,
            )
        };

        func.insts = PrimaryMap::new();
        for inst in [
            // block0: define the value that occupies the register and the two
            // the loop starts with, read the latter two off the stack so that
            // they have slots, and enter the loop. The branch reads the
            // resident value out of the register.
            op(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Any,
                resident_val,
            ),
            op(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Any,
                first_val,
            ),
            op(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Any,
                second_val,
            ),
            InstData::Op {
                operands: vec![stack_use(first_val), stack_use(second_val)],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Branch {
                operands: vec![reg_use(resident_val)],
                clobbers: vec![],
                targets: vec![BlockCall {
                    target: header,
                    args: vec![first_val, second_val],
                }],
            },
            // block1, the loop header: read both parameters off the stack,
            // which is what keeps them in slots, and test whether to go round
            // again.
            InstData::Op {
                operands: vec![
                    stack_use(first_param),
                    stack_use(second_param),
                    reg_use(resident_val),
                ],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: vec![
                    BlockCall {
                        target: Block::try_new(2).unwrap(),
                        args: vec![],
                    },
                    BlockCall {
                        target: Block::try_new(3).unwrap(),
                        args: vec![],
                    },
                ],
            },
            // block2, the loop body: hand the two parameters back the other
            // way round. Its branch reads the resident value too, so the
            // register is taken over the edge that carries the swap.
            InstData::Branch {
                operands: vec![reg_use(resident_val)],
                clobbers: vec![],
                targets: vec![BlockCall {
                    target: header,
                    args: vec![second_param, first_param],
                }],
            },
            // block3, the exit.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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
                insts: vec![inst(0), inst(1), inst(2), inst(3), inst(4)],
                frequency: 0,
            },
            BlockData {
                params: vec![first_param, second_param],
                insts: vec![inst(5), inst(6)],
                frequency: 0,
            },
            BlockData {
                params: vec![],
                insts: vec![inst(7)],
                frequency: 0,
            },
            BlockData {
                params: vec![],
                insts: vec![inst(8)],
                frequency: 0,
            },
        ] {
            func.blocks.push(&mut output, block).unwrap();
        }

        let mut machine = TestMachine::two_registers();
        machine.set_regs_per_bank(1);

        let mut input = TestInput {
            options: InputOptions::default(),
            machine,
            func,
        };
        input.fixup();
        input
    }

    /// A cycle of register-to-register moves running through every register
    /// the bank has, so that there is nothing free to break it with and
    /// nothing worth evicting either: a save would have to go above the very
    /// move that fills the victim. The cycle has to park on the stack.
    pub fn with_a_cycle_through_every_register() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let first_val = Val::try_new(0).unwrap();
        let second_val = Val::try_new(1).unwrap();
        let first_param = Val::try_new(2).unwrap();
        let second_param = Val::try_new(3).unwrap();
        let header = Block::try_new(1).unwrap();
        let both = RegClass::try_new(TestMachine::BOTH_REGS_CLASS.into()).unwrap();

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
            ValDef::BlockParam {
                block: header,
                i: 0,
            },
            ValDef::BlockParam {
                block: header,
                i: 1,
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

        let operand = |pos, kind, constraint, val| Operand::new(pos, kind, constraint, Some(val));
        let op = |pos, kind, constraint, val| InstData::Op {
            operands: vec![operand(pos, kind, constraint, val)],
            clobbers: vec![],
            side_effects: true,
        };
        let reg_use = |val| {
            operand(
                Position::Early,
                DefUse::Use,
                OperandConstraint::Reg(both),
                val,
            )
        };

        func.insts = PrimaryMap::new();
        for inst in [
            // block0: define the two values the loop starts with and enter it.
            op(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Any,
                first_val,
            ),
            op(
                Position::Late,
                DefUse::Def,
                OperandConstraint::Any,
                second_val,
            ),
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: vec![BlockCall {
                    target: header,
                    args: vec![first_val, second_val],
                }],
            },
            // block1, the loop header: read both parameters out of registers,
            // which is what keeps them there, and test whether to go round
            // again.
            InstData::Op {
                operands: vec![reg_use(first_param), reg_use(second_param)],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: vec![
                    BlockCall {
                        target: Block::try_new(2).unwrap(),
                        args: vec![],
                    },
                    BlockCall {
                        target: Block::try_new(3).unwrap(),
                        args: vec![],
                    },
                ],
            },
            // block2, the loop body: read both parameters out of registers
            // again, then hand them back the other way round. Both ends of
            // both moves are registers, and between them they are every
            // register the machine has.
            InstData::Op {
                operands: vec![reg_use(first_param), reg_use(second_param)],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: vec![BlockCall {
                    target: header,
                    args: vec![second_param, first_param],
                }],
            },
            // block3, the exit.
            InstData::Op {
                operands: vec![],
                clobbers: vec![],
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
                params: vec![first_param, second_param],
                insts: vec![inst(3), inst(4)],
                frequency: 0,
            },
            BlockData {
                params: vec![],
                insts: vec![inst(5), inst(6)],
                frequency: 0,
            },
            BlockData {
                params: vec![],
                insts: vec![inst(7)],
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

    /// A loop whose back edge swaps two values held in slots, on the machine
    /// whose two banks alias exactly, with a third value already parked out
    /// of the way.
    ///
    /// The batch on that edge is a two-slot swap plus a move whose ends
    /// overlap, which the solver drops. Staging the swap needs a register,
    /// and taking one evicts the other bank's too, so by the time the
    /// dropped move is looked at its register has already been lent out.
    /// A register in that state has its contents in a slot with a reload owed
    /// after the whole batch, which is precisely what the dropped move asks
    /// for, so it must not be counted a second time: a register cannot carry
    /// two brackets at once.
    pub fn with_a_dropped_move_on_a_lent_out_register() -> Self {
        let mut output = OutputInner::<u32>::new();
        let mut func = TestFunction::default();

        let val = |i| Val::try_new(i).unwrap();
        let block = |i| Block::try_new(i).unwrap();
        let wide = RegClass::try_new(TestMachine::WIDE_ALIAS_CLASS.into()).unwrap();

        func.values = PrimaryMap::new();
        for (reg_class, block, i) in [
            (TestMachine::NARROW_ALIAS_CLASS, block(0), 0),
            (TestMachine::WIDE_ALIAS_CLASS, block(0), 1),
            (TestMachine::NARROW_ALIAS_CLASS, block(1), 0),
            (TestMachine::NARROW_ALIAS_CLASS, block(1), 1),
        ] {
            func.values
                .push(
                    &mut output,
                    ValData {
                        reg_class,
                        def: ValDef::BlockParam { block, i },
                        remat: 0,
                    },
                )
                .unwrap();
        }

        func.insts = PrimaryMap::new();
        for inst in [
            // block0, the entry: hand its narrow parameter to both of the
            // loop header's parameters, so one value arrives in two places.
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: vec![
                    BlockCall {
                        target: block(1),
                        args: vec![val(0), val(0)],
                    },
                    BlockCall {
                        target: block(2),
                        args: vec![],
                    },
                ],
            },
            // block1, the loop header: the only read that pins anything to
            // the wide register, which is what keeps the two banks fighting
            // over the units they share.
            InstData::Op {
                operands: vec![Operand::new(
                    Position::Early,
                    DefUse::Use,
                    OperandConstraint::Reg(wide),
                    Some(val(1)),
                )],
                clobbers: vec![],
                side_effects: false,
            },
            // Round the loop with the two narrow parameters swapped, and back
            // to the entry with the wide one still live.
            InstData::Branch {
                operands: vec![],
                clobbers: vec![],
                targets: vec![
                    BlockCall {
                        target: block(1),
                        args: vec![val(3), val(2)],
                    },
                    BlockCall {
                        target: block(0),
                        args: vec![val(3), val(1)],
                    },
                ],
            },
            // block2, the exit: a late read of the entry parameter, happy to
            // take it from anywhere.
            InstData::Branch {
                operands: vec![Operand::new(
                    Position::Late,
                    DefUse::Use,
                    OperandConstraint::Any,
                    Some(val(0)),
                )],
                clobbers: vec![],
                targets: vec![],
            },
        ] {
            func.insts.push(&mut output, inst).unwrap();
        }

        let inst = |i| Inst::try_new(i).unwrap();
        func.blocks = PrimaryMap::new();
        for block in [
            BlockData {
                params: vec![val(0), val(1)],
                insts: vec![inst(0)],
                frequency: 37,
            },
            BlockData {
                params: vec![val(2), val(3)],
                insts: vec![inst(1), inst(2)],
                frequency: 0,
            },
            BlockData {
                params: vec![],
                insts: vec![inst(3)],
                frequency: 44,
            },
        ] {
            func.blocks.push(&mut output, block).unwrap();
        }

        let mut input = TestInput {
            options: InputOptions::default(),
            machine: TestMachine::two_aliasing_banks(),
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
/// `validate_input` is left alone: `TestInput::fixup` guarantees that the input
/// is valid, so turning it off would only lose coverage of the validator. Every
/// other option is mutated, so that the fuzzer explores their combinations.
#[derive(Default)]
pub struct InputOptionsMutator {}

impl Mutate<InputOptions> for InputOptionsMutator {
    fn mutate(
        &mut self,
        mutations: &mut mutatis::Candidates<'_>,
        options: &mut InputOptions,
    ) -> mutatis::Result<()> {
        mutations.mutation(|ctx| {
            mutate_move_elimination_level(ctx, &mut options.redundant_move_elimination_level)
        })?;

        mutations.mutation(|ctx| {
            mutate_move_elimination_level(ctx, &mut options.dead_move_elimination_level)
        })?;

        mutations.mutation(|ctx| {
            // Tracking fewer locations is simpler, so shrink towards `false`.
            options.eliminate_dead_register_moves = if ctx.shrink() {
                if !options.eliminate_dead_register_moves {
                    return Err(mutatis::error::Error::exhausted());
                }
                false
            } else {
                ctx.rng().gen_bool()
            };
            Ok(())
        })?;

        mutations.mutation(|ctx| {
            // Not narrowing is the simpler test case: it reserves each slot
            // across the whole live range, as the allocator always used to.
            options.narrow_spill_slot_live_ranges = if ctx.shrink() {
                if !options.narrow_spill_slot_live_ranges {
                    return Err(mutatis::error::Error::exhausted());
                }
                false
            } else {
                ctx.rng().gen_bool()
            };
            Ok(())
        })?;

        mutations.mutation(|ctx| {
            // Not hoisting leaves the edits as the other passes left them.
            options.hoist_demanded_moves = if ctx.shrink() {
                if !options.hoist_demanded_moves {
                    return Err(mutatis::error::Error::exhausted());
                }
                false
            } else {
                ctx.rng().gen_bool()
            };
            Ok(())
        })
    }
}

impl Generate<InputOptions> for InputOptionsMutator {
    fn generate(&mut self, ctx: &mut mutatis::Context) -> mutatis::Result<InputOptions> {
        Ok(InputOptions {
            redundant_move_elimination_level: gen_move_elimination_level(ctx)?,
            dead_move_elimination_level: gen_move_elimination_level(ctx)?,
            eliminate_dead_register_moves: ctx.rng().gen_bool(),
            narrow_spill_slot_live_ranges: ctx.rng().gen_bool(),
            hoist_demanded_moves: ctx.rng().gen_bool(),
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

/// The fixtures that every `TestInput` property check, the fuzz target's
/// corpus, and `the_corpus_all_checks_out` all start from.
///
/// Each entry is a shape the allocator has to get right: a critical edge, a
/// reuse of a value that survives its definition, a register group, a
/// rematerialized block argument, and so on. Mutating outwards from these
/// reaches interesting functions far sooner than mutating outwards from an
/// empty one.
pub fn corpus() -> Vec<TestInput> {
    let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();
    let group_class = RegClass::try_new(usize::from(TestMachine::GROUP_CLASS)).unwrap();
    vec![
        TestInput::default(),
        TestInput::with_more_spill_slot_groups_than_a_u8_can_index(),
        TestInput::with_spilled_merge_param(),
        TestInput::with_two_params_competing_for_a_slot(),
        TestInput::with_a_param_torn_between_a_vote_and_its_class(),
        TestInput::with_a_value_reloaded_on_every_arm(2),
        TestInput::with_a_reload_demanded_where_a_parameter_arrives(),
        TestInput::with_use_constraints(&[OperandConstraint::Reg(class)]),
        TestInput::with_use_constraints(&[OperandConstraint::Stack]),
        TestInput::with_use_constraints(&[OperandConstraint::Stack, OperandConstraint::Reg(class)]),
        // One stack use in the middle of a run of uses that do not care where
        // they read from, which is what cuts a live range into spans on either
        // side of it.
        TestInput::with_use_constraints(&[
            OperandConstraint::Any,
            OperandConstraint::Stack,
            OperandConstraint::Any,
            OperandConstraint::Any,
        ]),
        TestInput::with_group_use_constraints(&[
            OperandConstraint::Stack,
            OperandConstraint::Reg(group_class),
        ]),
        // The same value on the stack between two uses in its register group:
        // the spill and reload of a single member of a group.
        TestInput::with_group_use_constraints(&[
            OperandConstraint::Reg(group_class),
            OperandConstraint::Stack,
            OperandConstraint::Reg(group_class),
        ]),
        TestInput::with_reuse_def(OperandConstraint::Any),
        TestInput::with_reuse_of_a_surviving_value(),
        TestInput::with_two_reads_and_a_reuse_of_a_surviving_value(),
        TestInput::with_a_fixed_read_beside_a_reuse_of_a_surviving_value(),
        TestInput::with_a_pinned_read_before_a_reuse_that_reads_twice(),
        TestInput::with_a_pinned_read_before_a_reuse_of_an_unpinned_read(),
        TestInput::with_a_pinned_read_before_a_reuse_of_a_dying_value(),
        TestInput::with_a_pinned_read_after_a_reuse_target(),
        TestInput::with_a_reuse_of_a_live_in_value(),
        TestInput::with_two_reuses_at_one_point(),
        TestInput::with_two_reuses_of_a_dying_value(),
        TestInput::with_block_arg_constraints(OperandConstraint::Any, OperandConstraint::Stack),
        TestInput::with_stack_param_and_arg(),
        // The same edge with the machine's one register held by something
        // else, so the move has nowhere to go but through a borrowed one.
        TestInput::with_a_stack_to_stack_move_and_no_free_register(),
        // A cycle of those, which can only be broken by parking a value in
        // an emergency slot.
        TestInput::with_a_cycle_of_stack_moves_and_no_free_register(),
        // A cycle running through the whole bank, leaving nothing to break
        // it with but the stack.
        TestInput::with_a_cycle_through_every_register(),
        // A move the solver drops, naming a register the batch beside it has
        // already evicted.
        TestInput::with_a_dropped_move_on_a_lent_out_register(),
        TestInput::with_a_rematerialized_block_arg(),
        TestInput::with_two_uses_of_different_values(),
        TestInput::with_a_critical_edge(),
        // A value carried around a loop and read only past it.
        TestInput::with_a_looping_value_read_only_after_the_loop(),
        TestInput::with_a_value_read_on_the_stack_after_a_loop_exit(),
        TestInput::with_a_value_from_before_a_loop_read_on_the_stack_after_it(),
        // A register-to-register move a later block overwrites: the corpus's
        // one dead register-to-register move.
        TestInput::with_a_register_move_overwritten_in_a_later_block(),
        TestInput::with_values_in_two_banks_spilled_and_reloaded(),
        // A value defined outside a loop that spends part of its live range on
        // the stack inside it, which is where a spill has a region to be
        // hoisted out of.
        TestInput::with_a_value_spilled_inside_a_loop(),
        // A value defined in a loop and read past its exit, where the exit is
        // itself a legal store site: the store belongs on the edge into it.
        TestInput::with_a_value_defined_in_a_loop_and_read_past_its_exit(),
        // A loop nest, whose two loops must be separate regions so that an
        // outer-loop value's spill stays out of the inner loop.
        TestInput::with_a_nested_loop(),
        // A cycle entered at two different blocks, so no natural loop.
        TestInput::with_an_irreducible_loop(),
        TestInput::with_a_def_only_value_under_pressure(),
        // A recomputable value whose register-pinned read narrows to its early
        // half, leaving a carrier that is recomputable only after narrowing.
        TestInput::with_a_recomputable_value_read_under_full_pressure(),
        TestInput::with_a_stack_constrained_value_under_pressure(),
        TestInput::with_three_values_needing_two_register_groups(),
        TestInput::with_a_value_reloaded_past_a_diamond(),
        TestInput::with_an_entry_param_read_two_ways(),
        TestInput::with_two_entry_params(),
        TestInput::with_entry_params_in_two_banks(),
        TestInput::with_a_self_looping_entry_block(),
        // The same self loop with the parameter split at the top of the block:
        // the gap atop the entry block is the one gap two paths share, so an
        // edge into it cannot lean on the store there the way any other edge
        // can.
        TestInput::with_a_spilled_self_looping_entry_param(),
        TestInput::with_a_move_before_an_unconditional_branch(),
        TestInput::with_a_val_less_read_of_a_non_allocatable_reg(),
        TestInput::with_a_reuse_of_a_pinned_read(),
        TestInput::with_a_read_overwritten_by_a_fixed_def(),
        TestInput::with_a_dying_read_overwritten_by_a_fixed_def(),
        TestInput::with_two_reads_overwritten_by_a_fixed_def(),
        TestInput::with_a_fixed_def_before_a_reuse_of_its_pinned_read(),
        TestInput::with_one_value_read_from_two_registers(),
        TestInput::with_a_clobber_beside_a_live_through_value(),
        TestInput::with_an_early_read_beside_a_clobber_of_every_register(),
        TestInput::with_a_clobbering_terminator_before_a_merge(),
        TestInput::with_a_reload_clobbered_before_its_next_read(),
        TestInput::with_a_fixed_def_on_a_terminator(OperandConstraint::Any),
        TestInput::with_a_fixed_def_on_a_terminator(OperandConstraint::Stack),
        TestInput::with_a_terminator_passing_its_own_result(),
        TestInput::with_a_fixed_def_spilled_beside_a_fixed_read(),
        TestInput::with_a_reload_under_a_reversed_group_reservation(),
        TestInput::with_a_recomputed_value_pinned_at_a_block_start(),
        // A value live across four blocks and read in two of them. Given a
        // remat cost, its spans are cut at every instruction and absent from
        // the block that never mentions it, which is the shape gaps have to be
        // crossed in.
        {
            let mut input = TestInput::with_a_value_read_in_two_distant_blocks();
            input.set_remat_costs(Some(RematCost::AlwaysRemat));
            input
        },
        // The same gaps, crossed under register pressure and with a store to
        // place: a value we always recompute, read on the stack past a block
        // that keeps every register busy without ever mentioning it.
        {
            let mut input = TestInput::with_a_value_read_on_the_stack_past_a_crowded_block();
            input.set_remat_costs(Some(RematCost::AlwaysRemat));
            input
        },
        // A value recomputed at a read after a gap, beside a second value
        // that is spilled and reloaded: the rematerialization comes at the
        // earlier position of the two, the one shape where the index a move is
        // emitted with is not the index it lands at.
        TestInput::with_a_recomputed_read_before_a_spill_and_a_reload(),
        // A value we always recompute, read where both registers are spoken
        // for: recomputing is still no reason to deny its use a register.
        TestInput::with_a_recomputed_read_under_pressure(),
        // Every register held by a value that does not need one, and a
        // minimal read that does: the register has to come from somewhere.
        TestInput::with_a_minimal_register_read_among_stackable_values(),
        // A value carried past a block that wants every register, cheap enough
        // to recompute that the crossing piece gets no location at all.
        {
            let mut input = TestInput::with_a_value_carried_past_a_crowded_block(false);
            input.set_remat_costs(Some(RematCost::CheaperThanReload));
            input
        },
        // The same, but passed to the successor, so that piece is a move's
        // source and needs somewhere real to be read from after all.
        {
            let mut input = TestInput::with_a_value_carried_past_a_crowded_block(true);
            input.set_remat_costs(Some(RematCost::CheaperThanReload));
            input
        },
        // A value that arrives in a block from a piece holding it nowhere, and
        // has a slot: the store cannot go at that block's start, where the
        // recomputation that fills the register has not run yet.
        {
            let mut input = TestInput::with_a_value_stored_where_it_arrives_from_nowhere();
            input.set_remat_costs(Some(RematCost::CheaperThanReload));
            input
        },
        // Drives the early-half reload in `split_into_minimal_or_spill`.
        TestInput::with_an_early_read_under_a_full_late_half(),
        // Two sibling loops that only agree on a register through hints
        // relayed by their parent.
        TestInput::with_a_value_read_in_two_sibling_loops(),
    ]
}

/// Run the register allocator on `test_input` and check the allocation it
/// produces against the function it allocated.
///
/// This is the property the fuzz target fuzzes, kept here rather than in the
/// fuzz crate so that the fuzzer and `cargo test` are kept in sync.
///
/// `Err` is a bug in the allocator; `Ok` covers both "the allocation checks
/// out" and "the allocator gave up because the function does not fit on its
/// machine", since not every function fits on every machine.
#[cfg(any(test, feature = "checker"))]
pub fn check_allocation(test_input: &TestInput) -> Result<(), alloc::string::String> {
    use alloc::format;

    let mut context = crate::Context::new();
    assert!(context.is_reset());

    let result = test_input.with_input(|input| -> Result<(), alloc::string::String> {
        let output = match crate::run(&mut context, input) {
            Ok(output) => output,
            // Not the checker's problem: this function needs more registers
            // than this machine has.
            Err(crate::Error::TooManyLiveRegs) => return Ok(()),
            Err(e) => return Err(format!("allocation failed: {e:?}")),
        };
        crate::checker::check(input, &output).map_err(|e| format!("{e:?}"))
    });

    // The pipeline leaves nothing behind that a reset does not clean up.
    context.reset();
    assert!(context.is_reset());

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        error::{Error, InternalError},
        validation,
    };
    use mutatis::{
        check::{Check, CheckResult},
        mutators as m,
    };
    use std::{format, string::String};

    /// A `Context` is reusable across allocations even when an allocation made
    /// it take the `EntityReprTooSmall` retry path.
    ///
    /// The narrow context that bailed never finished its passes, so it holds
    /// partial state that only `reset` will clear. `run` asserts a reset
    /// context, and that assert is a plain `assert!`, so a `reset` that left
    /// the abandoned context dirty would fail the *second* `run` here even in
    /// a release build.
    #[test]
    fn a_context_is_reusable_after_the_entity_repr_retry() {
        let input = TestInput::with_more_spill_slot_groups_than_a_u8_can_index();
        let mut context = crate::Context::new();

        for _ in 0..2 {
            input
                .with_input(|input| crate::run(&mut context, input).map(|_| ()))
                .expect("the wider representation fits this input");
            context.reset();
            assert!(context.is_reset());
        }
    }

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
                    let (DefUse::Def, Some(val)) = (op.kind(), op.val()) else {
                        continue;
                    };
                    let expected = ValDef::InstResult { inst, i };
                    let actual = &func.values[val].def;
                    if *actual != expected {
                        return Err(format!(
                            "{val:?} is definition {i} of {inst:?}, but its `ValData::def` \
                             says {actual:?}",
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
        Check::new()
            .min_iters(1_000)
            .min_duration(std::time::Duration::from_secs(1))
            .run_with(m::default::<TestInput>(), corpus(), |input: &TestInput| {
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

    /// `with_input` hands the move-elimination options it holds down to the
    /// allocator.
    #[test]
    fn with_input_reports_the_move_elimination_options() {
        let mut input = TestInput::default();
        assert_eq!(
            input.options.redundant_move_elimination_level,
            InputOptions::default().redundant_move_elimination_level,
        );
        assert_eq!(
            input.options.dead_move_elimination_level,
            InputOptions::default().dead_move_elimination_level,
        );

        for redundant in MoveEliminationLevel::ALL {
            for dead in MoveEliminationLevel::ALL {
                for regs in [false, true] {
                    input.options.redundant_move_elimination_level = redundant;
                    input.options.dead_move_elimination_level = dead;
                    input.options.eliminate_dead_register_moves = regs;
                    input.with_input(|input| {
                        assert_eq!(input.options.redundant_move_elimination_level, redundant);
                        assert_eq!(input.options.dead_move_elimination_level, dead);
                        assert_eq!(input.options.eliminate_dead_register_moves, regs);
                    });
                }
            }
        }
    }

    /// `InputOptionsMutator` varies every move-elimination option, so the
    /// checks generating `TestInput`s exercise all of them.
    ///
    /// Both levels are checked separately: a mutator varying one and leaving the
    /// other at its default would leave a whole pass untested.
    #[test]
    fn generates_every_move_elimination_option() {
        let mut session = mutatis::Session::new().seed(0);
        let mut redundant = Vec::new();
        let mut dead = Vec::new();
        let mut regs = Vec::new();
        for _ in 0..100 {
            let options: InputOptions = session.generate().unwrap();
            if !redundant.contains(&options.redundant_move_elimination_level) {
                redundant.push(options.redundant_move_elimination_level);
            }
            if !dead.contains(&options.dead_move_elimination_level) {
                dead.push(options.dead_move_elimination_level);
            }
            if !regs.contains(&options.eliminate_dead_register_moves) {
                regs.push(options.eliminate_dead_register_moves);
            }
        }
        let all = MoveEliminationLevel::ALL.len();
        assert_eq!(redundant.len(), all, "only generated {redundant:?}");
        assert_eq!(dead.len(), all, "only generated {dead:?}");
        assert_eq!(regs.len(), 2, "only generated {regs:?}");
    }

    /// `InputOptionsMutator` really does vary spill slot range narrowing, so
    /// that the checks which generate `TestInput`s exercise both paths.
    #[test]
    fn generates_both_spill_slot_live_range_widths() {
        let mut session = mutatis::Session::new().seed(0);
        let mut seen = Vec::new();
        for _ in 0..100 {
            let options: InputOptions = session.generate().unwrap();
            if !seen.contains(&options.narrow_spill_slot_live_ranges) {
                seen.push(options.narrow_spill_slot_live_ranges);
            }
        }
        assert_eq!(seen.len(), 2, "only generated {seen:?}");
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
            .min_iters(1_000)
            .min_duration(std::time::Duration::from_secs(1))
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
    /// mutation, and every register it adds reaches every class the allocator
    /// owns.
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
                        // A class of registers the allocator does not own is
                        // not somewhere a new register could go: it holds the
                        // one register an operand reads, and widening the bank
                        // gives the allocator nothing there. The padding pass
                        // leaves such a class alone, so skip it here too.
                        if usize::from(regs[0]) >= REGS {
                            continue;
                        }

                        // Membership rather than a count: a class the
                        // allocator does own may have been written down with
                        // its members in any order, and padding appends.
                        for reg in 0..u8::try_from(REGS).unwrap() {
                            assert!(
                                regs.contains(&reg),
                                "a class of bank {i} is missing register {reg} of its {REGS} \
                                 {when}",
                            );
                        }
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
            assert_eq!(operands[0].val(), Some(val));
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
    fn reject_blocks_indexed_out_of_layout_order() {
        let mut func = valid_func(2, 1);
        let first = Block::try_new(0).unwrap();
        let second = Block::try_new(1).unwrap();

        // Swap the two blocks' instructions, so that the higher-indexed block
        // holds the earlier ones. Every instruction is still in exactly one
        // block and the runs still partition the index space; only the order
        // of the two runs against the two block indices changes.
        let first_insts = mem::take(&mut func.blocks[first].insts);
        let second_insts = mem::replace(&mut func.blocks[second].insts, first_insts);
        func.blocks[first].insts = second_insts;
        for (block, block_data) in func.blocks.iter() {
            for &inst in &block_data.insts {
                func.inst_blocks[inst] = Some(block);
            }
        }

        // The run that sorts second holds `first`'s instructions, and `first`
        // has the smaller index, so it is the block blamed.
        assert_invalid!(&func, Error::BlocksOutOfLayoutOrder { block: b } if b == first);
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

    /// A rematerialization computes its value from nothing, so a block
    /// parameter --- whose definition is the argument its predecessors pass
    /// --- can never carry a cost.
    #[test]
    fn reject_a_remat_cost_on_a_block_parameter() {
        let mut input =
            TestInput::with_block_arg_constraints(OperandConstraint::Any, OperandConstraint::Any);
        let param = input
            .func
            .values
            .iter()
            .find(|(_, val_data)| matches!(val_data.def, ValDef::BlockParam { .. }))
            .map(|(val, _)| val)
            .expect("this fixture passes a value as a block argument");

        // Not `set_remat_costs`, which honors `can_remat` and so would refuse
        // to build the input this checks we reject.
        input.func.values[param].remat = 1;

        let actual = expect_invalid_with(&input.machine.build(), &input.func);
        assert!(
            matches!(actual, Error::RematOfDerivedValue { val, def: None } if val == param),
            "expected a parameter `RematOfDerivedValue`, got {actual:?}",
        );
    }

    /// A `Remat` names one destination register, so a value that occupies a
    /// whole register group can never carry a cost.
    #[test]
    fn reject_a_remat_cost_on_a_register_group() {
        let mut input = TestInput::with_group_use_constraints(&[OperandConstraint::Any]);
        let val = Val::try_new(0).unwrap();
        input.func.values[val].remat = 1;

        let actual = expect_invalid_with(&input.machine.build(), &input.func);
        assert!(
            matches!(actual, Error::RematOfRegGroup { val: v } if v == val),
            "expected a `RematOfRegGroup`, got {actual:?}",
        );
    }

    /// A rematerialization recomputes its value wherever it is placed, from
    /// whatever happens to be lying around there, so a value whose definition
    /// reads something can never carry a cost.
    #[test]
    fn reject_a_remat_cost_on_a_value_whose_definition_reads() {
        let mut output = OutputInner::<u32>::new();
        let mut input = TestInput::with_use_constraints(&[OperandConstraint::Any]);

        // `inst1` reads the value `inst0` defines. Give it a definition of its
        // own, so that a value is defined by an instruction that reads.
        let reader = Inst::try_new(1).unwrap();
        let reg_class = input.func.values[Val::try_new(0).unwrap()].reg_class;
        let derived = input
            .func
            .values
            .push(
                &mut output,
                ValData {
                    reg_class,
                    def: ValDef::InstResult { inst: reader, i: 0 },
                    remat: 1,
                },
            )
            .unwrap();
        input.func.operands_mut(reader).push(Operand::new(
            Position::Late,
            DefUse::Def,
            OperandConstraint::Any,
            Some(derived),
        ));

        let actual = expect_invalid_with(&input.machine.build(), &input.func);
        assert!(
            matches!(
                actual,
                Error::RematOfDerivedValue { val, def: Some(def) }
                    if val == derived && def == reader
            ),
            "expected an instruction `RematOfDerivedValue`, got {actual:?}",
        );
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
        func.values[operand.val().unwrap()].reg_class = 0;
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
        func.values[operand.val().unwrap()].reg_class = 0;
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
    /// plus the two classes that name each of them alone.
    ///
    /// Class 0 is the only one a value may belong to, and class 1 is the only
    /// one a val-less operand may name. There is no class holding both, a
    /// class being wholly one kind or the other.
    ///
    /// [`TestMachine::with_a_non_allocatable_reg`] describes the same shape
    /// for the tests that need a whole `TestInput`; this one stays because the
    /// checks below want a bare `Machine` and nothing else.
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

        builder.define_reg_class(bank, 1.0, [reg]).unwrap();
        builder
            .define_reg_class(bank, 1.0, [non_allocatable])
            .unwrap();

        builder.finish().unwrap()
    }

    /// A definition constrained to a class with no register the allocator owns
    /// has nowhere to go, so it is the input that is wrong and not any
    /// allocation of it.
    #[test]
    fn reject_a_definition_pinned_to_a_non_allocatable_register() {
        let mut func = valid_func(1, 1);
        let block = Block::try_new(0).unwrap();
        let inst = func.blocks[block].insts[0];

        let machine = machine_with_a_non_allocatable_class();
        let operand = &mut func.insts[inst].operands_mut()[0];
        assert_eq!(operand.kind(), DefUse::Def);
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
                Error::OperandWithValInNonAllocatableRegClass { inst: i, operand: 0 }
                    if i == inst,
            ),
            "expected an `OperandWithValInNonAllocatableRegClass`, got {actual:?}",
        );
    }

    /// A *use* cannot name one either, so long as it names a value: such a
    /// class is how an operand reads a register the allocator does not own,
    /// and an operand that does so names no value at all.
    #[test]
    fn reject_a_use_of_a_value_pinned_to_a_non_allocatable_register() {
        let mut func = valid_func(1, 2);
        let block = Block::try_new(0).unwrap();
        let inst = func.blocks[block].insts[1];

        let machine = machine_with_a_non_allocatable_class();
        let operand = &mut func.operands_mut(inst)[0];
        assert_eq!(operand.kind(), DefUse::Def);
        *operand = Operand::new(
            operand.pos(),
            DefUse::Use,
            OperandConstraint::Reg(RegClass::try_new(1).unwrap()),
            Some(Val::try_new(0).unwrap()),
        );

        let actual = expect_invalid_with(&machine, &func);
        assert!(
            matches!(
                actual,
                Error::OperandWithValInNonAllocatableRegClass { inst: i, operand: 0 }
                    if i == inst,
            ),
            "expected an `OperandWithValInNonAllocatableRegClass`, got {actual:?}",
        );
    }

    /// Reading a register the allocator does not own is spelled by naming no
    /// value at all, which is exactly how an instruction says it reads the
    /// stack pointer.
    #[test]
    fn accept_a_val_less_use_pinned_to_a_non_allocatable_register() {
        let mut func = valid_func(1, 1);
        let block = Block::try_new(0).unwrap();
        let inst = func.blocks[block].insts[0];

        func.operands_mut(inst).push(Operand::new(
            Position::Early,
            DefUse::Use,
            OperandConstraint::Reg(RegClass::try_new(1).unwrap()),
            None,
        ));

        let machine = machine_with_a_non_allocatable_class();
        assert_eq!(check_ssa(&machine, &func), Ok(()));
    }

    /// An operand naming no value asks the allocator for nothing, so anything
    /// but a read of a register the allocator does not own leaves it asking
    /// for a home for something that does not exist.
    #[test]
    fn reject_val_less_operands_that_are_not_fixed_reads() {
        let non_allocatable = OperandConstraint::Reg(RegClass::try_new(1).unwrap());
        let allocatable = OperandConstraint::Reg(RegClass::try_new(0).unwrap());

        for (kind, constraint, why) in [
            (DefUse::Def, non_allocatable, "a definition of no value"),
            (DefUse::Use, OperandConstraint::Any, "unconstrained"),
            (DefUse::Use, OperandConstraint::Stack, "on the stack"),
            (DefUse::Use, allocatable, "pinned to the allocator's own"),
        ] {
            let mut func = valid_func(1, 1);
            let block = Block::try_new(0).unwrap();
            let inst = func.blocks[block].insts[0];
            func.operands_mut(inst)
                .push(Operand::new(Position::Early, kind, constraint, None));

            let machine = machine_with_a_non_allocatable_class();
            let actual = expect_invalid_with(&machine, &func);
            assert!(
                matches!(
                    actual,
                    Error::OperandWithoutValIsNotAFixedUse { inst: i, operand: 1 } if i == inst,
                ),
                "expected an `OperandWithoutValIsNotAFixedUse` for an operand {why}, \
                 got {actual:?}",
            );
        }
    }

    /// A `Reuse` is defined in the register its target reads its value from,
    /// so a target that reads no value leaves the definition tied to nothing.
    #[test]
    fn reject_a_reuse_of_an_operand_without_a_value() {
        let mut func = valid_func(1, 1);
        let block = Block::try_new(0).unwrap();
        let inst = func.blocks[block].insts[0];

        // Operand 1 reads a register the allocator does not own; operand 0,
        // the definition, ties itself to it.
        func.operands_mut(inst).push(Operand::new(
            Position::Early,
            DefUse::Use,
            OperandConstraint::Reg(RegClass::try_new(1).unwrap()),
            None,
        ));
        let operand = &mut func.operands_mut(inst)[0];
        assert_eq!(operand.kind(), DefUse::Def);
        *operand = Operand::new(
            Position::Late,
            operand.kind(),
            OperandConstraint::Reuse(1),
            operand.val(),
        );

        let machine = machine_with_a_non_allocatable_class();
        let actual = expect_invalid_with(&machine, &func);
        assert!(
            matches!(
                actual,
                Error::ReuseOfOperandWithoutVal { inst: i, operand: 0 } if i == inst,
            ),
            "expected a `ReuseOfOperandWithoutVal`, got {actual:?}",
        );
    }

    /// A value belongs wherever the allocator decides to put it, so a class
    /// the allocator owns nothing in is nowhere a value can belong: there is
    /// no home in it for the allocator to give out.
    #[test]
    fn reject_a_value_in_a_class_the_allocator_owns_nothing_in() {
        let mut func = valid_func(1, 1);
        for (_val, val_data) in func.values.iter_mut() {
            val_data.reg_class = 1;
        }

        let machine = machine_with_a_non_allocatable_class();
        let actual = expect_invalid_with(&machine, &func);
        assert!(
            matches!(actual, Error::NonAllocatableRegInValClass { val } if val.index() == 0),
            "expected a `NonAllocatableRegInValClass`, got {actual:?}",
        );
    }

    /// A parameter arrives wherever the allocator decides to put it, so a
    /// class that holds a register the allocator does not own would let it
    /// arrive in one --- a definition there spelled a longer way --- however
    /// the arguments passed to it are themselves constrained. Which is just
    /// the rule every value obeys, parameters included.
    #[test]
    fn reject_a_block_parameter_in_a_class_holding_a_non_allocatable_register() {
        let mut input =
            TestInput::with_block_arg_constraints(OperandConstraint::Any, OperandConstraint::Any);
        input.machine = TestMachine::with_a_non_allocatable_reg();

        let param = Val::try_new(1).unwrap();
        assert!(matches!(
            input.func.values[param].def,
            ValDef::BlockParam { .. }
        ));

        // Both values, so that the argument still agrees with the parameter it
        // is passed to and it is the class rule alone that is broken.
        for (_val, val_data) in input.func.values.iter_mut() {
            val_data.reg_class = TestMachine::PINNED_CLASS;
        }

        let actual = expect_invalid_with(&input.machine.build(), &input.func);
        assert!(
            matches!(actual, Error::NonAllocatableRegInValClass { .. }),
            "expected a `NonAllocatableRegInValClass`, got {actual:?}",
        );
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
                    Some(val(0)),
                )],
                clobbers: vec![],
                side_effects: true,
            },
            InstData::Op {
                operands: vec![
                    Operand::new(
                        Position::Early,
                        DefUse::Use,
                        OperandConstraint::Any,
                        Some(val(0)),
                    ),
                    Operand::new(
                        Position::Late,
                        DefUse::Def,
                        OperandConstraint::Reuse(0),
                        Some(val(1)),
                    ),
                ],
                clobbers: vec![],
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
        operands.push(Operand::new(Position::Late, DefUse::Def, reuse, Some(val)));
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
        let reused = input.func.insts[inst].operands()[target].val().unwrap();

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
            Some(reused),
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

    /// A `regs_per_bank` out of range reaches `fixup` from `Deserialize`,
    /// which does not go through `set_regs_per_bank`.
    #[test]
    fn fixup_clamps_regs_per_bank() {
        for (asked, want) in [
            (0, 1),
            (1, 1),
            (64, 64),
            (65, TestMachine::MAX_REGS_PER_BANK_TARGET),
            (350, TestMachine::MAX_REGS_PER_BANK_TARGET),
            (usize::MAX, TestMachine::MAX_REGS_PER_BANK_TARGET),
        ] {
            let mut machine = TestMachine::two_registers();
            machine.regs_per_bank = Some(asked);
            machine.fixup();

            assert_eq!(machine.regs_per_bank, Some(want), "asked for {asked}");
            for bank in &machine.banks {
                assert_eq!(bank.regs.len(), want, "asked for {asked}");
            }

            // Idempotent, so that a clamped machine survives the next
            // mutation unchanged.
            let mut again = machine.clone();
            again.fixup();
            assert_eq!(again.regs_per_bank, machine.regs_per_bank);

            machine.build();
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
        let (reusing, reused) = (operands[j].val().unwrap(), operands[target].val().unwrap());
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

    /// Seed a fuzz target's corpus from a set of fixtures.
    ///
    /// Keeping this in `cargo test` rather than in a separate step means a new
    /// fixture reaches the fuzzer without a second edit. The write is
    /// idempotent, and `fuzz/corpus/` is gitignored.
    fn write_fuzz_corpus_for<T>(target: &str, entries: Vec<T>, fixup: impl Fn(&mut T))
    where
        T: serde::Serialize + serde::de::DeserializeOwned,
    {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("fuzz")
            .join("corpus")
            .join(target);
        std::fs::create_dir_all(&dir).unwrap();

        for (i, entry) in entries.into_iter().enumerate() {
            let encoded = postcard::to_allocvec(&entry).unwrap();

            let (mut decoded, rest) =
                postcard::take_from_bytes::<T>(&encoded).unwrap_or_else(|e| {
                    panic!("corpus entry {i} does not decode: {e}");
                });
            assert!(
                rest.is_empty(),
                "corpus entry {i} left {} bytes over",
                rest.len()
            );

            // `fixup` is what rebuilds the derived state that the encoding
            // deliberately omits; it is exactly what the fuzz target does
            // after decoding.
            fixup(&mut decoded);
            assert_eq!(
                postcard::to_allocvec(&decoded).unwrap(),
                encoded,
                "corpus entry {i} does not survive a postcard round trip",
            );

            std::fs::write(dir.join(std::format!("{i}.postcard")), &encoded).unwrap();
        }
    }

    /// Seed the `allocate` fuzz target's corpus from [`corpus`].
    #[test]
    fn write_fuzz_corpus() {
        write_fuzz_corpus_for("allocate", corpus(), TestInput::fixup);
    }

    /// Seed the `parallel_moves` fuzz target's corpus from
    /// [`parallel_moves_corpus`].
    #[test]
    fn write_parallel_moves_fuzz_corpus() {
        write_fuzz_corpus_for(
            "parallel_moves",
            parallel_moves_corpus(),
            TestParallelMoves::fixup,
        );
    }
}
