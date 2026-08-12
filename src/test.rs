//! Test utilities.

#![allow(missing_docs)]

mod dominators;

use crate::{
    Block, InputBlock, InputFunction, InputInst, Operand, Val,
    dfs::{Dfs, DfsEvent},
    entity::{Entity, EntityRepr, Inst, PrimaryMap},
    input::{DefUse, FmtWithOutput, OperandPos},
    output::OutputInner,
};
use alloc::{vec, vec::Vec};
use core::{
    fmt::{self, Display},
    hash::Hasher,
    marker::PhantomData,
    mem,
};
use dominators::DominatorTree;
use mutatis::{DefaultMutate, Generate, Mutate};
use std::{
    collections::{BTreeSet, HashMap, HashSet, hash_map::Entry},
    dbg,
};

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
        let max = E::MAX.index();
        let value = E::try_new(new_index % max).unwrap();
        Ok(value)
    }
}

macro_rules! entity_default_mutate {
    ( $( $name:ident )* ) => {
        $(
            impl<E> DefaultMutate for crate::entity::$name<E>
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
    LiveRange
    Bundle
}

#[derive(Clone, Default, Debug, Hash, Mutate)]
pub struct BlockCall {
    target: Block,
    args: Vec<Val>,
}

#[derive(Clone, Debug, Hash, Mutate)]
pub enum InstData {
    Op {
        args: Vec<Operand>,
        results: Vec<Operand>,
        side_effects: bool,
    },
    Branch {
        args: Vec<Operand>,
        targets: Vec<BlockCall>,
    },
}

impl Default for InstData {
    fn default() -> Self {
        Self::Op {
            results: vec![],
            args: vec![],
            side_effects: false,
        }
    }
}

#[derive(Clone, Default, Debug, Hash, Mutate)]
pub struct ValData {
    ty: Type,
    def: ValDef,
}

#[derive(Clone, Debug, Hash, Mutate)]
pub enum ValDef {
    InstResult { inst: Inst, i: usize },
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
}

#[derive(Clone, Hash)]
pub struct TestFunction {
    mutated: bool,
    values: PrimaryMap<Val, ValData>,
    blocks: PrimaryMap<Block, BlockData>,
    insts: PrimaryMap<Inst, InstData>,
    dominators: DominatorTree,
}

impl Default for TestFunction {
    fn default() -> Self {
        let mut func = TestFunction {
            mutated: false,
            values: PrimaryMap::default(),
            blocks: PrimaryMap::default(),
            insts: PrimaryMap::default(),
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

fn hash(func: &TestFunction) -> u64 {
    use std::hash::Hash;
    let mut hasher = std::hash::DefaultHasher::new();
    <TestFunction as Hash>::hash(func, &mut hasher);
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
    pub fn fixup(&mut self) {
        let mut output = OutputInner::<u32>::new();
        self.ensure_non_empty(&mut output);
        let (old_to_new, old_insts) = self.ensure_unique_insts_in_layout(&mut output);
        self.ensure_terminators(&mut output);
        self.ensure_all_blocks_are_reachable(&mut output);
        self.fixup_dominator_tree();
        self.ensure_values_in_bounds(&mut output);
        // TODO: fixup values in bounds
        // TODO: fixup values uses dominated by defs
        // TODO: fixup block args
    }

    fn ensure_non_empty(&mut self, output: &mut OutputInner<u32>) {
        if self.blocks.is_empty() {
            self.blocks
                .push(
                    output,
                    BlockData {
                        params: vec![],
                        insts: vec![],
                    },
                )
                .unwrap();
        }

        if self.insts.is_empty() {
            self.insts
                .push(
                    output,
                    InstData::Op {
                        args: vec![],
                        results: vec![Operand {
                            pos: OperandPos::Early,
                            kind: DefUse::Def,
                            val: Val::try_new(0).unwrap(),
                        }],
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
    }

    /// Make sure each instruction appears in the layout exactly once, cloning
    /// instructions as needed, and dropping instructions that aren't in the
    /// layout.
    ///
    /// Returns a map from old `Inst`s to new `Inst`s.
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

        for (_block, block_data) in self.blocks.iter_mut() {
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
            }
        }

        let old_insts = mem::replace(&mut self.insts, new_insts);
        (old_to_new, old_insts)
    }

    /// Make sure that every block ends in a terminator instruction, and that
    /// they name valid blocks as their successors.
    fn ensure_terminators(&mut self, output: &mut OutputInner<u32>) {
        let num_blocks = self.blocks.len();
        assert!(num_blocks > 0);

        for (_block, block_data) in self.blocks.iter_mut() {
            match block_data.insts.last_mut() {
                Some(inst) => match &mut self.insts[*inst] {
                    inst_data @ InstData::Op { .. } => {
                        *inst_data = InstData::Branch {
                            args: vec![],
                            targets: vec![],
                        };
                    }
                    InstData::Branch { args, targets } => {
                        for target in targets {
                            target.target =
                                Block::try_new(target.target.index() % num_blocks).unwrap();
                        }
                    }
                },
                None => {
                    let inst = self
                        .insts
                        .push(
                            output,
                            InstData::Branch {
                                args: vec![],
                                targets: vec![],
                            },
                        )
                        .unwrap();
                    block_data.insts.push(inst);
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
                InstData::Branch { args: _, targets } => {
                    targets.push(BlockCall {
                        target: block,
                        args: vec![],
                    });
                }
            }
        }
    }

    fn fixup_dominator_tree(&mut self) {
        let mut dominators = mem::take(&mut self.dominators);
        dominators.compute(self);
        self.dominators = dominators;
    }

    fn ensure_values_in_bounds(&mut self, output: &mut OutputInner<u32>) {
        let num_vals = self.values.len();
        assert!(num_vals > 0);

        for (inst, inst_data) in self.insts.iter_mut() {
            match inst_data {
                InstData::Op {
                    args,
                    results,
                    side_effects: _,
                } => {
                    for arg in args {
                        arg.val = Val::try_new(arg.val.index() % num_vals).unwrap();
                    }
                    for arg in results {
                        arg.val = Val::try_new(arg.val.index() % num_vals).unwrap();
                    }
                }
                InstData::Branch { args, targets: _ } => {
                    for arg in args {
                        arg.val = Val::try_new(arg.val.index() % num_vals).unwrap();
                    }
                }
            }
        }
    }
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
    block: Block,
    idx: usize,
}

impl<'b> Iterator for TestInstsIter<'b> {
    type Item = (Inst, TestInst<'b>);

    fn next(&mut self) -> Option<Self::Item> {
        let insts = &self.func.blocks[self.block].insts;
        if self.idx < insts.len() {
            let inst = insts[self.idx];
            self.idx += 1;
            Some((
                inst,
                TestInst {
                    func: self.func,
                    inst,
                },
            ))
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.func.blocks[self.block].insts.len() - self.idx;
        (remaining, Some(remaining))
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
            block: self.block,
            idx: 0,
        }
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
        let inst = self.func.blocks[self.block].insts.last().unwrap();
        TestBlockSuccessorsIter {
            state: match &self.func.insts[*inst] {
                InstData::Op { .. } => panic!("invalid function; should have called `fixup`"),
                InstData::Branch { args, targets } => {
                    TestBlockSuccessorsIterState::Many(targets.iter())
                }
            },
        }
    }

    fn len_successor_block_args(&self, _i: usize) -> usize {
        todo!()
    }

    type SuccessorBlockArgsIter<'b>
        = core::iter::Empty<Val>
    where
        Self: 'b;

    fn successor_block_args(&self, _successor: usize) -> core::iter::Empty<Val> {
        todo!()
    }
}

pub struct TestBlockSuccessorsIter<'a> {
    state: TestBlockSuccessorsIterState<'a>,
}

enum TestBlockSuccessorsIterState<'a> {
    None,
    Many(core::slice::Iter<'a, BlockCall>),
}

impl Iterator for TestBlockSuccessorsIter<'_> {
    type Item = Block;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.state {
            TestBlockSuccessorsIterState::None => None,
            TestBlockSuccessorsIterState::Many(block_calls) => {
                let call = block_calls.next()?;
                Some(call.target)
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.state {
            TestBlockSuccessorsIterState::None => (0, Some(0)),
            TestBlockSuccessorsIterState::Many(iter) => iter.size_hint(),
        }
    }
}

impl ExactSizeIterator for TestBlockSuccessorsIter<'_> {}

impl<'a> InputInst<'a> for TestInst<'a> {
    fn operands_len(&self) -> usize {
        self.operands().len()
    }

    type OperandsIter<'b>
        = TestOperandsIter<'b>
    where
        Self: 'b;

    fn operands(&self) -> Self::OperandsIter<'_> {
        match &self.func.insts[self.inst] {
            InstData::Op {
                args,
                results,
                side_effects: _,
            } => TestOperandsIter {
                args: args.iter(),
                results: results.iter(),
            },
            InstData::Branch { args, targets: _ } => TestOperandsIter {
                args: args.iter(),
                results: (&[][..]).iter(),
            },
        }
    }

    fn operand(&self, i: usize) -> Operand {
        todo!()
    }

    fn clobbers(&self) -> crate::input::RegSet {
        todo!()
    }
}

pub struct TestOperandsIter<'a> {
    args: core::slice::Iter<'a, Operand>,
    results: core::slice::Iter<'a, Operand>,
}

impl Iterator for TestOperandsIter<'_> {
    type Item = Operand;

    fn next(&mut self) -> Option<Self::Item> {
        self.args.next().or_else(|| self.results.next()).cloned()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (args_min, args_max) = self.args.size_hint();
        let (results_min, results_max) = self.results.size_hint();
        (
            args_min + results_min,
            match (args_max, results_max) {
                (None, None) => None,
                (None, Some(_)) | (Some(_), None) => None,
                (Some(a), Some(b)) => Some(a + b),
            },
        )
    }
}

impl ExactSizeIterator for TestOperandsIter<'_> {}
