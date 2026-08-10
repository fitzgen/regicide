//! Test utilities.

#![allow(missing_docs)]

use crate::{
    Block, InputBlock, InputFunction, InputInst, Operand, Val,
    entity::{Inst, PrimaryMap},
};
use alloc::vec::Vec;

pub struct BlockCall {
    target: Block,
    args: Vec<Val>,
}

pub enum InstData {
    Op {
        results: Vec<Operand>,
        args: Vec<Operand>,
        side_effects: bool,
    },
    Jump {
        target: BlockCall,
    },
    ConditionalBr {
        condition: Operand,
        targets: Vec<BlockCall>,
    },
    Return {
        results: Vec<Operand>,
    },
}

pub struct ValData {
    ty: Type,
    def: ValDef,
}

pub enum ValDef {
    InstResult { inst: Inst, i: usize },
    BlockParam { block: Block, i: usize },
}

pub enum Type {
    I32,
    I64,
    F32,
    F64,
    V128,
    V256,
}

pub struct BlockData {
    pub params: Vec<Val>,
    pub insts: Vec<Inst>,
}

pub struct TestFunction {
    values: PrimaryMap<Val, ValData>,
    blocks: PrimaryMap<Block, BlockData>,
    insts: PrimaryMap<Inst, InstData>,
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
    keys: crate::entity::PrimaryMapKeys<'a, Block>,
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
        todo!()
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
        todo!()
    }

    fn dominates(&self, _other: Block) -> bool {
        todo!()
    }

    fn len_successors(&self) -> usize {
        todo!()
    }

    type SuccessorsIter<'b>
        = core::iter::Empty<Block>
    where
        Self: 'b;

    fn successors(&self) -> core::iter::Empty<Block> {
        todo!()
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

impl<'a> InputInst<'a> for TestInst<'a> {}
