//! Test utilities.

#![allow(missing_docs)]

use crate::{
    Block, Function, Operand, Val,
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
    If {
        condition: Operand,
        then_target: BlockCall,
        else_target: BlockCall,
    },
    IndirectBr {
        condition: Operand,
        targets: Vec<BlockCall>,
    },
    Return {
        results: Vec<Operand>,
    },
}

pub enum ValData {
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
    pub params: Vec<Type>,
    pub insts: Vec<Inst>,
}

pub struct TestFunction {
    values: PrimaryMap<Val, ValData>,
    blocks: PrimaryMap<Block, BlockData>,
    insts: PrimaryMap<Inst, InstData>,
}

impl Function for TestFunction {
    fn len_values(&self) -> usize {
        self.values.len()
    }

    fn remat_cost(&self, val: Val) -> Option<crate::RematCost> {
        None
    }

    fn len_blocks(&self) -> usize {
        self.blocks.len()
    }

    type BlocksIter<'a>
        = crate::entity::PrimaryMapKeys<'a, Block>
    where
        Self: 'a;

    fn blocks(&self) -> Self::BlocksIter<'_> {
        self.blocks.keys()
    }

    fn block_insts_len(&self, block: Block) -> usize {
        self.blocks[block].insts.len()
    }

    type BlockInstsIter<'a>
        = core::iter::Copied<core::slice::Iter<'a, Inst>>
    where
        Self: 'a;

    fn block_insts(&self, block: Block) -> Self::BlockInstsIter<'_> {
        self.blocks[block].insts.iter().copied()
    }
}
