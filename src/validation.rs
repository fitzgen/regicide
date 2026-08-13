//! Validation of the input to register allocation.
//!
//! This checks everything that the rest of the allocator assumes about its
//! input:
//!
//! * entity references are in bounds,
//! * every block is reachable and terminated,
//! * the function is in valid SSA form,
//! * control-flow edges and block parameters agree, and
//! * the dominance relation the input reports really is the dominance relation
//!   of the control-flow graph it reports.

use crate::{
    dominators::DominatorTree,
    entity::{Block, Entity, EntityRepr, Inst, SecondaryMap, Val},
    error::{Error, IResult, Result},
    input::{DefUse, InputBlock, InputFunction, InputInst, Operand},
    output::OutputInner,
    timing::Timing,
};
use alloc::{vec, vec::Vec};

pub(crate) fn validate<E>(func: &impl InputFunction, output: &mut OutputInner<E>) -> IResult<()>
where
    E: EntityRepr,
{
    let _timing = Timing::new("validation");

    validate_entity_references(func, output)?;

    // Every check below this point indexes by entity, and computing the
    // dominator tree does too, so the bounds check has to come first. The
    // dominator tree is built from the input's predecessors, so those have to
    // be checked before it, rather than alongside the rest of the dominance
    // information below.
    validate_predecessors(func, output)?;

    let mut dominators = DominatorTree::new();
    dominators.compute(func);

    validate_reachability(func, &dominators, output)?;
    validate_block_args(func, output)?;
    validate_dominance(func, &dominators, output)?;

    let defs = validate_definitions(func, output)?;
    validate_uses(func, &dominators, &defs, output)?;

    Ok(())
}

/// Check that every entity reference in `func` is within the index space that
/// `func` declares, and that every `len_*` method agrees with the iterator it
/// describes.
///
/// Every other check indexes by entity, so this one has to come first.
fn validate_entity_references<E>(
    func: &impl InputFunction,
    output: &mut OutputInner<E>,
) -> IResult<()>
where
    E: EntityRepr,
{
    let num_blocks = func.len_blocks();
    let num_values = func.len_values();

    let entry = func.entry_block();
    if entry.index() >= num_blocks {
        return output.error(Error::BlockOutOfBounds { block: entry });
    }

    for (block, _) in func.blocks() {
        if block.index() >= num_blocks {
            return output.error(Error::BlockOutOfBounds { block });
        }

        let result = check_block_references(&func.block(block), block, num_blocks, num_values);
        if let Err(e) = result {
            return output.error(e);
        }
    }

    Ok(())
}

fn check_block_references<'a>(
    input_block: &impl InputBlock<'a>,
    block: Block,
    num_blocks: usize,
    num_values: usize,
) -> Result<()> {
    let mut num_params = 0;
    for param in input_block.params() {
        if param.index() >= num_values {
            return Err(Error::ValOutOfBounds { val: param });
        }
        num_params += 1;
    }
    if input_block.len_params() != num_params {
        return Err(Error::InconsistentLen {
            method: "len_params",
            block,
        });
    }

    for_each_operand(input_block, |_inst, _i, operand| {
        if operand.val.index() >= num_values {
            return Err(Error::ValOutOfBounds { val: operand.val });
        }
        Ok(())
    })?;

    let mut num_successors = 0;
    for successor in input_block.successors() {
        if successor.index() >= num_blocks {
            return Err(Error::BlockOutOfBounds { block: successor });
        }
        num_successors += 1;
    }
    if input_block.len_successors() != num_successors {
        return Err(Error::InconsistentLen {
            method: "len_successors",
            block,
        });
    }

    for i in 0..num_successors {
        let mut num_args = 0;
        for arg in input_block.successor_block_args(i) {
            if arg.index() >= num_values {
                return Err(Error::ValOutOfBounds { val: arg });
            }
            num_args += 1;
        }
        if input_block.len_successor_block_args(i) != num_args {
            return Err(Error::InconsistentLen {
                method: "len_successor_block_args",
                block,
            });
        }
    }

    Ok(())
}

/// Check that the predecessors the input reports are the exact reverse of the
/// successors it reports.
fn validate_predecessors<E>(func: &impl InputFunction, output: &mut OutputInner<E>) -> IResult<()>
where
    E: EntityRepr,
{
    // Every edge, as a `(from, to)` pair, collected once from each direction.
    // Comparing whole pairs rather than per-block counts is what catches an
    // edge whose endpoints have been swapped with another's.
    let mut forward = Vec::new();
    let mut backward = Vec::new();

    for (block, _) in func.blocks() {
        for successor in func.block(block).successors() {
            forward.push((block, successor));
        }

        let mut len = 0;
        for predecessor in func.block(block).predecessors() {
            backward.push((predecessor, block));
            len += 1;
        }
        if func.block(block).len_predecessors() != len {
            return output.error(Error::InconsistentLen {
                method: "len_predecessors",
                block,
            });
        }
    }

    forward.sort_unstable();
    backward.sort_unstable();

    // Blame the first edge that one direction has and the other does not, which
    // after sorting is the smaller of the two pairs at the first difference.
    for i in 0..forward.len().max(backward.len()) {
        let block = match (forward.get(i), backward.get(i)) {
            (Some(f), Some(b)) if f == b => continue,
            (Some(&(_, to)), None) => to,
            (None, Some(&(_, to))) => to,
            (Some(&f), Some(&b)) => core::cmp::min(f, b).1,
            (None, None) => unreachable!(),
        };
        return output.error(Error::InvalidPredecessors { block });
    }

    Ok(())
}

/// Check that every block is reachable from the entry block and ends in a
/// terminator.
///
/// Unreachable blocks are not in the dominator tree, they are never assigned to
/// a strongly-connected component, and their values have no meaningful live
/// ranges. Reject them up front so that we don't have to constantly
/// special-case unreachable blocks.
fn validate_reachability<E>(
    func: &impl InputFunction,
    dominators: &DominatorTree,
    output: &mut OutputInner<E>,
) -> IResult<()>
where
    E: EntityRepr,
{
    for (block, _) in func.blocks() {
        if !dominators.is_reachable(block) {
            return output.error(Error::UnreachableBlock { block });
        }
        if terminator(&func.block(block)).is_none() {
            return output.error(Error::BlockWithoutTerminator { block });
        }
    }

    Ok(())
}

/// Check that every control-flow edge passes exactly as many block arguments as
/// its target block has parameters.
fn validate_block_args<E>(func: &impl InputFunction, output: &mut OutputInner<E>) -> IResult<()>
where
    E: EntityRepr,
{
    for (block, _) in func.blocks() {
        for (i, successor) in func.block(block).successors().enumerate() {
            let expected = func.block(successor).len_params();
            let actual = func.block(block).len_successor_block_args(i);
            if expected != actual {
                return output.error(Error::BlockArgCountMismatch {
                    block,
                    successor: i,
                    expected,
                    actual,
                });
            }
        }
    }

    Ok(())
}

/// Check that the dominance information the input reports agrees with the
/// control-flow graph it reports.
fn validate_dominance<E>(
    func: &impl InputFunction,
    dominators: &DominatorTree,
    output: &mut OutputInner<E>,
) -> IResult<()>
where
    E: EntityRepr,
{
    for (block, _) in func.blocks() {
        if func.block(block).immediate_dominator() != dominators.idom(block) {
            return output.error(Error::InvalidImmediateDominator { block });
        }

        let mut check = |a: Block, b: Block| -> Result<()> {
            if func.block(a).dominates(b) == dominators.block_dominates(a, b) {
                Ok(())
            } else {
                Err(Error::InvalidDominance { a, b })
            }
        };

        let mut result = check(block, block);
        if let Some(idom) = dominators.idom(block) {
            result = result.and_then(|()| check(idom, block));
            result = result.and_then(|()| check(block, idom));
        }
        for successor in func.block(block).successors() {
            result = result.and_then(|()| check(block, successor));
            result = result.and_then(|()| check(successor, block));
        }
        if let Err(e) = result {
            return output.error(e);
        }
    }

    Ok(())
}

/// Check that every value is defined exactly once, and report where each one is
/// defined.
fn validate_definitions<E>(
    func: &impl InputFunction,
    output: &mut OutputInner<E>,
) -> IResult<SecondaryMap<Val, Option<ProgramPoint>>>
where
    E: EntityRepr,
{
    let mut defs = SecondaryMap::<Val, Option<_>>::new(None);

    for (block, _) in func.blocks() {
        let mut define = |val: Val, point: ProgramPoint| -> Result<()> {
            let slot = &mut defs[val];
            if slot.is_some() {
                return Err(Error::MultiplyDefinedValue { val });
            }
            *slot = Some(point);
            Ok(())
        };

        for param in func.block(block).params() {
            if let Err(e) = define(param, ProgramPoint::block_entry(block)) {
                return output.error(e);
            }
        }

        let result = for_each_operand(&func.block(block), |_inst, i, operand| match operand.kind {
            DefUse::Def => define(operand.val, ProgramPoint::inst(block, i)),
            DefUse::Use => Ok(()),
        });
        if let Err(e) = result {
            return output.error(e);
        }
    }

    for (val, def) in defs.iter() {
        if def.is_none() {
            return output.error(Error::UndefinedValue { val });
        }
    }

    Ok(defs)
}

/// Check that every use of a value is dominated by that value's definition.
fn validate_uses<E>(
    func: &impl InputFunction,
    dominators: &DominatorTree,
    defs: &SecondaryMap<Val, Option<ProgramPoint>>,
    output: &mut OutputInner<E>,
) -> IResult<()>
where
    E: EntityRepr,
{
    for (block, _) in func.blocks() {
        let result = for_each_operand(&func.block(block), |inst, i, operand| {
            if !matches!(operand.kind, DefUse::Use) {
                return Ok(());
            }
            let def = defs[operand.val].unwrap();
            let use_ = ProgramPoint::inst(block, i);
            if def.dominates(use_, dominators) {
                Ok(())
            } else {
                Err(Error::InvalidSsa {
                    val: operand.val,
                    inst,
                })
            }
        });
        if let Err(e) = result {
            return output.error(e);
        }

        let (terminator, num_insts) = terminator(&func.block(block)).unwrap();
        let use_ = ProgramPoint::inst(block, num_insts - 1);
        for i in 0..func.block(block).len_successors() {
            for arg in func.block(block).successor_block_args(i) {
                if !defs[arg].unwrap().dominates(use_, dominators) {
                    return output.error(Error::InvalidSsa {
                        val: arg,
                        inst: terminator,
                    });
                }
            }
        }
    }

    Ok(())
}

/// Call `f` on each operand of each instruction in `input_block`, along with
/// that instruction and its index within the block.
fn for_each_operand<'a>(
    input_block: &impl InputBlock<'a>,
    mut f: impl FnMut(Inst, usize, Operand) -> Result<()>,
) -> Result<()> {
    for (i, (inst, input_inst)) in input_block.insts().enumerate() {
        for operand in input_inst.operands() {
            f(inst, i, operand)?;
        }
    }
    Ok(())
}

/// Get `input_block`'s terminator and its number of instructions, or `None` if
/// the block has no instructions at all.
fn terminator<'a>(input_block: &impl InputBlock<'a>) -> Option<(Inst, usize)> {
    let mut last = None;
    let mut count = 0;
    for (inst, _input_inst) in input_block.insts() {
        last = Some(inst);
        count += 1;
    }
    last.map(|inst| (inst, count))
}

/// A point in a function: a position within a block, where `0` is the block's
/// parameter list and `i + 1` is its `i`th instruction.
#[derive(Clone, Copy, PartialEq, Eq)]
struct ProgramPoint {
    block: Block,
    position: usize,
}

impl ProgramPoint {
    /// The point at which a block's parameters are defined, before any of its
    /// instructions.
    fn block_entry(block: Block) -> Self {
        Self { block, position: 0 }
    }

    /// The point at which a block's `i`th instruction runs.
    fn inst(block: Block, i: usize) -> Self {
        Self {
            block,
            position: i + 1,
        }
    }

    /// Does a definition at `self` dominate a use at `other`?
    fn dominates(&self, other: Self, dominators: &DominatorTree) -> bool {
        if self.block == other.block {
            self.position < other.position
        } else {
            dominators.block_dominates(self.block, other.block)
        }
    }
}
