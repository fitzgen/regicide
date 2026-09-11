//! Validation of the input to register allocation.
//!
//! This checks everything that the rest of the allocator assumes about its
//! input:
//!
//! * entity references are in bounds,
//! * every block is reachable and terminated,
//! * the function is in valid SSA form,
//! * control-flow edges and block parameters agree,
//! * every register class named is one the machine defines, and can hold the
//!   value it is named for, and
//! * the dominance relation the input reports really is the dominance relation
//!   of the control-flow graph it reports.

use crate::{
    dominators::DominatorTree,
    entity::{Block, Entity, EntityRepr, Inst, SecondaryMap, Val},
    error::{Error, IResult, Result},
    input::{
        DefUse, Input, InputBlock, InputFunction, InputInst, InputValue, Operand,
        OperandConstraint, Position,
    },
    live_ranges::{MAX_INST_INDEX, MAX_OPERANDS_PER_INST},
    machine::Machine,
    output::OutputInner,
    timing::Timing,
};
use alloc::vec::Vec;

pub(crate) fn validate<E>(
    input: &Input<'_, impl InputFunction>,
    output: &mut OutputInner<E>,
) -> IResult<()>
where
    E: EntityRepr,
{
    let _timing = Timing::new("validation");

    let func = input.func;

    // Nothing here indexes by entity, and everything below assumes that a block
    // has a terminator to look at, so this goes first.
    validate_insts(func, output)?;

    validate_entity_references(func, input.machine.num_user_classes(), output)?;

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
    validate_reg_classes(func, input.machine, output)?;
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
    num_classes: usize,
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

    let mut num_values_seen = 0;
    for (val, input_val) in func.values() {
        if val.index() >= num_values {
            return output.error(Error::ValOutOfBounds { val });
        }
        num_values_seen += 1;

        // A value's class is intersected with its operands' classes through a
        // table indexed by class, so an undefined class would be an
        // out-of-bounds index rather than a diagnosis.
        if input_val.reg_class().index() >= num_classes {
            return output.error(Error::InvalidValRegClass { val });
        }

        // The allocator reaches a value both by iterating over the function's
        // values and by looking one up by index, so the two have to describe
        // the same value.
        let looked_up = func.value(val);
        if input_val.val() != val
            || looked_up.val() != val
            || looked_up.reg_class() != input_val.reg_class()
            || looked_up.remat_cost() != input_val.remat_cost()
        {
            return output.error(Error::InconsistentVal { val });
        }
    }
    if num_values_seen != num_values {
        return output.error(Error::InconsistentLen {
            method: "len_values",
            block: None,
        });
    }

    for (block, _) in func.blocks() {
        if block.index() >= num_blocks {
            return output.error(Error::BlockOutOfBounds { block });
        }

        let result = check_block_references(
            &func.block(block),
            block,
            num_blocks,
            num_values,
            num_classes,
        );
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
    num_classes: usize,
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
            block: Some(block),
        });
    }

    for_each_operand(input_block, |_inst, _i, operand| {
        if operand.val().index() >= num_values {
            return Err(Error::ValOutOfBounds { val: operand.val() });
        }
        Ok(())
    })?;

    // Live range construction indexes an instruction's operands with a `u16`,
    // so an instruction may not have more operands than that can address.
    //
    // Count the operands actually yielded rather than trusting
    // `operands_len`, since it is the yielded ones that get indexed; check the
    // two agree while we are here, as we do for every other length.
    for (inst, input_inst) in input_block.insts() {
        let mut num_operands = 0;
        for _ in input_inst.operands() {
            num_operands += 1;
            if num_operands > MAX_OPERANDS_PER_INST {
                return Err(Error::TooManyOperands { inst });
            }
        }
        if input_inst.operands_len() != num_operands {
            return Err(Error::InconsistentLen {
                method: "operands_len",
                block: Some(block),
            });
        }

        for (i, operand) in input_inst.operands().enumerate() {
            match operand.constraint() {
                // A `Reuse` ties a late definition to an early use of the same
                // instruction: anywhere else it names two things live at once.
                // The target, being a use, never carries a `Reuse` itself.
                OperandConstraint::Reuse(target) => {
                    let reusing_is_late_def =
                        operand.kind() == DefUse::Def && operand.pos() == Position::Late;
                    if !reusing_is_late_def || target >= num_operands {
                        return Err(Error::InvalidReuse { inst, operand: i });
                    }
                    let target_operand = input_inst.operand(target);
                    let target_is_early_use = target_operand.kind() == DefUse::Use
                        && target_operand.pos() == Position::Early;
                    if !target_is_early_use {
                        return Err(Error::InvalidReuse { inst, operand: i });
                    }
                    // The pair share a location, and only a register can be
                    // shared: each value has its own stack home.
                    if target_operand.constraint() == OperandConstraint::Stack {
                        return Err(Error::InvalidReuse { inst, operand: i });
                    }
                    // One target, one reuse: two definitions sharing the
                    // use's location would overwrite one another.
                    let claimed = input_inst
                        .operands()
                        .take(i)
                        .any(|other| other.constraint() == OperandConstraint::Reuse(target));
                    if claimed {
                        return Err(Error::InvalidReuse { inst, operand: i });
                    }
                }

                // A `Reg` must name a class this machine defines. Merging
                // constraints intersects their classes through a table indexed
                // by class, so an undefined class would be an out-of-bounds
                // index rather than a diagnosis.
                OperandConstraint::Reg(class) if class.index() >= num_classes => {
                    return Err(Error::InvalidRegClass { inst, operand: i });
                }

                OperandConstraint::Any | OperandConstraint::Reg(_) | OperandConstraint::Stack => {}
            }
        }
    }

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
            block: Some(block),
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
                block: Some(block),
            });
        }
    }

    Ok(())
}

/// Check that every block has at least one instruction, that each block's
/// instructions are numbered contiguously, that no instruction appears in more
/// than one block, and that no instruction index is out of range.
///
/// Together these make each block's instructions a run, and the runs a
/// partition of `0..func.len_insts()`, which is what makes
/// [`InputFunction::inst`] well-defined at every index it accepts. Since this
/// is the pass that walks every instruction of every block, it is also where
/// each instruction is checked against the block it says it lies within.
fn validate_insts<E>(func: &impl InputFunction, output: &mut OutputInner<E>) -> IResult<()>
where
    E: EntityRepr,
{
    // The first and last instruction of each block.
    let mut runs = Vec::new();

    for (block, _) in func.blocks() {
        match inst_run(func, &func.block(block), block) {
            Ok(Some(run)) => {
                // A block's instructions are contiguous and ascending, so its
                // last one has the largest index in the block. Checking it here
                // is what lets `LivePoint::new` pack an index and a position
                // together without a fallible conversion.
                if run.1.index() >= MAX_INST_INDEX {
                    return output.error(Error::TooManyInsts { inst: run.1 });
                }
                runs.push((run.0, run.1, block));
            }
            // A block with no instructions has no terminator, and so no way to
            // leave it.
            Ok(None) => return output.error(Error::BlockWithoutTerminator { block }),
            Err(e) => return output.error(e),
        }
    }

    // After sorting, any overlap at all implies an overlap between neighbours:
    // if `a` and `b` overlap and `a` sorts first, then whatever sorts
    // immediately after `a` starts within `a` too.
    runs.sort_unstable();
    for pair in runs.windows(2) {
        let (_, previous_last, _) = pair[0];
        let (first, _, _) = pair[1];
        if first <= previous_last {
            return output.error(Error::InstInMultipleBlocks { inst: first });
        }
    }

    // The runs are now known to be sorted, disjoint, and within
    // `0..func.len_insts()`, so the only way left for them to miss part of that
    // index space is a gap between two of them, or after the last one. Every
    // index in the space must belong to some block, since that is the block
    // that `InputInst::block` has to name and the block whose instruction list
    // every pass walks to reach the instruction.
    //
    // Every index reported below is at most one past an instruction that some
    // block reports, and every one of those is below `MAX_INST_INDEX`, so the
    // conversions cannot fail.
    let mut next = 0;
    for &(first, last, _) in &runs {
        if first.index() > next {
            return output.error(Error::InstInNoBlock {
                inst: Inst::try_new(next).unwrap(),
            });
        }
        next = last.index() + 1;
    }
    if next < func.len_insts() {
        return output.error(Error::InstInNoBlock {
            inst: Inst::try_new(next).unwrap(),
        });
    }

    Ok(())
}

/// Get the first and last instruction of `input_block`, or `None` if it has no
/// instructions.
///
/// This is the only walk over every instruction of every block, so it also
/// checks each one as it goes: that the block's instructions are numbered
/// contiguously, that each of them is an instruction the function declares, and
/// that the two ways of reaching an instruction agree about which block it lies
/// within and about what it is.
fn inst_run<'a>(
    func: &impl InputFunction,
    input_block: &impl InputBlock<'a>,
    block: Block,
) -> Result<Option<(Inst, Inst)>, Error> {
    let mut first = None;
    let mut previous: Option<Inst> = None;

    for (inst, input_inst) in input_block.insts() {
        match previous {
            None => first = Some(inst),
            Some(previous) if inst.index() != previous.index() + 1 => {
                return Err(Error::NonContiguousInsts { block, inst });
            }
            Some(_) => {}
        }
        previous = Some(inst);

        // Looking an instruction up is only defined within the index space that
        // the function declares, so this bounds check comes before the lookup
        // below.
        if inst.index() >= func.len_insts() {
            return Err(Error::InstOutOfBounds { inst });
        }

        if input_inst.block() != block {
            return Err(Error::InvalidInstBlock {
                inst,
                block: input_inst.block(),
            });
        }

        // The allocator reaches an instruction both by walking its block and by
        // looking it up by index, so the two have to describe the same
        // instruction.
        let looked_up = func.inst(inst);
        if looked_up.block() != block
            || looked_up.operands_len() != input_inst.operands_len()
            || looked_up.operands().ne(input_inst.operands())
        {
            return Err(Error::InconsistentInst { inst });
        }
    }

    Ok(first.map(|first| (first, previous.unwrap())))
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
                block: Some(block),
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

/// Check that every block is reachable from the entry block.
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
        if !block.is_reachable(dominators) {
            return output.error(Error::UnreachableBlock { block });
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

/// Check that every register class the input names can actually hold the value
/// it is named for, and that values the input pins to a single location agree
/// about which class they may live in.
fn validate_reg_classes<E>(
    func: &impl InputFunction,
    machine: &Machine,
    output: &mut OutputInner<E>,
) -> IResult<()>
where
    E: EntityRepr,
{
    for (block, _) in func.blocks() {
        if let Err(e) = check_block_reg_classes(func, machine, &func.block(block), block) {
            return output.error(e);
        }
    }

    Ok(())
}

fn check_block_reg_classes<'a>(
    func: &impl InputFunction,
    machine: &Machine,
    input_block: &impl InputBlock<'a>,
    block: Block,
) -> Result<()> {
    let class_of = |val: Val| func.value(val).reg_class();

    for (inst, input_inst) in input_block.insts() {
        for (i, operand) in input_inst.operands().enumerate() {
            match operand.constraint() {
                // The register class we are constraining a value to must be a
                // subset of the value's register class.
                OperandConstraint::Reg(class) => {
                    if class.intersect(machine, class_of(operand.val())) != Some(class) {
                        return Err(Error::IncompatibleRegClass { inst, operand: i });
                    }
                }

                // `validate_entity_references` has already shown that `target`
                // names a real operand of this instruction.
                OperandConstraint::Reuse(target) => {
                    let target = input_inst.operand(target);
                    if class_of(operand.val()) != class_of(target.val()) {
                        return Err(Error::ReuseRegClassMismatch { inst, operand: i });
                    }
                }

                OperandConstraint::Any | OperandConstraint::Stack => {}
            }
        }
    }

    for (i, successor) in input_block.successors().enumerate() {
        let params = func.block(successor);
        let args = input_block.successor_block_args(i);
        for (index, (arg, param)) in args.zip(params.params()).enumerate() {
            if class_of(arg) != class_of(param) {
                return Err(Error::BlockArgRegClassMismatch {
                    block,
                    successor: i,
                    index,
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
        if func.block(block).immediate_dominator() != block.idom(dominators) {
            return output.error(Error::InvalidImmediateDominator { block });
        }

        let check = |a: Block, b: Block| -> Result<()> {
            if func.block(a).dominates(b) == a.dominates(dominators, b) {
                Ok(())
            } else {
                Err(Error::InvalidDominance { a, b })
            }
        };

        let mut result = check(block, block);
        if let Some(idom) = block.idom(dominators) {
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

        let result = for_each_operand(&func.block(block), |_inst, i, operand| {
            match operand.kind() {
                DefUse::Def => define(operand.val(), ProgramPoint::inst(block, i)),
                DefUse::Use => Ok(()),
            }
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
            if operand.kind() != DefUse::Use {
                return Ok(());
            }
            let def = defs[operand.val()].unwrap();
            let use_ = ProgramPoint::inst(block, i);
            if def.dominates(use_, dominators) {
                Ok(())
            } else {
                Err(Error::InvalidSsa {
                    val: operand.val(),
                    inst,
                })
            }
        });
        if let Err(e) = result {
            return output.error(e);
        }

        // `validate_insts` has already checked that every block has at least
        // one instruction.
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
            self.block.dominates(dominators, other.block)
        }
    }
}
