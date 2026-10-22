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
//!   value it is named for,
//! * every value the input says may be rematerialized really can be, and
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
    live_ranges::{MAX_INST_INDEX, MAX_OPERANDS_PER_INST, fixed_operand_of},
    machine::{Machine, Reg, RegUnit},
    output::{OutputInner, RegAllocation},
    timing::Timing,
};
use alloc::vec::Vec;
use core::ops::Range;

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

    validate_entity_references(
        func,
        input.machine.num_user_classes(),
        input.machine.num_registers(),
        output,
    )?;

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
    validate_remat_costs(input, output)?;
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
    num_registers: usize,
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
            num_registers,
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
    num_registers: usize,
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
        if let Some(val) = operand.val() {
            if val.index() >= num_values {
                return Err(Error::ValOutOfBounds { val });
            }
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

        // The checks below index tables by a clobbered register.
        for reg in input_inst.clobbers().iter() {
            if reg.index() >= num_registers {
                return Err(Error::RegOutOfBounds { inst, reg });
            }
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
        let (_, previous_last, previous_block) = pair[0];
        let (first, _, block) = pair[1];
        if first <= previous_last {
            return output.error(Error::InstInMultipleBlocks { inst: first });
        }

        // Several passes take the blocks a program point range covers to be the
        // block index range between its ends, which holds only while the two
        // orders agree. `LiveSpan::blocks` is the one that reads it most.
        if block <= previous_block {
            return output.error(Error::BlocksOutOfLayoutOrder { block });
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
/// Unreachable blocks are not in the dominator tree, the region tree has
/// nothing meaningful to say about where they belong, and their values have no
/// meaningful live ranges. Reject them up front so that we don't have to
/// constantly special-case unreachable blocks.
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
    for (val, input_val) in func.values() {
        if !input_val.reg_class().has_an_allocatable_member(machine) {
            return output.error(Error::NonAllocatableRegInValClass { val });
        }
    }

    // Reused by the per-instruction check, so it allocates once per function.
    let mut scratch = FixedOperandScratch::default();

    for (block, _) in func.blocks() {
        if let Err(e) =
            check_block_reg_classes(func, machine, &mut scratch, &func.block(block), block)
        {
            return output.error(e);
        }
    }

    Ok(())
}

fn check_block_reg_classes<'a>(
    func: &impl InputFunction,
    machine: &Machine,
    scratch: &mut FixedOperandScratch,
    input_block: &impl InputBlock<'a>,
    block: Block,
) -> Result<()> {
    let class_of = |val: Val| func.value(val).reg_class();

    for (inst, input_inst) in input_block.insts() {
        for (i, operand) in input_inst.operands().enumerate() {
            // A class holding nothing but registers the allocator does not
            // own is how an operand names one of them, and an operand names
            // one exactly when it names no value: there is nothing there for
            // the allocator to place, so what the register holds is the
            // client's own business. See
            // `MachineBuilder::define_non_allocatable_reg`.
            let pinned = match operand.constraint() {
                OperandConstraint::Reg(class) => !class.has_an_allocatable_member(machine),
                _ => false,
            };

            // Naming no value any other way asks the allocator to choose a
            // home for something that does not exist.
            let Some(val) = operand.val() else {
                if operand.kind() != DefUse::Use || !pinned {
                    return Err(Error::OperandWithoutValIsNotAFixedUse { inst, operand: i });
                }
                continue;
            };

            // And the converse: a value pinned there has nowhere to go that
            // the allocator may give it. Diagnosed ahead of the class rules
            // below, which it also breaks, because this is the more specific
            // thing to say about it.
            if pinned {
                return Err(Error::OperandWithValInNonAllocatableRegClass { inst, operand: i });
            }

            match operand.constraint() {
                OperandConstraint::Reg(class) => {
                    // The register class we are constraining a value to must
                    // be a subset of the value's register class.
                    if class.intersect(machine, class_of(val)) != Some(class) {
                        return Err(Error::IncompatibleRegClass { inst, operand: i });
                    }
                }

                // `validate_entity_references` has already shown that `target`
                // names a real operand of this instruction.
                OperandConstraint::Reuse(target) => {
                    // A reuse is defined in the register its target reads its
                    // value from, so a target that reads no value leaves the
                    // definition tied to nothing.
                    let Some(target) = input_inst.operand(target).val() else {
                        return Err(Error::ReuseOfOperandWithoutVal { inst, operand: i });
                    };
                    if class_of(val) != class_of(target) {
                        return Err(Error::ReuseRegClassMismatch { inst, operand: i });
                    }
                }

                OperandConstraint::Any | OperandConstraint::Stack => {}
            }
        }

        check_inst_fixed_operands(func, machine, scratch, inst, input_inst.operands_len())?;
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

/// Check that no two of an instruction's fixed operands, and no fixed operand
/// and clobber of it, want the same register at the same time.
pub(crate) fn check_inst_fixed_operands(
    func: &impl InputFunction,
    machine: &Machine,
    scratch: &mut FixedOperandScratch,
    inst: Inst,
    num_operands: usize,
) -> Result<()> {
    let FixedOperandScratch { claims, holds } = scratch;
    claims.clear();
    holds.clear();

    // One hold per (claim, register, half). Two claims want the same register
    // at the same time exactly when two holds overlap.
    let push_claim = |claims: &mut Vec<(Option<usize>, FixedClaim)>,
                      holds: &mut Vec<Hold>,
                      operand: Option<usize>,
                      claim: FixedClaim| {
        let index = claims.len();
        for units in claim.reg().units(machine) {
            // A non-allocatable register covers no units, and so holds
            // nothing anything else could contend for.
            if units.start >= units.end {
                continue;
            }
            for half in [Position::Early, Position::Late] {
                if claim.covers(half) {
                    holds.push(Hold {
                        half,
                        units: units.clone(),
                        claim: index,
                    });
                }
            }
        }
        claims.push((operand, claim));
    };

    for operand in 0..num_operands {
        let Some(claim) = FixedClaim::of(func, machine, inst, operand) else {
            continue;
        };
        push_claim(claims, holds, Some(operand), claim);
    }

    // And one claim per clobbered register, on the late half.
    for reg in func.inst(inst).clobbers().iter() {
        push_claim(claims, holds, None, FixedClaim::of_clobber(reg));
    }

    // Sorted, so that the scan below is linear: overlapping holds are adjacent
    // once the ones that ended are dropped.
    holds.sort_unstable_by_key(|h| (h.half, h.units.start));

    // The hold the scan is inside of: the end of its units and the claim that
    // owns it. One is enough, since overlapping holds that do not conflict
    // cover the very same units, and so are indistinguishable here.
    let mut open: Option<(Position, RegUnit, usize)> = None;

    for hold in holds.iter() {
        if let Some((half, end, claim)) = open
            && half == hold.half
            && hold.units.start < end
        {
            if claim != hold.claim {
                let (i, this) = claims[hold.claim];
                let (j, other) = claims[claim];
                if this.conflicts_with(machine, &other) {
                    return Err(match (i, j) {
                        (Some(i), Some(j)) => Error::ConflictingFixedOperands {
                            inst,
                            operand: i.max(j),
                            conflicts_with: i.min(j),
                        },
                        // A clobber has no operand index of its own, so name
                        // the operand it collides with.
                        (Some(operand), None) => Error::ConflictingClobber {
                            inst,
                            operand,
                            reg: clobbered_reg(other),
                        },
                        (None, Some(operand)) => Error::ConflictingClobber {
                            inst,
                            operand,
                            reg: clobbered_reg(this),
                        },
                        // Two clobbers of one register agree, but two that
                        // merely share a unit each want a reservation over
                        // that unit's late half, and those may not overlap.
                        (None, None) => {
                            let (a, b) = (clobbered_reg(this), clobbered_reg(other));
                            Error::ConflictingClobbers {
                                inst,
                                reg: a.max(b),
                                conflicts_with: a.min(b),
                            }
                        }
                    });
                }
            }
            // Keep the earlier operand, the one worth naming.
            open = Some((half, end.max(hold.units.end), claim.min(hold.claim)));
        } else {
            open = Some((hold.half, hold.units.end, hold.claim));
        }
    }

    Ok(())
}

/// The register a clobber claim names, for the error naming it.
///
/// Every clobber claim comes from `FixedClaim::of_clobber`, which names a
/// single register; only a fixed operand can name a group.
fn clobbered_reg(clobber: FixedClaim) -> Reg {
    match clobber.reg() {
        RegAllocation::Reg(reg) => reg,
        RegAllocation::RegGroup(_) => unreachable!("a clobber names a single register"),
    }
}

/// Scratch for `check_inst_fixed_operands`, reused across instructions.
#[derive(Default)]
pub(crate) struct FixedOperandScratch {
    /// The instruction's claims: its fixed operands in operand order, each
    /// with its index, then its clobbers, which have no index.
    claims: Vec<(Option<usize>, FixedClaim)>,

    /// One entry per claim, register of that claim, and half the claim covers.
    holds: Vec<Hold>,
}

/// One claim's hold on the units of one of the registers it names, over one
/// half of the instruction.
struct Hold {
    /// The half held, and the first part of the sort key.
    half: Position,

    /// The units held, which are the units of one register.
    units: Range<RegUnit>,

    /// The index in `FixedOperandScratch::claims` of the claim holding them.
    claim: usize,
}

/// One claim on a register: either a fixed operand's, or a clobber's.
#[derive(Clone, Copy)]
struct FixedClaim {
    /// The register, or register group, claimed.
    reg: RegAllocation,

    /// The value read out of, or written into, it. `None` for a clobber.
    val: Option<Val>,

    /// Whether the claim covers the instruction's early half.
    early: bool,

    /// Whether it covers the late half.
    late: bool,
}

impl FixedClaim {
    /// The claim `operand` makes, or `None` when it is not a fixed operand.
    fn of(
        func: &impl InputFunction,
        machine: &Machine,
        inst: Inst,
        operand: usize,
    ) -> Option<Self> {
        let fixed = fixed_operand_of(func, machine, inst, operand)?;

        // Asked of `FixedOperand`, so the halves checked here are exactly the
        // ones `collect_block_reservations` would hold.
        Some(FixedClaim {
            reg: fixed.reg,
            val: Some(fixed.val),
            early: fixed.holds(inst, Position::Early),
            late: fixed.holds(inst, Position::Late),
        })
    }

    /// The claim a clobber of `reg` makes, matching the hold
    /// `collect_block_reservations` gives it.
    fn of_clobber(reg: Reg) -> Self {
        FixedClaim {
            reg: RegAllocation::Reg(reg),
            val: None,
            early: false,
            late: true,
        }
    }

    /// Does this claim cover `half` of the instruction?
    fn covers(&self, half: Position) -> bool {
        match half {
            Position::Early => self.early,
            Position::Late => self.late,
        }
    }

    /// The register, or register group, this claim names.
    fn reg(&self) -> RegAllocation {
        self.reg
    }

    /// The value it reads out of, or writes into, that register. `None` for a
    /// clobber.
    fn val(&self) -> Option<Val> {
        self.val
    }

    /// Do these two claims want the same register at the same time?
    fn conflicts_with(&self, machine: &Machine, other: &Self) -> bool {
        // Different halves, so no contest: a late definition may take the
        // register an early read consumed.
        if !((self.early && other.early) || (self.late && other.late)) {
            return false;
        }

        // Two claims on one register for one value agree rather than compete;
        // `collect_block_reservations` folds them into one hold. So do two
        // clobbers of one register, the `None == None` case: destroying it
        // twice asks no more than destroying it once.
        if self.reg() == other.reg() && self.val() == other.val() {
            return false;
        }

        // Compared unit by unit, since two registers that are not equal may
        // still overlap: a register group and one of its members, say.
        self.reg().units(machine).any(|a| {
            other
                .reg()
                .units(machine)
                .any(|b| a.start < b.end && b.start < a.end)
        })
    }
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

/// Check that every value the input says may be rematerialized really can be.
fn validate_remat_costs<E>(
    input: &Input<'_, impl InputFunction>,
    output: &mut OutputInner<E>,
) -> IResult<()>
where
    E: EntityRepr,
{
    let func = input.func;

    for (val, input_val) in func.values() {
        if input_val.remat_cost().is_none() {
            continue;
        }
        if input_val.reg_class().group_size(input.machine).unwrap_or(1) != 1 {
            return output.error(Error::RematOfRegGroup { val });
        }
    }

    for (block, _) in func.blocks() {
        let result = check_block_remat_costs(func, &func.block(block));
        if let Err(e) = result {
            return output.error(e);
        }
    }

    Ok(())
}

fn check_block_remat_costs<'a>(
    func: &impl InputFunction,
    input_block: &impl InputBlock<'a>,
) -> Result<()> {
    for param in input_block.params() {
        if func.value(param).remat_cost().is_some() {
            return Err(Error::RematOfDerivedValue {
                val: param,
                def: None,
            });
        }
    }

    for (inst, input_inst) in input_block.insts() {
        if !input_inst.operands().any(|op| op.kind() == DefUse::Use) {
            continue;
        }
        for op in input_inst.operands() {
            // An operand naming no value defines nothing.
            let (DefUse::Def, Some(val)) = (op.kind(), op.val()) else {
                continue;
            };
            if func.value(val).remat_cost().is_some() {
                return Err(Error::RematOfDerivedValue {
                    val,
                    def: Some(inst),
                });
            }
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
            match (operand.kind(), operand.val()) {
                (DefUse::Def, Some(val)) => define(val, ProgramPoint::inst(block, i)),
                // An operand naming no value defines nothing.
                (DefUse::Def, None) | (DefUse::Use, _) => Ok(()),
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
            // An operand naming no value reads nothing that has to be in
            // scope here.
            let Some(val) = operand.val() else {
                return Ok(());
            };
            let def = defs[val].unwrap();
            let use_ = ProgramPoint::inst(block, i);
            if def.dominates(use_, dominators) {
                Ok(())
            } else {
                Err(Error::InvalidSsa { val, inst })
            }
        });
        if let Err(e) = result {
            return output.error(e);
        }

        // A block argument is read as control leaves the block, not at the
        // terminator, so a terminator may pass a value it defines itself along
        // its own out-edge. That is, e.g., Cranelift's `try_call`'s shape.
        //
        // `validate_insts` has already checked that every block has at least
        // one instruction.
        let (terminator, num_insts) = terminator(&func.block(block)).unwrap();
        let use_ = ProgramPoint::block_exit(block, num_insts);
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

    /// The point at which control leaves a block of `num_insts` instructions,
    /// after every one of them has run.
    ///
    /// This is where the block's outgoing arguments are read, so a value the
    /// terminator itself defines is in scope here.
    fn block_exit(block: Block, num_insts: usize) -> Self {
        Self {
            block,
            position: num_insts + 1,
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
