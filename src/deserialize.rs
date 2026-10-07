//! Deserializing a register allocation problem.
//!
//! See the [`serialize`][crate::serialize] module for details on serializing
//! register allocation inputs.
//!
//! # Encoding Format Stability
//!
//! The encoding is **not stable** and is liable to change across minor and
//! patch version bumps.
//!
//! # Example
//!
//! ```
//! # fn _foo() -> Result<(), Box<dyn std::error::Error>> {
//! use regicide::deserialize::DeserializedInput;
//!
//! // You can use whatever encoding format you like; for example, JSON.
//! # let read_json_string_from_disk = || -> String { unimplemented!() };
//! let json = read_json_string_from_disk();
//! let input: DeserializedInput = serde_json::from_str(&json)?;
//!
//! // Alternatively, you can use `postcard`'s binary encoding.
//! # let read_postcard_bytes_from_disk = || -> Vec<u8> { unimplemented!() };
//! let bytes = read_postcard_bytes_from_disk();
//! let input: DeserializedInput = postcard::from_bytes(&bytes)?;
//! # let _ = input;
//! # Ok(())
//! # }
//! ```

use crate::{
    Block, BlockFrequency, ENCODING_FORMAT_VERSION, Entity, Error, Input, InputBlock,
    InputFunction, InputInst, InputOptions, InputValue, Inst, Machine, MachineBuilder, Operand,
    OperandConstraint, Reg, RegBank, RegClass, RegGroup, RegSet, RegUnit, RematCost, Result,
    SpillSlotSize, Val,
    dominators::DominatorTree,
    entity::{PrimaryMap, PrimaryMapKeys},
};
use alloc::vec::Vec;
use core::{fmt, iter, mem, slice};
use serde::{
    Deserialize, Deserializer,
    de::{self},
};

#[derive(Deserialize)]
#[serde(rename = "Machine", deny_unknown_fields)]
struct WireMachine {
    version: u32,
    banks: Vec<WireBank>,
    registers: Vec<WireRegister>,
    groups: Vec<WireGroup>,
    classes: Vec<WireClass>,
}

#[derive(Deserialize)]
#[serde(rename = "Bank", deny_unknown_fields)]
struct WireBank {
    size: u16,
}

#[derive(Deserialize)]
#[serde(rename = "Register", deny_unknown_fields)]
struct WireRegister {
    bank: RegBank,
    units: Option<WireUnitRange>,
}

#[derive(Deserialize)]
#[serde(rename = "UnitRange", deny_unknown_fields)]
struct WireUnitRange {
    start: RegUnit,
    end: RegUnit,
}

#[derive(Deserialize)]
#[serde(rename = "Group", deny_unknown_fields)]
struct WireGroup {
    bank: RegBank,
    members: Vec<Reg>,
}

#[derive(Deserialize)]
#[serde(rename = "Class", deny_unknown_fields)]
struct WireClass {
    bank: RegBank,
    spill_cost: f32,
    members: WireClassMembers,
}

#[derive(Deserialize)]
#[serde(rename = "ClassMembers", rename_all = "lowercase", deny_unknown_fields)]
enum WireClassMembers {
    Regs(Vec<Reg>),
    Groups(Vec<RegGroup>),
}

impl<'de> Deserialize<'de> for Machine {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        WireMachine::deserialize(deserializer)?.build()
    }
}

impl WireMachine {
    /// Replay this description through a `MachineBuilder`, which validates it
    /// by construction and rederives everything the encoding leaves out.
    fn build<E>(self) -> Result<Machine, E>
    where
        E: de::Error,
    {
        if self.version != ENCODING_FORMAT_VERSION {
            return Err(E::custom(format_args!(
                "unsupported format version {}; this is version {ENCODING_FORMAT_VERSION}",
                self.version,
            )));
        }

        let mut builder = MachineBuilder::new();

        // Flat, in definition order, so that each index space is numbered
        // exactly as it was: a `RegClass` index is named by operands.
        for bank in &self.banks {
            let size = SpillSlotSize::new(bank.size).ok_or_else(|| {
                E::custom(format_args!(
                    "bank size {} is not a power of two",
                    bank.size
                ))
            })?;
            builder.declare_reg_bank(size).map_err(E::custom)?;
        }
        for reg in &self.registers {
            match &reg.units {
                Some(units) => builder
                    .define_reg(reg.bank, units.start..units.end)
                    .map_err(E::custom)?,
                None => builder
                    .define_non_allocatable_reg(reg.bank)
                    .map_err(E::custom)?,
            };
        }
        for group in &self.groups {
            builder
                .define_reg_group(group.bank, group.members.iter().copied())
                .map_err(E::custom)?;
        }
        for class in &self.classes {
            // `define_reg_class` asserts this; a file must not be able to panic.
            if !class.spill_cost.is_sign_positive() {
                return Err(E::custom(format_args!(
                    "spill cost {} is negative",
                    class.spill_cost,
                )));
            }
            match &class.members {
                WireClassMembers::Regs(regs) => builder
                    .define_reg_class(class.bank, class.spill_cost, regs.iter().copied())
                    .map_err(E::custom)?,
                WireClassMembers::Groups(groups) => builder
                    .define_reg_group_class(class.bank, class.spill_cost, groups.iter().copied())
                    .map_err(E::custom)?,
            };
        }

        builder.finish().map_err(E::custom)
    }
}

#[derive(Deserialize)]
#[serde(rename = "Function", deny_unknown_fields)]
struct WireFunction {
    version: u32,
    entry_block: Block,
    values: Vec<WireValue>,
    insts: Vec<WireInst>,
    blocks: Vec<WireBlock>,
}

#[derive(Deserialize)]
#[serde(rename = "Value", deny_unknown_fields)]
struct WireValue {
    reg_class: RegClass,
    remat_cost: Option<RematCost>,
}

#[derive(Deserialize)]
#[serde(rename = "Inst", deny_unknown_fields)]
struct WireInst {
    block: Block,
    operands: Vec<Operand>,

    /// The clobbered registers, as the ascending index list `RegSet`'s
    /// `Serialize` emits.
    clobbers: Vec<Reg>,
}

#[derive(Deserialize)]
#[serde(rename = "Block", deny_unknown_fields)]
struct WireBlock {
    frequency: f32,
    params: Vec<Val>,
    insts: Vec<Inst>,
    successors: Vec<WireSuccessor>,
    predecessors: Vec<Block>,
}

#[derive(Deserialize)]
#[serde(rename = "Successor", deny_unknown_fields)]
struct WireSuccessor {
    block: Block,
    args: Vec<Val>,
}

impl<'de> Deserialize<'de> for DeserializedFunction {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        WireFunction::deserialize(deserializer)?.from_wire()
    }
}

impl WireFunction {
    /// Move this into owned tables and check it, the same checks `capture`
    /// runs on a live function.
    fn from_wire<E: de::Error>(self) -> Result<DeserializedFunction, E> {
        if self.version != ENCODING_FORMAT_VERSION {
            return Err(E::custom(format_args!(
                "unsupported format version {}; this is version {ENCODING_FORMAT_VERSION}",
                self.version,
            )));
        }

        let mut values = PrimaryMap::default();
        for value in self.values {
            values.push_unwrap(ValueData {
                reg_class: value.reg_class,
                remat_cost: value.remat_cost,
            });
        }

        let mut insts = PrimaryMap::default();
        for inst in self.insts {
            insts.push_unwrap(InstData {
                block: inst.block,
                operands: inst.operands,
                clobbers: inst.clobbers,
            });
        }

        let mut blocks = PrimaryMap::default();
        for block in self.blocks {
            // `BlockFrequency::new` asserts this; a file must not be able to
            // panic.
            if !block.frequency.is_sign_positive() {
                return Err(E::custom(format_args!(
                    "block frequency {} is negative",
                    block.frequency,
                )));
            }
            blocks.push_unwrap(BlockData {
                frequency: BlockFrequency::new(block.frequency),
                params: block.params,
                insts: block.insts,
                successors: block
                    .successors
                    .into_iter()
                    .map(|succ| SuccessorData {
                        block: succ.block,
                        args: succ.args,
                    })
                    .collect(),
                predecessors: block.predecessors,
            });
        }

        DeserializedFunction {
            entry_block: self.entry_block,
            values,
            insts,
            blocks,
            dominators: DominatorTree::default(),
        }
        .finish()
        .map_err(E::custom)
    }
}

/// A function deserialized from [`serialize`][crate::serialize]'s encoding.
///
/// Implements [`InputFunction`].
#[derive(Clone)]
pub struct DeserializedFunction {
    entry_block: Block,
    values: PrimaryMap<Val, ValueData>,
    insts: PrimaryMap<Inst, InstData>,
    blocks: PrimaryMap<Block, BlockData>,
    dominators: DominatorTree,
}

#[derive(Clone)]
struct ValueData {
    reg_class: RegClass,
    remat_cost: Option<RematCost>,
}

#[derive(Clone)]
struct InstData {
    block: Block,
    operands: Vec<Operand>,
    clobbers: Vec<Reg>,
}

#[derive(Clone)]
struct BlockData {
    frequency: BlockFrequency,
    params: Vec<Val>,
    insts: Vec<Inst>,
    successors: Vec<SuccessorData>,
    predecessors: Vec<Block>,
}

#[derive(Clone)]
struct SuccessorData {
    block: Block,
    args: Vec<Val>,
}

impl fmt::Debug for DeserializedFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.display(), f)
    }
}

impl DeserializedFunction {
    /// Bounds-check every entity reference, then compute the dominator tree.
    fn finish(mut self) -> Result<Self> {
        let check_val = |val: Val| {
            (val.index() < self.values.len())
                .then_some(val)
                .ok_or(Error::ValOutOfBounds { val })
        };
        let check_block = |block: Block| {
            (block.index() < self.blocks.len())
                .then_some(block)
                .ok_or(Error::BlockOutOfBounds { block })
        };
        let check_inst = |inst: Inst| {
            (inst.index() < self.insts.len())
                .then_some(inst)
                .ok_or(Error::InstOutOfBounds { inst })
        };

        check_block(self.entry_block)?;
        for (_inst, inst) in self.insts.iter() {
            check_block(inst.block)?;
            for operand in &inst.operands {
                if let Some(val) = operand.val() {
                    check_val(val)?;
                }
            }
            // Clobbers need the machine, which this pass does not have;
            // `impl Deserialize for DeserializedInput` bounds them.
        }

        for (_b, block) in self.blocks.iter() {
            for &param in &block.params {
                check_val(param)?;
            }
            for &inst in &block.insts {
                check_inst(inst)?;
            }
            for succ in &block.successors {
                check_block(succ.block)?;
                for &arg in &succ.args {
                    check_val(arg)?;
                }
            }
            for &pred in &block.predecessors {
                check_block(pred)?;
            }
        }

        self.recompute_dominators();
        Ok(self)
    }

    /// Rebuild the dominator tree from the control-flow graph.
    fn recompute_dominators(&mut self) {
        let mut dominators = mem::take(&mut self.dominators);
        dominators.compute(&*self);
        self.dominators = dominators;
    }
}

/// A value of a [`DeserializedFunction`].
#[derive(Clone, Copy)]
pub struct DeserializedValue<'a> {
    func: &'a DeserializedFunction,
    val: Val,
}

/// An instruction of a [`DeserializedFunction`].
#[derive(Clone, Copy)]
pub struct DeserializedInst<'a> {
    func: &'a DeserializedFunction,
    inst: Inst,
}

/// A block of a [`DeserializedFunction`].
#[derive(Clone, Copy)]
pub struct DeserializedBlock<'a> {
    func: &'a DeserializedFunction,
    block: Block,
}

/// The iterator returned by [`InputFunction::values`] for a
/// [`DeserializedFunction`].
pub struct DeserializedValuesIter<'a> {
    func: &'a DeserializedFunction,
    keys: PrimaryMapKeys<Val>,
}

/// The iterator returned by [`InputFunction::blocks`] for a
/// [`DeserializedFunction`].
pub struct DeserializedBlocksIter<'a> {
    func: &'a DeserializedFunction,
    keys: PrimaryMapKeys<Block>,
}

/// The iterator returned by [`InputBlock::insts`] for a
/// [`DeserializedFunction`].
pub struct DeserializedInstsIter<'b> {
    func: &'b DeserializedFunction,
    insts: slice::Iter<'b, Inst>,
}

/// The iterator returned by [`InputBlock::successors`] for a
/// [`DeserializedFunction`].
pub struct DeserializedSuccessorsIter<'b> {
    inner: slice::Iter<'b, SuccessorData>,
}

impl<'a> Iterator for DeserializedValuesIter<'a> {
    type Item = (Val, DeserializedValue<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        let val = self.keys.next()?;
        Some((
            val,
            DeserializedValue {
                func: self.func,
                val,
            },
        ))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.keys.size_hint()
    }
}

impl ExactSizeIterator for DeserializedValuesIter<'_> {}

impl<'a> Iterator for DeserializedBlocksIter<'a> {
    type Item = (Block, DeserializedBlock<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        let block = self.keys.next()?;
        Some((
            block,
            DeserializedBlock {
                func: self.func,
                block,
            },
        ))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.keys.size_hint()
    }
}

impl ExactSizeIterator for DeserializedBlocksIter<'_> {}

impl<'b> DeserializedInstsIter<'b> {
    fn item(&self, inst: &Inst) -> (Inst, DeserializedInst<'b>) {
        (
            *inst,
            DeserializedInst {
                func: self.func,
                inst: *inst,
            },
        )
    }
}

impl<'b> Iterator for DeserializedInstsIter<'b> {
    type Item = (Inst, DeserializedInst<'b>);

    fn next(&mut self) -> Option<Self::Item> {
        let inst = self.insts.next()?;
        Some(self.item(inst))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.insts.size_hint()
    }
}

impl DoubleEndedIterator for DeserializedInstsIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let inst = self.insts.next_back()?;
        Some(self.item(inst))
    }
}

impl ExactSizeIterator for DeserializedInstsIter<'_> {}

impl Iterator for DeserializedSuccessorsIter<'_> {
    type Item = Block;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.inner.next()?.block)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl ExactSizeIterator for DeserializedSuccessorsIter<'_> {}

impl InputFunction for DeserializedFunction {
    type InputBlock<'a>
        = DeserializedBlock<'a>
    where
        Self: 'a;

    type InputInst<'a>
        = DeserializedInst<'a>
    where
        Self: 'a;

    type InputValue<'a>
        = DeserializedValue<'a>
    where
        Self: 'a;

    fn len_values(&self) -> usize {
        self.values.len()
    }

    type ValuesIter<'a>
        = DeserializedValuesIter<'a>
    where
        Self: 'a;

    fn values(&self) -> Self::ValuesIter<'_> {
        DeserializedValuesIter {
            func: self,
            keys: self.values.keys(),
        }
    }

    fn value(&self, val: Val) -> Self::InputValue<'_> {
        DeserializedValue { func: self, val }
    }

    fn len_insts(&self) -> usize {
        self.insts.len()
    }

    fn inst(&self, inst: Inst) -> Self::InputInst<'_> {
        DeserializedInst { func: self, inst }
    }

    fn entry_block(&self) -> Block {
        self.entry_block
    }

    fn len_blocks(&self) -> usize {
        self.blocks.len()
    }

    fn block(&self, block: Block) -> Self::InputBlock<'_> {
        DeserializedBlock { func: self, block }
    }

    type BlocksIter<'a>
        = DeserializedBlocksIter<'a>
    where
        Self: 'a;

    fn blocks(&self) -> Self::BlocksIter<'_> {
        DeserializedBlocksIter {
            func: self,
            keys: self.blocks.keys(),
        }
    }
}

impl<'a> InputValue<'a> for DeserializedValue<'a> {
    fn val(&self) -> Val {
        self.val
    }

    fn remat_cost(&self) -> Option<RematCost> {
        self.func.values[self.val].remat_cost
    }

    fn reg_class(&self) -> RegClass {
        self.func.values[self.val].reg_class
    }
}

impl<'a> InputInst<'a> for DeserializedInst<'a> {
    fn inst(&self) -> Inst {
        self.inst
    }

    fn block(&self) -> Block {
        self.func.insts[self.inst].block
    }

    fn operands_len(&self) -> usize {
        self.func.insts[self.inst].operands.len()
    }

    type OperandsIter<'b>
        = iter::Copied<slice::Iter<'b, Operand>>
    where
        Self: 'b;

    fn operands(&self) -> Self::OperandsIter<'_> {
        self.func.insts[self.inst].operands.iter().copied()
    }

    fn operand(&self, i: usize) -> Operand {
        self.func.insts[self.inst].operands[i]
    }

    fn clobbers(&self) -> RegSet {
        let mut set = RegSet::new();
        for &reg in &self.func.insts[self.inst].clobbers {
            set.insert(reg);
        }
        set
    }
}

impl<'a> InputBlock<'a> for DeserializedBlock<'a> {
    type InputInst<'b>
        = DeserializedInst<'b>
    where
        Self: 'b;

    fn block(&self) -> Block {
        self.block
    }

    fn frequency(&self) -> BlockFrequency {
        self.func.blocks[self.block].frequency
    }

    fn len_insts(&self, _block: Block) -> usize {
        self.func.blocks[self.block].insts.len()
    }

    type InstsIter<'b>
        = DeserializedInstsIter<'b>
    where
        Self: 'b;

    fn insts(&self) -> Self::InstsIter<'_> {
        DeserializedInstsIter {
            func: self.func,
            insts: self.func.blocks[self.block].insts.iter(),
        }
    }

    fn len_params(&self) -> usize {
        self.func.blocks[self.block].params.len()
    }

    type ParamsIter<'b>
        = iter::Copied<slice::Iter<'b, Val>>
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
        self.func.blocks[self.block].successors.len()
    }

    type SuccessorsIter<'b>
        = DeserializedSuccessorsIter<'b>
    where
        Self: 'b;

    fn successors(&self) -> Self::SuccessorsIter<'_> {
        DeserializedSuccessorsIter {
            inner: self.func.blocks[self.block].successors.iter(),
        }
    }

    fn len_predecessors(&self) -> usize {
        self.func.blocks[self.block].predecessors.len()
    }

    type PredecessorsIter<'b>
        = iter::Copied<slice::Iter<'b, Block>>
    where
        Self: 'b;

    fn predecessors(&self) -> Self::PredecessorsIter<'_> {
        self.func.blocks[self.block].predecessors.iter().copied()
    }

    fn len_successor_block_args(&self, i: usize) -> usize {
        self.func.blocks[self.block].successors[i].args.len()
    }

    type SuccessorBlockArgsIter<'b>
        = iter::Copied<slice::Iter<'b, Val>>
    where
        Self: 'b;

    fn successor_block_args(&self, successor: usize) -> Self::SuccessorBlockArgsIter<'_> {
        self.func.blocks[self.block].successors[successor]
            .args
            .iter()
            .copied()
    }
}

/// A whole allocation problem, deserialized from [`crate::serialize`]'s
/// encoding.
pub struct DeserializedInput {
    options: InputOptions,
    machine: Machine,
    func: DeserializedFunction,
}

#[derive(Deserialize)]
#[serde(rename = "Input", deny_unknown_fields)]
struct WireInput {
    options: InputOptions,
    machine: Machine,
    func: DeserializedFunction,
}

impl<'de> Deserialize<'de> for DeserializedInput {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let WireInput {
            options,
            machine,
            func,
        } = WireInput::deserialize(deserializer)?;

        // The references a function cannot check without the machine, and
        // `options.validate_input` may be `false` in the file.
        let num_classes = machine.reg_classes().len();
        let check = |class: RegClass| -> Result<(), D::Error> {
            (class.index() < num_classes).then_some(()).ok_or_else(|| {
                de::Error::custom(format_args!(
                    "register class {} is out of range; the machine has {num_classes}",
                    class.index(),
                ))
            })
        };
        for (_val, value) in func.values() {
            check(value.reg_class())?;
        }
        for i in 0..func.len_insts() {
            for operand in func.inst(Inst::try_new(i).unwrap()).operands() {
                if let OperandConstraint::Reg(class) = operand.constraint() {
                    check(class)?;
                }
            }
        }

        // Read out of the wire `Vec`, not through `InputInst::clobbers`:
        // building that `RegSet` is itself the unsafe step, since
        // `FixedEntitySet::insert` panics above its capacity.
        let num_registers = machine.num_registers();
        for inst in func.insts.values() {
            for reg in &inst.clobbers {
                if reg.index() >= num_registers {
                    return Err(de::Error::custom(format_args!(
                        "clobbered register {} is out of range; the machine has \
                         {num_registers}",
                        reg.index(),
                    )));
                }
            }
        }

        Ok(DeserializedInput {
            options,
            machine,
            func,
        })
    }
}

impl DeserializedInput {
    /// The options this problem asks the allocator for.
    pub fn options(&self) -> &InputOptions {
        &self.options
    }

    /// The machine this problem allocates registers of.
    pub fn machine(&self) -> &Machine {
        &self.machine
    }

    /// The function this problem allocates registers for.
    pub fn func(&self) -> &DeserializedFunction {
        &self.func
    }

    /// Borrow this as an [`Input`], ready to hand to [`crate::run`].
    ///
    /// No callback, unlike `TestInput::with_input`: this owns its `Machine`,
    /// so all three references come from the same `&self`.
    pub fn as_input(&self) -> Input<'_, DeserializedFunction> {
        Input {
            options: &self.options,
            machine: &self.machine,
            func: &self.func,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{OperandConstraint, test::*};
    use alloc::vec;

    /// Every `TestInput` fixture, by name.
    pub fn fixtures() -> Vec<(&'static str, TestInput)> {
        use OperandConstraint::{Any, Reg as RegC, Stack};
        let class = |i| RegClass::try_new(i).unwrap();
        vec![
            ("default", TestInput::default()),
            (
                "use_constraints",
                TestInput::with_use_constraints(&[Any, Stack, RegC(class(0))]),
            ),
            (
                "group_use_constraints",
                TestInput::with_group_use_constraints(&[Any, Stack]),
            ),
            (
                "two_uses_of_different_values",
                TestInput::with_two_uses_of_different_values(),
            ),
            (
                "values_in_two_banks_spilled_and_reloaded",
                TestInput::with_values_in_two_banks_spilled_and_reloaded(),
            ),
            ("reuse_def_any", TestInput::with_reuse_def(Any)),
            ("reuse_def_stack", TestInput::with_reuse_def(Stack)),
            (
                "reuse_of_a_surviving_value",
                TestInput::with_reuse_of_a_surviving_value(),
            ),
            (
                "two_reads_and_a_reuse_of_a_surviving_value",
                TestInput::with_two_reads_and_a_reuse_of_a_surviving_value(),
            ),
            (
                "a_fixed_read_beside_a_reuse_of_a_surviving_value",
                TestInput::with_a_fixed_read_beside_a_reuse_of_a_surviving_value(),
            ),
            (
                "a_pinned_read_before_a_reuse_that_reads_twice",
                TestInput::with_a_pinned_read_before_a_reuse_that_reads_twice(),
            ),
            (
                "a_reuse_of_a_live_in_value",
                TestInput::with_a_reuse_of_a_live_in_value(),
            ),
            (
                "two_reuses_at_one_point",
                TestInput::with_two_reuses_at_one_point(),
            ),
            (
                "two_reuses_of_a_dying_value",
                TestInput::with_two_reuses_of_a_dying_value(),
            ),
            (
                "block_arg_constraints",
                TestInput::with_block_arg_constraints(Any, Stack),
            ),
            (
                "a_rematerialized_block_arg",
                TestInput::with_a_rematerialized_block_arg(),
            ),
            ("a_critical_edge", TestInput::with_a_critical_edge()),
            ("spilled_merge_param", TestInput::with_spilled_merge_param()),
            (
                "a_move_before_an_unconditional_branch",
                TestInput::with_a_move_before_an_unconditional_branch(),
            ),
            (
                "a_self_looping_entry_block",
                TestInput::with_a_self_looping_entry_block(),
            ),
            ("two_entry_params", TestInput::with_two_entry_params()),
            (
                "entry_params_in_two_banks",
                TestInput::with_entry_params_in_two_banks(),
            ),
            (
                "an_entry_param_read_two_ways",
                TestInput::with_an_entry_param_read_two_ways(),
            ),
            ("stack_param_and_arg", TestInput::with_stack_param_and_arg()),
            (
                "an_early_read_beside_a_clobber_of_every_register",
                TestInput::with_an_early_read_beside_a_clobber_of_every_register(),
            ),
            (
                "a_clobbering_terminator_before_a_merge",
                TestInput::with_a_clobbering_terminator_before_a_merge(),
            ),
            (
                "a_reload_clobbered_before_its_next_read",
                TestInput::with_a_reload_clobbered_before_its_next_read(),
            ),
        ]
    }

    /// Assert that `b` reports exactly what `a` does, through every method of
    /// `InputFunction`, `InputBlock`, `InputInst` and `InputValue`.
    pub fn assert_same_function(a: &impl InputFunction, b: &impl InputFunction) {
        assert_eq!(a.len_values(), b.len_values());
        assert_eq!(a.len_insts(), b.len_insts());
        assert_eq!(a.len_blocks(), b.len_blocks());
        assert_eq!(a.entry_block(), b.entry_block());

        // Through the iterator and through the by-key accessor, which are two
        // different code paths on both sides.
        for i in 0..a.len_values() {
            let val = Val::try_new(i).unwrap();
            assert_eq!(describe_value(&a.value(val)), describe_value(&b.value(val)));
        }
        assert_eq!(
            a.values()
                .map(|(val, v)| (val, describe_value(&v)))
                .collect::<Vec<_>>(),
            b.values()
                .map(|(val, v)| (val, describe_value(&v)))
                .collect::<Vec<_>>(),
        );

        for i in 0..a.len_insts() {
            let inst = Inst::try_new(i).unwrap();
            assert_eq!(describe_inst(&a.inst(inst)), describe_inst(&b.inst(inst)));
        }

        for i in 0..a.len_blocks() {
            let block = Block::try_new(i).unwrap();
            assert_same_block(&a.block(block), &b.block(block), block, a.len_blocks());
        }

        // `blocks()` must agree with `block()`, and yield the blocks in order.
        assert_eq!(
            a.blocks().map(|(b, _)| b).collect::<Vec<_>>(),
            b.blocks().map(|(b, _)| b).collect::<Vec<_>>(),
        );
    }

    fn describe_value<'x>(v: &impl InputValue<'x>) -> (Val, RegClass, Option<RematCost>) {
        (v.val(), v.reg_class(), v.remat_cost())
    }

    type InstFacts = (Inst, Block, usize, Vec<Operand>, Vec<Operand>, RegSet);

    fn describe_inst<'x>(i: &impl InputInst<'x>) -> InstFacts {
        (
            i.inst(),
            i.block(),
            i.operands_len(),
            i.operands().collect(),
            (0..i.operands_len()).map(|j| i.operand(j)).collect(),
            i.clobbers(),
        )
    }

    fn assert_same_block<'x, 'y>(
        a: &impl InputBlock<'x>,
        b: &impl InputBlock<'y>,
        block: Block,
        len_blocks: usize,
    ) {
        assert_eq!(a.block(), b.block());
        assert_eq!(a.frequency(), b.frequency());
        assert_eq!(a.len_insts(block), b.len_insts(block));
        assert_eq!(
            a.insts().map(|(i, _)| i).collect::<Vec<_>>(),
            b.insts().map(|(i, _)| i).collect::<Vec<_>>(),
        );
        assert_eq!(
            a.insts().rev().map(|(i, _)| i).collect::<Vec<_>>(),
            b.insts().rev().map(|(i, _)| i).collect::<Vec<_>>(),
        );
        assert_eq!(a.len_params(), b.len_params());
        assert_eq!(
            a.params().collect::<Vec<_>>(),
            b.params().collect::<Vec<_>>(),
        );
        assert_eq!(a.immediate_dominator(), b.immediate_dominator());
        assert_eq!(a.len_successors(), b.len_successors());
        assert_eq!(
            a.successors().collect::<Vec<_>>(),
            b.successors().collect::<Vec<_>>(),
        );
        assert_eq!(a.len_predecessors(), b.len_predecessors());
        assert_eq!(
            a.predecessors().collect::<Vec<_>>(),
            b.predecessors().collect::<Vec<_>>(),
        );
        for i in 0..a.len_successors() {
            assert_eq!(a.len_successor_block_args(i), b.len_successor_block_args(i));
            assert_eq!(
                a.successor_block_args(i).collect::<Vec<_>>(),
                b.successor_block_args(i).collect::<Vec<_>>(),
            );
        }

        // Dominance over every pair, which is what proves recomputing it is
        // the same as carrying it.
        for i in 0..len_blocks {
            let other = Block::try_new(i).unwrap();
            assert_eq!(a.dominates(other), b.dominates(other));
        }
    }

    #[test]
    fn deserialized_function_is_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<DeserializedFunction>();
        assert_send_sync::<DeserializedInput>();
        assert_send_sync::<Input<'_, DeserializedFunction>>();
    }
}

#[cfg(all(test, feature = "serialize"))]
mod round_trip_tests {
    use super::{tests::*, *};
    use crate::{
        Context, RegClass,
        serialize::{SerializeFunction, SerializeInput},
        test::*,
    };
    use alloc::{
        format,
        string::{String, ToString},
    };
    use mutatis::{
        check::{Check, CheckResult},
        mutators as m,
    };

    /// Round-trip `machine` through both formats, and report what came back.
    ///
    /// `Machine: Debug` covers the derived state too -- the intersection
    /// classes, the `member_set` bitsets -- so comparing the two debug strings
    /// is a strong equality.
    fn round_trip(machine: &Machine) -> Result<(), String> {
        let json = serde_json::to_string(machine).map_err(|e| e.to_string())?;
        let from_json: Machine = serde_json::from_str(&json).map_err(|e| e.to_string())?;
        if format!("{from_json:?}") != format!("{machine:?}") {
            return Err(format!("json round trip changed the machine:\n{json}"));
        }

        let bytes = postcard::to_allocvec(machine).map_err(|e| e.to_string())?;
        let from_postcard: Machine = postcard::from_bytes(&bytes).map_err(|e| e.to_string())?;
        if format!("{from_postcard:?}") != format!("{machine:?}") {
            return Err("postcard round trip changed the machine".into());
        }

        Ok(())
    }

    /// A machine with a non-allocatable register, both in a class and out of
    /// one: `TestMachine` never generates one, so the `units: None` arm would
    /// otherwise go untested.
    fn machine_with_non_allocatable_regs() -> Machine {
        let mut builder = MachineBuilder::new();
        let bank = builder
            .declare_reg_bank(SpillSlotSize::new(8).unwrap())
            .unwrap();
        let unit = |i| RegUnit::try_new(i).unwrap();
        let r0 = builder.define_reg(bank, unit(0)..unit(1)).unwrap();
        let r1 = builder.define_reg(bank, unit(1)..unit(2)).unwrap();
        let in_class = builder.define_non_allocatable_reg(bank).unwrap();
        builder.define_non_allocatable_reg(bank).unwrap();
        builder.define_reg_class(bank, 1.0, [r0, r1]).unwrap();
        builder.define_reg_class(bank, 1.0, [in_class]).unwrap();
        builder.finish().unwrap()
    }

    /// Round-trip `func` through both formats.
    fn round_trip_function(func: &impl InputFunction) -> Result<[DeserializedFunction; 2], String> {
        let wrapped = SerializeFunction::new(func);
        let json = serde_json::to_string(&wrapped).map_err(|e| e.to_string())?;
        let bytes = postcard::to_allocvec(&wrapped).map_err(|e| e.to_string())?;
        Ok([
            serde_json::from_str(&json).map_err(|e| e.to_string())?,
            postcard::from_bytes(&bytes).map_err(|e| e.to_string())?,
        ])
    }

    /// Round-trip `input` through both formats.
    fn round_trip_input(
        input: &Input<'_, impl InputFunction>,
    ) -> Result<[DeserializedInput; 2], String> {
        let wrapped = SerializeInput::new(input);
        let json = serde_json::to_string(&wrapped).map_err(|e| e.to_string())?;
        let bytes = postcard::to_allocvec(&wrapped).map_err(|e| e.to_string())?;
        Ok([
            serde_json::from_str(&json).map_err(|e| e.to_string())?,
            postcard::from_bytes(&bytes).map_err(|e| e.to_string())?,
        ])
    }

    /// Everything an allocation says, as one comparable value.
    fn describe_allocation(input: &Input<'_, impl InputFunction>) -> String {
        let mut context = Context::new();
        let output = match crate::run(&mut context, input) {
            Ok(output) => output,
            Err(e) => return format!("Err({e})"),
        };

        let mut described = format!("{:?}", output.spill_slots().collect::<Vec<_>>());
        for i in 0..input.func.len_insts() {
            let inst = Inst::try_new(i).unwrap();
            described += &format!("{inst:?}: {:?}\n", output.inst_allocs(inst));
        }
        for i in 0..input.func.len_blocks() {
            let block = Block::try_new(i).unwrap();
            described += &format!(
                "{block:?}: {:?} {:?}\n",
                output.block_param_allocs(block),
                output
                    .block_insts_and_edits(input.func, block)
                    .collect::<Vec<_>>(),
            );
        }
        described
    }

    /// Every fixture, through both formats, reports exactly what it started as.
    #[test]
    fn function_round_trips() {
        for (name, input) in fixtures() {
            for deserialized in
                round_trip_function(&input.func).unwrap_or_else(|e| panic!("{name}: {e}"))
            {
                assert_same_function(&input.func, &deserialized);
                assert_eq!(
                    format!("{}", input.func.display()),
                    format!("{}", deserialized.display()),
                    "{name}",
                );
            }
        }
    }

    /// The headline property: a round-tripped problem allocates identically.
    #[test]
    fn allocation_results_match() {
        for (name, input) in fixtures() {
            input.with_input(|input| {
                let before = describe_allocation(input);
                for deserialized in
                    round_trip_input(input).unwrap_or_else(|e| panic!("{name}: {e}"))
                {
                    assert_eq!(
                        before,
                        describe_allocation(&deserialized.as_input()),
                        "{name}"
                    );
                }
            });
        }
    }

    /// The whole-`Input` path carries the options and the machine too.
    #[test]
    fn input_round_trips() {
        for (name, test_input) in fixtures() {
            test_input.with_input(|input| {
                for deserialized in
                    round_trip_input(input).unwrap_or_else(|e| panic!("{name}: {e}"))
                {
                    assert_eq!(
                        deserialized.options().validate_input,
                        input.options.validate_input,
                        "{name}",
                    );
                    assert_eq!(
                        deserialized.options().redundant_move_elimination_level,
                        input.options.redundant_move_elimination_level,
                        "{name}",
                    );
                    assert_eq!(
                        deserialized.options().dead_move_elimination_level,
                        input.options.dead_move_elimination_level,
                        "{name}",
                    );
                    assert_eq!(
                        deserialized.options().eliminate_dead_register_moves,
                        input.options.eliminate_dead_register_moves,
                        "{name}",
                    );
                    assert_eq!(
                        deserialized.options().narrow_spill_slot_live_ranges,
                        input.options.narrow_spill_slot_live_ranges,
                        "{name}",
                    );
                    assert_eq!(
                        deserialized.options().hoist_demanded_moves,
                        input.options.hoist_demanded_moves,
                        "{name}",
                    );
                    assert_eq!(
                        format!("{:?}", deserialized.machine()),
                        format!("{:?}", input.machine),
                        "{name}",
                    );
                    assert_same_function(input.func, deserialized.func());
                }
            });
        }
    }

    /// Folded into the tests above, but named so that a `serialize_seq(None)`
    /// regression -- which only postcard rejects -- fails obviously.
    #[test]
    fn postcard_round_trips() {
        let input = TestInput::with_a_critical_edge();
        input.with_input(|input| {
            let bytes = postcard::to_allocvec(&SerializeInput::new(input)).unwrap();
            let deserialized: DeserializedInput = postcard::from_bytes(&bytes).unwrap();
            assert_same_function(input.func, deserialized.func());
        });
    }

    #[test]
    fn machine_round_trips() -> CheckResult<TestMachine> {
        for machine in [
            TestMachine::two_registers().build(),
            TestMachine::one_register_group().build(),
            TestMachine::groups_and_registers().build(),
            TestMachine::default().build(),
            machine_with_non_allocatable_regs(),
        ] {
            round_trip(&machine).unwrap();
        }

        Check::new()
            .iters(1000)
            .run(|machine: &TestMachine| round_trip(&machine.build()))
    }

    /// The sweep over the machine x function space, which is what shakes out
    /// an accessor the format forgot.
    #[test]
    fn round_trips_arbitrary_inputs() -> CheckResult<TestInput> {
        Check::new().iters(1000).run_with(
            m::default::<TestInput>(),
            crate::test::corpus(),
            |input: &TestInput| {
                input.with_input(|input| -> Result<(), String> {
                    let before = describe_allocation(input);
                    for deserialized in round_trip_input(input)? {
                        assert_same_function(input.func, deserialized.func());
                        if describe_allocation(&deserialized.as_input()) != before {
                            return Err("a round trip changed the allocation".into());
                        }
                    }
                    Ok(())
                })
            },
        )
    }

    /// A frequency survives postcard bit-exactly: it is already truncated to
    /// the 16 bits `BlockFrequency` packs, so repacking is idempotent.
    #[test]
    fn block_frequency_round_trips_exactly() {
        for frequency in [
            BlockFrequency::COLD,
            BlockFrequency::NORMAL,
            BlockFrequency::HOT,
            BlockFrequency::new(0.5),
            BlockFrequency::new(10.0),
            BlockFrequency::new(10_000.0),
            BlockFrequency::new(f32::INFINITY),
        ] {
            let bytes = postcard::to_allocvec(&frequency.as_f32()).unwrap();
            let back: f32 = postcard::from_bytes(&bytes).unwrap();
            assert_eq!(BlockFrequency::new(back), frequency);
        }
    }

    /// The documented `serde_json` limitation, pinned so that it stays a known
    /// one: JSON has no way to write a non-finite float.
    #[test]
    fn json_cannot_carry_an_infinite_frequency() {
        let json = serde_json::to_string(&f32::INFINITY).unwrap();
        assert_eq!(json, "null");
        assert!(serde_json::from_str::<f32>(&json).is_err());
    }

    /// A round trip must hand out the same `RegClass` indices, because
    /// operands and values name classes by index. Guards against a future
    /// "group the builder calls by bank" refactor renumbering them.
    #[test]
    fn reg_class_indices_are_preserved() {
        let machine = TestMachine::groups_and_registers().build();
        let json = serde_json::to_string(&machine).unwrap();
        let again: Machine = serde_json::from_str(&json).unwrap();

        assert_eq!(again.num_user_classes(), machine.num_user_classes());
        for i in 0..machine.num_user_classes() {
            let class = RegClass::try_new(i).unwrap();
            assert_eq!(class.bank(&again), class.bank(&machine));
            assert_eq!(class.spill_cost(&again), class.spill_cost(&machine));
            assert_eq!(
                format!("{:?}", class.members(&again)),
                format!("{:?}", class.members(&machine)),
            );
        }
    }
}

/// Every kind of corruption a file can carry must come back as an error, and
/// never as a panic, an unbounded allocation, or a silently repaired value.
#[cfg(all(test, feature = "serialize"))]
mod corrupt_tests {
    use super::*;
    use crate::{serialize::SerializeInput, test::*};
    use alloc::{
        string::{String, ToString},
        vec,
    };
    use serde_json::{Value, json};

    /// Serialize a fixture, let `corrupt` edit the JSON, and return the error
    /// that reading it back produces.
    fn error_from(corrupt: impl FnOnce(&mut Value)) -> String {
        let input = TestInput::with_use_constraints(&[crate::OperandConstraint::Any]);
        let mut json =
            input.with_input(|input| serde_json::to_value(SerializeInput::new(input)).unwrap());
        corrupt(&mut json);
        match serde_json::from_value::<DeserializedInput>(json.clone()) {
            Ok(_) => panic!("expected an error, but this was accepted:\n{json:#}"),
            Err(e) => e.to_string(),
        }
    }

    #[test]
    fn rejects_corrupt_encodings() {
        // Each case is a corruption and a fragment its error must mention.
        let cases: Vec<(&str, fn(&mut Value), &str)> = vec![
            (
                "machine version",
                |j| j["machine"]["version"] = json!(ENCODING_FORMAT_VERSION + 1),
                "version",
            ),
            (
                "function version",
                |j| j["func"]["version"] = json!(ENCODING_FORMAT_VERSION + 1),
                "version",
            ),
            (
                "entry block",
                |j| j["func"]["entry_block"] = json!(9),
                "block index space",
            ),
            (
                "inst's block",
                |j| j["func"]["insts"][0]["block"] = json!(9),
                "block index space",
            ),
            (
                "block's inst",
                |j| j["func"]["blocks"][0]["insts"][0] = json!(9),
                "instruction index space",
            ),
            (
                "block parameter",
                |j| j["func"]["blocks"][0]["params"] = json!([9]),
                "value index space",
            ),
            (
                "successor block",
                |j| j["func"]["blocks"][0]["successors"] = json!([{"block": 9, "args": []}]),
                "block index space",
            ),
            (
                "successor argument",
                |j| j["func"]["blocks"][0]["successors"] = json!([{"block": 0, "args": [9]}]),
                "value index space",
            ),
            (
                "predecessor",
                |j| j["func"]["blocks"][0]["predecessors"] = json!([9]),
                "block index space",
            ),
            (
                "operand value",
                |j| j["func"]["insts"][0]["operands"][0]["val"] = json!(9),
                "value index space",
            ),
            (
                "unrepresentable value",
                |j| j["func"]["insts"][0]["operands"][0]["val"] = json!(u64::MAX),
                "out of range",
            ),
            (
                "oversized reuse",
                |j| j["func"]["insts"][0]["operands"][0]["constraint"] = json!({"reuse": 70000}),
                "does not fit",
            ),
            (
                "value's register class",
                |j| j["func"]["values"][0]["reg_class"] = json!(300),
                "out of range",
            ),
            (
                "operand's register class",
                |j| {
                    j["func"]["insts"][0]["operands"][0]["constraint"] = json!({"reg": 300});
                },
                "out of range",
            ),
            (
                "negative frequency",
                |j| j["func"]["blocks"][0]["frequency"] = json!(-1.0),
                "frequency",
            ),
            (
                "negative spill cost",
                |j| j["machine"]["classes"][0]["spill_cost"] = json!(-1.0),
                "spill cost",
            ),
            (
                "bank size",
                |j| j["machine"]["banks"][0]["size"] = json!(3),
                "power of two",
            ),
            (
                "empty unit range",
                |j| j["machine"]["registers"][0]["units"] = json!({"start": 5, "end": 5}),
                "register units",
            ),
            (
                "backwards unit range",
                |j| j["machine"]["registers"][0]["units"] = json!({"start": 2, "end": 1}),
                "register units",
            ),
            (
                "class member",
                |j| j["machine"]["classes"][0]["members"] = json!({"regs": [9]}),
                "r9 is not in bank0",
            ),
            (
                "one-register group",
                |j| {
                    j["machine"]["groups"] = json!([{"bank": 0, "members": [0]}]);
                    j["machine"]["classes"][0]["members"] = json!({"groups": [0]});
                },
                "1 registers in it",
            ),
            (
                // Unrepresentable, so `Reg`'s own `Deserialize` refuses it.
                "unrepresentable clobber",
                |j| j["func"]["insts"][0]["clobbers"] = json!([u64::MAX]),
                "out of range",
            ),
            (
                // Representable, but not a register this machine defines.
                "out-of-range clobber",
                |j| j["func"]["insts"][0]["clobbers"] = json!([9]),
                "clobbered register 9 is out of range",
            ),
            (
                // Above `RegSet`'s capacity, where building the set panics.
                "clobber beyond the register set's capacity",
                |j| j["func"]["insts"][0]["clobbers"] = json!([1000]),
                "clobbered register 1000 is out of range",
            ),
            (
                "unknown field",
                |j| j["func"]["bogus"] = json!(1),
                "unknown field",
            ),
        ];

        for (what, corrupt, expected) in cases {
            let error = error_from(corrupt);
            assert!(
                error.contains(expected),
                "corrupting the {what} should report {expected:?}, but it reported {error:?}",
            );
        }
    }

    /// A buffer that stops in the middle is an error too, not a hang or a
    /// gigantic allocation from a length prefix that outruns the data.
    #[test]
    fn rejects_truncated_postcard() {
        let input = TestInput::with_use_constraints(&[crate::OperandConstraint::Any]);
        let bytes =
            input.with_input(|input| postcard::to_allocvec(&SerializeInput::new(input)).unwrap());

        for len in 0..bytes.len() {
            let result = postcard::from_bytes::<DeserializedInput>(&bytes[..len]);
            assert!(
                result.is_err(),
                "a {len}-byte prefix of a {}-byte encoding was accepted",
                bytes.len(),
            );
        }
    }
}
