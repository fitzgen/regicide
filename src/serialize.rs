//! Serializing a register allocation problem.
//!
//! [`SerializeInput`] captures a whole register allocation problem (options,
//! machine, and function); [`SerializeFunction`] captures just the
//! function. Both implement [`serde::Serialize`], so the serialization format
//! is the caller's choice: use [`serde_json`] for JSON, `postcard` for binary
//! encoding, etc...
//!
//! You can read serialized inputs, options, machines, and functions back again
//! with the [`deserialize`][crate::deserialize] module, whose
//! [`DeserializedInput`][crate::deserialize::DeserializedInput] hands out a
//! register allocation [`Input`] again. It can be replayed offline, attached to
//! a bug report, kept in a corpus, or loaded into the visualizer.
//!
//! What serialization does not do is reproduce validation errors. An invalid
//! function implementation will not round trip serialization and
//! deserialization.
//!
//! See the [`deserialize`][crate::deserialize] module for details on
//! deserializing register allocation inputs.
//!
//! # Encoding Format Stability
//!
//! The encoding is **not stable** and is liable to change across minor and
//! patch version bumps.
//!
//! # Example
//!
//! ```
//! use regicide::{
//!     Input, InputFunction,
//!     serialize::{SerializeFunction, SerializeInput},
//! };
//!
//! // Capture a whole allocation problem as JSON, to attach to a bug report.
//! fn capture(input: &Input<'_, impl InputFunction>) -> serde_json::Result<String> {
//!     let input = SerializeInput::new(input);
//!     serde_json::to_string(&input)
//! }
//!
//! // Or capture just the function, in a compact binary encoding, to keep a
//! // corpus of them next to the one machine that describes all their registers.
//! fn capture_func(func: &impl InputFunction) -> postcard::Result<Vec<u8>> {
//!     let func = SerializeFunction::new(func);
//!     postcard::to_allocvec(&func)
//! }
//! ```

use crate::{
    Block, ENCODING_FORMAT_VERSION, Entity, Input, InputBlock, InputFunction, InputInst,
    InputOptions, InputValue, Inst, Machine, RegBank, RegClass, RegUnit, RematCost,
    machine::RegClassMembers,
};
use serde::{
    Serialize, Serializer,
    ser::{self, SerializeSeq},
};

/// Serialize a sequence whose length is known up front.
fn serialize_seq<S, I>(
    serializer: S,
    len: usize,
    what: &'static str,
    iter: I,
) -> Result<S::Ok, S::Error>
where
    S: Serializer,
    I: Iterator,
    I::Item: Serialize,
{
    let mut seq = serializer.serialize_seq(Some(len))?;
    let mut n = 0;
    for item in iter {
        seq.serialize_element(&item)?;
        n += 1;
    }
    if n != len {
        return Err(ser::Error::custom(format_args!(
            "`{what}` reported {len} items but its iterator yielded {n}",
        )));
    }
    seq.end()
}

#[derive(Serialize)]
#[serde(rename = "Machine")]
struct WireMachine<B, R, G, C> {
    version: u32,
    banks: B,
    registers: R,
    groups: G,
    classes: C,
}

#[derive(Serialize)]
#[serde(rename = "Bank")]
struct WireBank {
    size: u16,
}

#[derive(Serialize)]
#[serde(rename = "Register")]
struct WireRegister {
    bank: RegBank,
    units: Option<WireUnitRange>,
}

#[derive(Serialize)]
#[serde(rename = "UnitRange")]
struct WireUnitRange {
    start: RegUnit,
    end: RegUnit,
}

#[derive(Serialize)]
#[serde(rename = "Group")]
struct WireGroup<M> {
    bank: RegBank,
    members: M,
}

#[derive(Serialize)]
#[serde(rename = "Class")]
struct WireClass<M> {
    bank: RegBank,
    spill_cost: f32,
    members: M,
}

#[derive(Serialize)]
#[serde(rename = "ClassMembers", rename_all = "lowercase")]
enum WireClassMembers<R, G> {
    Regs(R),
    Groups(G),
}

#[derive(Serialize)]
#[serde(rename = "Function")]
struct WireFunction<V, I, B> {
    version: u32,
    entry_block: Block,
    values: V,
    insts: I,
    blocks: B,
}

#[derive(Serialize)]
#[serde(rename = "Value")]
struct WireValue {
    reg_class: RegClass,
    remat_cost: Option<RematCost>,
}

#[derive(Serialize)]
#[serde(rename = "Inst")]
struct WireInst<O, C> {
    block: Block,
    operands: O,
    clobbers: C,
}

#[derive(Serialize)]
#[serde(rename = "Block")]
struct WireBlock<P, I, S, D> {
    frequency: f32,
    params: P,
    insts: I,
    successors: S,
    predecessors: D,
}

#[derive(Serialize)]
#[serde(rename = "Successor")]
struct WireSuccessor<A> {
    block: Block,
    args: A,
}

#[derive(Serialize)]
#[serde(rename = "Input")]
struct WireInput<'a, M, F> {
    options: &'a InputOptions,
    machine: M,
    func: F,
}

impl Serialize for Machine {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        WireMachine {
            version: ENCODING_FORMAT_VERSION,
            banks: Banks(self),
            registers: Regs(self),
            groups: Groups(self),
            classes: Classes(self),
        }
        .serialize(serializer)
    }
}

struct Banks<'a>(&'a Machine);
struct Regs<'a>(&'a Machine);
struct Groups<'a>(&'a Machine);
struct Classes<'a>(&'a Machine);

impl Serialize for Banks<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.collect_seq(self.0.reg_banks().map(|bank| WireBank {
            size: bank.size(self.0).size(),
        }))
    }
}

impl Serialize for Regs<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.collect_seq(self.0.regs().map(|reg| WireRegister {
            bank: reg.bank(self.0),
            units: reg.is_allocatable(self.0).then(|| {
                let units = reg.units(self.0);
                WireUnitRange {
                    start: units.start,
                    end: units.end,
                }
            }),
        }))
    }
}

impl Serialize for Groups<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.collect_seq(self.0.reg_groups().map(|group| WireGroup {
            bank: group.bank(self.0),
            members: group.members(self.0),
        }))
    }
}

impl Serialize for Classes<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let machine = self.0;
        // Only the user's classes; deserialization rederives the intersection
        // classes that follow them.
        serializer.collect_seq((0..machine.num_user_classes()).map(|i| {
            let class = RegClass::try_new(i).unwrap();
            WireClass {
                bank: class.bank(machine),
                spill_cost: class.spill_cost(machine),
                members: match class.members(machine) {
                    RegClassMembers::Regs(regs) => WireClassMembers::Regs(&regs[..]),
                    RegClassMembers::Groups(groups) => WireClassMembers::Groups(&groups[..]),
                },
            }
        }))
    }
}

/// An [`InputFunction`] wrapped up so that it implements [`Serialize`].
///
/// # Example
///
/// You can use whatever encoding format you like; here, we're using
/// `postcard`'s binary encoding.
///
/// ```
/// use regicide::{InputFunction, serialize::SerializeFunction};
///
/// fn capture_func(func: &impl InputFunction) -> postcard::Result<Vec<u8>> {
///     let func = SerializeFunction::new(func);
///     postcard::to_allocvec(&func)
/// }
/// ```
pub struct SerializeFunction<'a, F>(&'a F)
where
    F: InputFunction + ?Sized;

impl<'a, F> SerializeFunction<'a, F>
where
    F: InputFunction + ?Sized,
{
    /// Wrap `func` up for serialization.
    pub fn new(func: &'a F) -> Self {
        SerializeFunction(func)
    }
}

impl<F> Serialize for SerializeFunction<'_, F>
where
    F: InputFunction + ?Sized,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        WireFunction {
            version: ENCODING_FORMAT_VERSION,
            entry_block: self.0.entry_block(),
            values: Values(self.0),
            insts: Insts(self.0),
            blocks: Blocks(self.0),
        }
        .serialize(serializer)
    }
}

struct Values<'a, F: ?Sized>(&'a F);
struct Insts<'a, F: ?Sized>(&'a F);
struct Blocks<'a, F: ?Sized>(&'a F);
struct InstOperands<'a, F: ?Sized>(&'a F, Inst);
struct InstClobbers<'a, F: ?Sized>(&'a F, Inst);
struct BlockParams<'a, F: ?Sized>(&'a F, Block);
struct BlockInsts<'a, F: ?Sized>(&'a F, Block);
struct BlockSuccessors<'a, F: ?Sized>(&'a F, Block);
struct BlockPredecessors<'a, F: ?Sized>(&'a F, Block);
struct SuccessorArgs<'a, F: ?Sized>(&'a F, Block, usize);

impl<F> Serialize for Values<'_, F>
where
    F: InputFunction + ?Sized,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serialize_seq(
            serializer,
            self.0.len_values(),
            "len_values",
            self.0.values().map(|(_, value)| WireValue {
                reg_class: value.reg_class(),
                remat_cost: value.remat_cost(),
            }),
        )
    }
}

impl<F> Serialize for Insts<'_, F>
where
    F: InputFunction + ?Sized,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let func = self.0;
        let len = func.len_insts();
        serialize_seq(
            serializer,
            len,
            "len_insts",
            (0..len).map(|i| {
                let inst = Inst::try_new(i).unwrap();
                WireInst {
                    block: func.inst(inst).block(),
                    operands: InstOperands(func, inst),
                    clobbers: InstClobbers(func, inst),
                }
            }),
        )
    }
}

impl<F> Serialize for InstOperands<'_, F>
where
    F: InputFunction + ?Sized,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let inst = self.0.inst(self.1);
        serialize_seq(
            serializer,
            inst.operands_len(),
            "operands_len",
            inst.operands(),
        )
    }
}

impl<F> Serialize for InstClobbers<'_, F>
where
    F: InputFunction + ?Sized,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // The set iterates in ascending index order, exactly the `Vec<Reg>`
        // the other end reads. Its own `Serialize` collects an iterator of
        // unknown length, which postcard refuses.
        let clobbers = self.0.inst(self.1).clobbers();
        serialize_seq(serializer, clobbers.len(), "clobbers", clobbers.iter())
    }
}

impl<F> Serialize for Blocks<'_, F>
where
    F: InputFunction + ?Sized,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let func = self.0;
        let len = func.len_blocks();
        serialize_seq(
            serializer,
            len,
            "len_blocks",
            (0..len).map(|i| {
                let b = Block::try_new(i).unwrap();
                WireBlock {
                    frequency: func.block(b).frequency().as_f32(),
                    params: BlockParams(func, b),
                    insts: BlockInsts(func, b),
                    successors: BlockSuccessors(func, b),
                    predecessors: BlockPredecessors(func, b),
                }
            }),
        )
    }
}

impl<F> Serialize for BlockParams<'_, F>
where
    F: InputFunction + ?Sized,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let block = self.0.block(self.1);
        serialize_seq(serializer, block.len_params(), "len_params", block.params())
    }
}

impl<F> Serialize for BlockInsts<'_, F>
where
    F: InputFunction + ?Sized,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        fn insts<'a, S: Serializer>(
            serializer: S,
            block: &impl InputBlock<'a>,
            b: Block,
        ) -> Result<S::Ok, S::Error> {
            serialize_seq(
                serializer,
                block.len_insts(b),
                "len_insts",
                block.insts().map(|(inst, _)| inst),
            )
        }
        insts(serializer, &self.0.block(self.1), self.1)
    }
}

impl<F> Serialize for BlockSuccessors<'_, F>
where
    F: InputFunction + ?Sized,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let (func, b) = (self.0, self.1);
        let block = func.block(b);
        serialize_seq(
            serializer,
            block.len_successors(),
            "len_successors",
            block
                .successors()
                .enumerate()
                .map(|(i, succ)| WireSuccessor {
                    block: succ,
                    args: SuccessorArgs(func, b, i),
                }),
        )
    }
}

impl<F> Serialize for BlockPredecessors<'_, F>
where
    F: InputFunction + ?Sized,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let block = self.0.block(self.1);
        serialize_seq(
            serializer,
            block.len_predecessors(),
            "len_predecessors",
            block.predecessors(),
        )
    }
}

impl<F> Serialize for SuccessorArgs<'_, F>
where
    F: InputFunction + ?Sized,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let block = self.0.block(self.1);
        serialize_seq(
            serializer,
            block.len_successor_block_args(self.2),
            "len_successor_block_args",
            block.successor_block_args(self.2),
        )
    }
}

/// A whole register allocation problem (options, machine, and function) wrapped
/// up so that it implements [`Serialize`].
///
/// # Example
///
/// ```
/// use regicide::{Input, InputFunction, serialize::SerializeInput};
/// use std::{error::Error, fs::File, io::BufWriter, path::Path};
///
/// // Write the problem out before handing it to `regicide::run`, so that
/// // whatever the allocator does with it can be replayed later.
/// fn dump_json(input: &Input<'_, impl InputFunction>, path: &Path) -> Result<(), Box<dyn Error>> {
///     let file = BufWriter::new(File::create(path)?);
///     let input = SerializeInput::new(input);
///     serde_json::to_writer(file, &input)?;
///     Ok(())
/// }
/// ```
pub struct SerializeInput<'a, 'b, F>(&'a Input<'b, F>)
where
    F: InputFunction;

impl<'a, 'b, F> SerializeInput<'a, 'b, F>
where
    F: InputFunction,
{
    /// Wrap `input` up for serialization.
    pub fn new(input: &'a Input<'b, F>) -> Self {
        SerializeInput(input)
    }
}

impl<F> Serialize for SerializeInput<'_, '_, F>
where
    F: InputFunction,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        WireInput {
            options: self.0.options,
            machine: self.0.machine,
            func: SerializeFunction::new(self.0.func),
        }
        .serialize(serializer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{OperandConstraint, test::*};

    /// Changing this is a wire-format change; bump `ENCODING_FORMAT_VERSION`.
    #[test]
    fn json_snapshot() {
        let input = TestInput::with_use_constraints(&[OperandConstraint::Any]);
        let json = input
            .with_input(|input| serde_json::to_string_pretty(&SerializeInput::new(input)).unwrap());
        assert_eq!(
            json,
            r#"{
  "options": {
    "validate_input": true,
    "redundant_move_elimination_level": "global",
    "dead_move_elimination_level": "global",
    "eliminate_dead_register_moves": true
  },
  "machine": {
    "version": 3,
    "banks": [
      {
        "size": 8
      }
    ],
    "registers": [
      {
        "bank": 0,
        "units": {
          "start": 0,
          "end": 1
        }
      },
      {
        "bank": 0,
        "units": {
          "start": 1,
          "end": 2
        }
      }
    ],
    "groups": [],
    "classes": [
      {
        "bank": 0,
        "spill_cost": 1.0,
        "members": {
          "regs": [
            0
          ]
        }
      },
      {
        "bank": 0,
        "spill_cost": 1.0,
        "members": {
          "regs": [
            1
          ]
        }
      },
      {
        "bank": 0,
        "spill_cost": 1.0,
        "members": {
          "regs": [
            0,
            1
          ]
        }
      }
    ]
  },
  "func": {
    "version": 3,
    "entry_block": 0,
    "values": [
      {
        "reg_class": 2,
        "remat_cost": null
      }
    ],
    "insts": [
      {
        "block": 0,
        "operands": [
          {
            "pos": "late",
            "kind": "def",
            "constraint": "any",
            "val": 0
          }
        ],
        "clobbers": []
      },
      {
        "block": 0,
        "operands": [
          {
            "pos": "early",
            "kind": "use",
            "constraint": "any",
            "val": 0
          }
        ],
        "clobbers": []
      },
      {
        "block": 0,
        "operands": [],
        "clobbers": []
      }
    ],
    "blocks": [
      {
        "frequency": 1.0,
        "params": [],
        "insts": [
          0,
          1,
          2
        ],
        "successors": [],
        "predecessors": []
      }
    ]
  }
}"#,
        );
    }
}
