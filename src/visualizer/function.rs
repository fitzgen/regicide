//! The IR skeleton and the register file.
//!
//! Everything the function pane and the details pane draw, built once from
//! the final allocation state: the input function, the machine description,
//! and the passes' results.
//!
//! Every array here is indexed by its entity's index — `blocks[3]` is
//! `block3` — and every cross-reference is a bare index, typed by the
//! [`schema`](super::schema) halves at the bottom of this file. There is no
//! `id` field anywhere: the position is the index, and a second copy of it
//! would be one more thing that can disagree with itself.

use super::{
    index::{Index, SpanParent},
    schema::{self, Descriptor, Table},
};
use crate::{
    OperandConstraint,
    context::ContextInner,
    entity::{Block, Entity, EntityRepr, Inst, Region, SecondaryMap, Val},
    input::{BlockFrequency, DefUse, Input, InputBlock, InputFunction, InputInst, Position},
    live_ranges::{LiveBundle, LivePoint, LiveSpan, Use},
    machine::{Machine, Reg, RegBank, RegClass, RegClassMembers, RegGroup, RegSet},
    move_generation::MovePosition,
    output::{Edit, RegAllocation},
    spill_slot_allocation::{SpillSlot, SpillSlotGroup},
};
use alloc::vec::Vec;

/// `serde_json` refuses to write a NaN or an infinity, which would turn a
/// debugging aid into a failed write. Every float in the blob goes through
/// here first.
fn finite(x: f32) -> f32 {
    if x.is_finite() { x } else { 0.0 }
}

/// The register file: what a register, class, group, or bank *is*, so that the
/// details pane can answer "what is `r3`?" rather than printing a label.
#[derive(Debug, serde::Serialize)]
pub(crate) struct MachineInfo {
    /// Every register bank.
    banks: Vec<BankInfo>,

    /// Every register class, the ones `MachineBuilder::finish` derived
    /// included.
    classes: Vec<ClassInfo>,

    /// Every register.
    regs: Vec<RegInfo>,

    /// Every register group.
    #[serde(rename = "regGroups")]
    reg_groups: Vec<RegGroupInfo>,
}

/// One register bank.
#[derive(Debug, serde::Serialize)]
struct BankInfo {
    /// The classes that belong to this bank.
    classes: Vec<RegClass>,

    /// The registers that belong to this bank.
    regs: Vec<Reg>,

    /// The subset of them that may never be allocated.
    #[serde(rename = "nonAllocatable")]
    non_allocatable: Vec<Reg>,

    /// The size in bytes of a spill slot holding one of them.
    size: u16,
}

/// One register class.
#[derive(Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
struct ClassInfo {
    /// The bank this class belongs to.
    bank: RegBank,

    /// The class's registers, in allocation-preference order, for a class of
    /// single registers.
    regs: Vec<Reg>,

    /// The class's register groups, in allocation-preference order, for a
    /// class of groups.
    groups: Vec<RegGroup>,

    /// Is this a class of register groups rather than of single registers?
    is_group: bool,

    /// How much spilling a value of this class costs.
    spill_cost: f32,

    /// Did the user define this class, or did `MachineBuilder::finish` derive
    /// it as an intersection of two that the user defined?
    derived: bool,
}

/// One register.
#[derive(Debug, serde::Serialize)]
struct RegInfo {
    /// The bank this register belongs to.
    bank: RegBank,

    /// The classes it is a member of.
    classes: Vec<RegClass>,

    /// The groups it is a member of.
    groups: Vec<RegGroup>,

    /// Can it be allocated, or is it one of the machine's reserved registers?
    allocatable: bool,
}

/// One register group.
#[derive(Debug, serde::Serialize)]
struct RegGroupInfo {
    /// The bank this group belongs to.
    bank: RegBank,

    /// Its registers, in order.
    members: Vec<Reg>,
}

impl MachineInfo {
    /// Describe `machine`.
    pub(crate) fn new(machine: &Machine) -> Self {
        let regs = Vec::from_iter(machine.regs().map(|reg| {
            RegInfo {
                bank: reg.bank(machine),
                classes: Vec::from_iter(
                    machine
                        .reg_classes()
                        .filter(|class| class.member_set(machine).contains(reg)),
                ),
                groups: Vec::from_iter(
                    machine
                        .reg_groups()
                        .filter(|group| group.member_set(machine).contains(reg)),
                ),
                allocatable: reg.is_allocatable(machine),
            }
        }));

        let classes = Vec::from_iter(machine.reg_classes().map(|class| {
            let (regs, groups) = match class.members(machine) {
                RegClassMembers::Regs(regs) => (Vec::from(&**regs), Vec::new()),
                RegClassMembers::Groups(groups) => (Vec::new(), Vec::from(&**groups)),
            };
            ClassInfo {
                bank: class.bank(machine),
                is_group: !groups.is_empty(),
                regs,
                groups,
                spill_cost: finite(class.spill_cost(machine)),
                derived: class.index() >= machine.num_user_classes(),
            }
        }));

        let reg_groups = Vec::from_iter(machine.reg_groups().map(|group| RegGroupInfo {
            bank: group.bank(machine),
            members: Vec::from(group.members(machine)),
        }));

        let banks = Vec::from_iter(machine.reg_banks().map(|bank| {
            BankInfo {
                classes: Vec::from_iter(
                    machine
                        .reg_classes()
                        .filter(|class| class.bank(machine) == bank),
                ),
                regs: Vec::from_iter(bank.registers(machine).iter()),
                non_allocatable: Vec::from_iter(bank.non_allocatable(machine).iter()),
                size: bank.size(machine).size(),
            }
        }));

        MachineInfo {
            banks,
            classes,
            regs,
            reg_groups,
        }
    }
}

/// The function, as allocated.
#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
#[serde(rename_all = "camelCase")]
pub(crate) struct FunctionInfo<E>
where
    E: EntityRepr,
{
    /// Every block.
    blocks: Vec<BlockInfo<E>>,

    /// Every instruction.
    insts: Vec<InstInfo<E>>,

    /// Every region, with a hole where an index names no region.
    ///
    /// A region is named by the representative of a strongly-connected
    /// component, so the indices are sparse and the array is only long enough
    /// to be indexed by any of them.
    regions: Vec<Option<RegionInfo<E>>>,

    /// Every live span.
    spans: Vec<SpanInfo<E>>,

    /// Every live bundle.
    bundles: Vec<BundleInfo<E>>,

    /// Every use.
    uses: Vec<UseInfo<E>>,

    /// Every stack slot.
    spill_slots: Vec<SpillSlotInfo<E>>,
}

/// How the function pane prefixes a block, decided here so that every consumer
/// agrees.
#[derive(Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
enum BlockKind {
    /// The entry block, whatever its frequency.
    Entry,

    /// A block the embedder said runs about as often as any other.
    Normal,

    /// A block at or below [`BlockFrequency::COLD`].
    Cold,

    /// A block at or above [`BlockFrequency::HOT`].
    Hot,

    /// Anything else, which is shown as its number.
    Freq(f32),
}

/// One block.
#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
#[serde(rename_all = "camelCase")]
struct BlockInfo<E>
where
    E: EntityRepr,
{
    /// How often the embedder says this block runs.
    frequency: f32,

    /// What the function pane prefixes it with.
    kind: BlockKind,

    /// Its successors, in outgoing-edge order.
    successors: Vec<Block<E>>,

    /// Its predecessors.
    predecessors: Vec<Block<E>>,

    /// Its instructions, in program order.
    insts: Vec<Inst<E>>,

    /// Its block parameters.
    params: Vec<Val<E>>,

    /// The arguments it passes along each outgoing edge, in the same order as
    /// `successors`.
    call_args: Vec<Vec<Val<E>>>,

    /// The values live on entry.
    live_in: Vec<Val<E>>,

    /// The values live on exit.
    live_out: Vec<Val<E>>,

    /// The spans that reach the block's start, recomputed from the final
    /// spans rather than read out of `Block::live_in_spans`, which is stale
    /// once anything has been split.
    live_in_spans: Vec<LiveSpan<E>>,

    /// The spans that reach the block's end, recomputed the same way.
    live_out_spans: Vec<LiveSpan<E>>,

    /// The edits move generation put on this block's outgoing critical edges,
    /// which belong to no instruction.
    edge_edits: Vec<EdgeEditInfo<E>>,
}

/// One edit on a critical edge leaving a block.
#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
struct EdgeEditInfo<E>
where
    E: EntityRepr,
{
    /// Which of the block's outgoing edges it sits on.
    succ: usize,

    /// What to do there.
    edit: Edit<E>,
}

/// One instruction.
#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
struct InstInfo<E>
where
    E: EntityRepr,
{
    /// The block it belongs to.
    block: Block<E>,

    /// Its operands, in operand order.
    operands: Vec<OperandInfo<E>>,

    /// The edits move generation put in the gaps around it.
    edits: Vec<PointEditInfo<E>>,
}

/// One operand.
#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
#[serde(rename_all = "camelCase")]
struct OperandInfo<E>
where
    E: EntityRepr,
{
    /// The value it names.
    val: Val<E>,

    /// Whether it defines or uses that value.
    def_use: DefUse,

    /// Which half of the instruction it is accessed in.
    pos: Position,

    /// Where the value may be.
    constraint: OperandConstraint,
}

/// One edit at a program point.
#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
struct PointEditInfo<E>
where
    E: EntityRepr,
{
    /// The point it sits at.
    at: LivePoint<E>,

    /// What to do there.
    edit: Edit<E>,
}

/// One region.
#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
struct RegionInfo<E>
where
    E: EntityRepr,
{
    /// The region that encloses it, or `null` for the root.
    parent: Option<Region<E>>,

    /// The regions it immediately encloses.
    children: Vec<Region<E>>,

    /// The blocks that belong to it.
    blocks: Vec<Block<E>>,

    /// The bundles allocated within it.
    bundles: Vec<LiveBundle<E>>,

    /// How far below the root it is.
    depth: u32,
}

/// One live span.
#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
#[serde(rename_all = "camelCase")]
struct SpanInfo<E>
where
    E: EntityRepr,
{
    /// The value that is live over it.
    val: Val<E>,

    /// Where it begins.
    start: LivePoint<E>,

    /// Where it ends.
    end: LivePoint<E>,

    /// The block it lies in; a span never crosses a block boundary.
    block: Block<E>,

    /// The bundle it was placed in, or `null` if it never reached one.
    bundle: Option<LiveBundle<E>>,

    /// Its uses, in ascending program order.
    uses: Vec<Use<E>>,

    /// The merge of its uses' constraints.
    constraint: OperandConstraint,

    /// What it was split out of, if it was.
    parent: Option<SpanParent<E>>,
}

/// One live bundle.
#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
#[serde(rename_all = "camelCase")]
struct BundleInfo<E>
where
    E: EntityRepr,
{
    /// The region it is allocated within.
    region: Region<E>,

    /// Its spans, in ascending program order.
    spans: Vec<LiveSpan<E>>,

    /// Where its spans may go.
    constraint: OperandConstraint,

    /// The registers it would rather have.
    preference: RegSet,

    /// The register it got, or `null` if it went to the stack.
    allocation: Option<RegAllocation<E>>,

    /// How expensive it would be to spill.
    spill_weight: f32,

    /// Is it too small to split any further?
    is_minimal: bool,

    /// What it was split out of, if it was.
    parent: Option<LiveBundle<E>>,
}

/// One use.
#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
struct UseInfo<E>
where
    E: EntityRepr,
{
    /// The span it belongs to.
    span: LiveSpan<E>,

    /// Where it is.
    point: LivePoint<E>,

    /// Which of its instruction's operands it is.
    operand: usize,

    /// How much it contributes to its bundle's spill weight.
    weight: f32,
}

/// One stack slot.
#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
struct SpillSlotInfo<E>
where
    E: EntityRepr,
{
    /// How many bytes it holds.
    size: u16,

    /// Is it one of the slots move generation borrows to break a cycle,
    /// rather than one a value was assigned?
    emergency: bool,

    /// The group it belongs to, if any.
    group: Option<SpillSlotGroup<E>>,
}

impl<E> FunctionInfo<E>
where
    E: EntityRepr,
{
    /// Describe the function `context` allocated.
    pub(crate) fn new(
        input: &Input<'_, impl InputFunction>,
        context: &ContextInner<E>,
        index: &Index<E>,
    ) -> Self {
        let func = input.func;
        let live_ranges = &context.live_ranges;
        let liveness = &context.liveness;
        let region_tree = &context.region_tree;
        let spill_slots = &context.spill_slots;
        let indexes = &index.indexes;

        let widen = |block: Block| {
            block
                .with_repr::<E>()
                .expect("every block index already fit in `E` in the earlier passes")
        };
        let widen_val = |val: Val| {
            val.with_repr::<E>()
                .expect("every value index already fit in `E` in the earlier passes")
        };

        // A span reaches a block boundary only if its value is live across it,
        // and `Block::live_in_spans` is documented as stale once anything has
        // been split, which region allocation has long since done. Recompute.
        let mut live_in_spans = SecondaryMap::<Block<E>, Vec<LiveSpan<E>>>::new(Vec::new());
        let mut live_out_spans = SecondaryMap::<Block<E>, Vec<LiveSpan<E>>>::new(Vec::new());
        for span in live_ranges.spans() {
            let val = span.val(live_ranges);
            let block = span.block(func, live_ranges);
            if span.start(live_ranges) == block.start_point(input)
                && block.is_live_in(liveness, val)
            {
                live_in_spans[block].push(span);
            }
            if span.end(live_ranges) == block.end_point(input) && block.is_live_out(liveness, val) {
                live_out_spans[block].push(span);
            }
        }

        let blocks =
            Vec::from_iter(func.blocks().map(|(block, input_block)| {
                let wide = widen(block);
                let (first, last) = crate::liveness::block_inst_bounds(&input_block);
                let frequency = input_block.frequency();
                BlockInfo {
                    frequency: finite(frequency.as_f32()),
                    kind: block_kind(block, func.entry_block(), frequency),
                    successors: Vec::from_iter(input_block.successors().map(widen)),
                    predecessors: Vec::from_iter(input_block.predecessors().map(widen)),
                    insts: Vec::from_iter(
                        (first.index()..=last.index())
                            .map(|i| Inst::try_new(i).expect("already fit in `E`")),
                    ),
                    params: Vec::from_iter(input_block.params().map(widen_val)),
                    call_args: Vec::from_iter((0..input_block.len_successors()).map(|i| {
                        Vec::from_iter(input_block.successor_block_args(i).map(widen_val))
                    })),
                    live_in: Vec::from_iter(wide.live_in(liveness)),
                    live_out: Vec::from_iter(wide.live_out(liveness)),
                    live_in_spans: live_in_spans[wide].clone(),
                    live_out_spans: live_out_spans[wide].clone(),
                    edge_edits: Vec::from_iter(
                        context.move_generation.block_edge_edits(wide).iter().map(
                            |&(pos, edit)| {
                                let MovePosition::CriticalEdge { succ, .. } = pos.unpack() else {
                                    unreachable!("`block_edge_edits` only yields edge positions")
                                };
                                EdgeEditInfo { succ, edit }
                            },
                        ),
                    ),
                }
            }));

        let insts = Vec::from_iter((0..func.len_insts()).map(|i| {
            let inst = Inst::try_new(i).expect("an instruction index is in bounds");
            let input_inst = func.inst(inst);
            let wide = inst.with_repr::<E>().expect("already fit in `E`");
            InstInfo {
                block: widen(input_inst.block()),
                operands: Vec::from_iter(input_inst.operands().map(|operand| OperandInfo {
                    val: widen_val(operand.val()),
                    def_use: operand.kind(),
                    pos: operand.pos(),
                    constraint: operand.constraint(),
                })),
                edits: Vec::from_iter(
                    context
                        .move_generation
                        .block_point_edits(wide, wide)
                        .iter()
                        .map(|&(pos, edit)| {
                            let MovePosition::Point(at) = pos.unpack() else {
                                unreachable!("`block_point_edits` only yields point positions")
                            };
                            PointEditInfo { at, edit }
                        }),
                ),
            }
        }));

        // `Region::bundles` only covers the bundles coalescing created, so the
        // membership has to come from the bundles themselves.
        let mut region_bundles = SecondaryMap::<Region<E>, Vec<LiveBundle<E>>>::new(Vec::new());
        for bundle in live_ranges.bundles() {
            region_bundles[bundle.region(live_ranges)].push(bundle);
        }

        // A pre-order walk reaches a region only after its parent, so one pass
        // gives every depth. The tree has no depth of its own.
        let mut depths = SecondaryMap::<Region<E>, u32>::new(0);
        let mut regions = Vec::from_iter((0..func.len_blocks()).map(|_| None));
        for region in region_tree.pre_order_iter() {
            let parent = region.parent(region_tree);
            if let Some(parent) = parent {
                depths[region] = depths[parent] + 1;
            }
            regions[region.index()] = Some(RegionInfo {
                parent,
                children: Vec::from_iter(region.children(region_tree)),
                blocks: Vec::from_iter(region.blocks(region_tree)),
                bundles: core::mem::take(&mut region_bundles[region]),
                depth: depths[region],
            });
        }

        let spans = Vec::from_iter(live_ranges.spans().map(|span| SpanInfo {
            val: span.val(live_ranges),
            start: span.start(live_ranges),
            end: span.end(live_ranges),
            block: span.block(func, live_ranges),
            bundle: span.bundle(live_ranges),
            uses: Vec::from_iter(span.uses(live_ranges)),
            constraint: span.constraint(live_ranges, input),
            parent: indexes.span_parent(span),
        }));

        let bundles = Vec::from_iter(live_ranges.bundles().map(|bundle| BundleInfo {
            region: bundle.region(live_ranges),
            spans: Vec::from_iter(bundle.spans(live_ranges)),
            constraint: bundle.constraint(live_ranges),
            preference: bundle.preference(live_ranges).clone(),
            allocation: bundle.reg_allocation(live_ranges),
            spill_weight: finite(bundle.spill_weight(live_ranges)),
            is_minimal: bundle.is_minimal(live_ranges),
            parent: indexes.bundle_parent(bundle),
        }));

        let uses = Vec::from_iter((0..live_ranges.len_uses()).map(|i| {
            let u = Use::try_new(i).expect("a use index is in bounds");
            UseInfo {
                span: u.span(live_ranges),
                point: u.point(live_ranges),
                operand: u.operand(live_ranges),
                weight: finite(u.weight(live_ranges).as_f32()),
            }
        }));

        let mut slot_group = SecondaryMap::<SpillSlot<E>, Option<SpillSlotGroup<E>>>::new(None);
        for group in spill_slots.groups() {
            for &slot in group.members(spill_slots) {
                slot_group[slot] = Some(group);
            }
        }
        let spill_slots_info = Vec::from_iter((0..spill_slots.len_slots()).map(|i| {
            let slot = SpillSlot::try_new(i).expect("a slot index is in bounds");
            SpillSlotInfo {
                size: slot.size(spill_slots).size(),
                emergency: spill_slots.is_emergency(slot),
                group: slot_group[slot],
            }
        }));

        FunctionInfo {
            blocks,
            insts,
            regions,
            spans,
            bundles,
            uses,
            spill_slots: spill_slots_info,
        }
    }
}

/// Which prefix the function pane gives a block.
///
/// The thresholds live here, and not in the JavaScript, so that every consumer
/// of the blob draws the same picture.
fn block_kind(block: Block, entry: Block, frequency: BlockFrequency) -> BlockKind {
    if block == entry {
        BlockKind::Entry
    } else if frequency.is_cold() {
        BlockKind::Cold
    } else if frequency >= BlockFrequency::HOT {
        BlockKind::Hot
    } else if frequency == BlockFrequency::NORMAL {
        BlockKind::Normal
    } else {
        BlockKind::Freq(finite(frequency.as_f32()))
    }
}

/// The `machine` half of the blob's `schema`.
pub(crate) const MACHINE_SCHEMA: Table = &[
    (
        "banks",
        &[
            (
                "classes",
                Some(Descriptor::List(&Descriptor::Entity("RegClass"))),
            ),
            ("regs", Some(Descriptor::List(&Descriptor::Entity("Reg")))),
            (
                "nonAllocatable",
                Some(Descriptor::List(&Descriptor::Entity("Reg"))),
            ),
            ("size", None),
        ],
    ),
    (
        "classes",
        &[
            ("bank", Some(Descriptor::Entity("RegBank"))),
            ("regs", Some(Descriptor::List(&Descriptor::Entity("Reg")))),
            (
                "groups",
                Some(Descriptor::List(&Descriptor::Entity("RegGroup"))),
            ),
            ("isGroup", None),
            ("spillCost", None),
            ("derived", None),
        ],
    ),
    (
        "regs",
        &[
            ("bank", Some(Descriptor::Entity("RegBank"))),
            (
                "classes",
                Some(Descriptor::List(&Descriptor::Entity("RegClass"))),
            ),
            (
                "groups",
                Some(Descriptor::List(&Descriptor::Entity("RegGroup"))),
            ),
            ("allocatable", None),
        ],
    ),
    (
        "regGroups",
        &[
            ("bank", Some(Descriptor::Entity("RegBank"))),
            (
                "members",
                Some(Descriptor::List(&Descriptor::Entity("Reg"))),
            ),
        ],
    ),
];

/// The `function` half of the blob's `schema`.
///
/// Written here, beside the structs above, so that the two are edited
/// together.
pub(crate) const FUNCTION_SCHEMA: Table = &[
    (
        "blocks",
        &[
            ("frequency", None),
            ("kind", None),
            (
                "successors",
                Some(Descriptor::List(&Descriptor::Entity("Block"))),
            ),
            (
                "predecessors",
                Some(Descriptor::List(&Descriptor::Entity("Block"))),
            ),
            ("insts", Some(Descriptor::List(&Descriptor::Entity("Inst")))),
            ("params", Some(Descriptor::List(&Descriptor::Entity("Val")))),
            (
                "callArgs",
                Some(Descriptor::List(&Descriptor::List(&Descriptor::Entity(
                    "Val",
                )))),
            ),
            ("liveIn", Some(Descriptor::List(&Descriptor::Entity("Val")))),
            (
                "liveOut",
                Some(Descriptor::List(&Descriptor::Entity("Val"))),
            ),
            (
                "liveInSpans",
                Some(Descriptor::List(&Descriptor::Entity("LiveSpan"))),
            ),
            (
                "liveOutSpans",
                Some(Descriptor::List(&Descriptor::Entity("LiveSpan"))),
            ),
            // `succ` is an outgoing-edge ordinal, not a block, and typing it
            // would make the page render `block1`.
            ("edgeEdits", Some(Descriptor::List(&EDGE_EDIT_INFO))),
        ],
    ),
    (
        "insts",
        &[
            ("block", Some(Descriptor::Entity("Block"))),
            ("operands", Some(Descriptor::List(&OPERAND))),
            ("edits", Some(Descriptor::List(&POINT_EDIT_INFO))),
        ],
    ),
    (
        "regions",
        &[
            ("parent", Some(Descriptor::Entity("Region"))),
            (
                "children",
                Some(Descriptor::List(&Descriptor::Entity("Region"))),
            ),
            (
                "blocks",
                Some(Descriptor::List(&Descriptor::Entity("Block"))),
            ),
            (
                "bundles",
                Some(Descriptor::List(&Descriptor::Entity("LiveBundle"))),
            ),
            ("depth", None),
        ],
    ),
    (
        "spans",
        &[
            ("val", Some(Descriptor::Entity("Val"))),
            ("start", None),
            ("end", None),
            ("block", Some(Descriptor::Entity("Block"))),
            ("bundle", Some(Descriptor::Entity("LiveBundle"))),
            ("uses", Some(Descriptor::List(&Descriptor::Entity("Use")))),
            ("constraint", Some(schema::CONSTRAINT)),
            ("parent", Some(SPAN_PARENT)),
        ],
    ),
    (
        "bundles",
        &[
            ("region", Some(Descriptor::Entity("Region"))),
            (
                "spans",
                Some(Descriptor::List(&Descriptor::Entity("LiveSpan"))),
            ),
            ("constraint", Some(schema::CONSTRAINT)),
            ("preference", Some(schema::REG_SET)),
            ("allocation", Some(schema::REG_ALLOCATION)),
            ("spillWeight", None),
            ("isMinimal", None),
            ("parent", Some(Descriptor::Entity("LiveBundle"))),
        ],
    ),
    (
        "uses",
        &[
            ("span", Some(Descriptor::Entity("LiveSpan"))),
            ("point", None),
            ("operand", None),
            ("weight", None),
        ],
    ),
    (
        "spillSlots",
        &[
            ("size", None),
            ("emergency", None),
            ("group", Some(Descriptor::Entity("SpillSlotGroup"))),
        ],
    ),
];

/// A `SpanParent`.
const SPAN_PARENT: Descriptor = Descriptor::Fields(&[("parent", Descriptor::Entity("LiveSpan"))]);

/// An `OperandInfo`.
const OPERAND: Descriptor = Descriptor::Fields(&[
    ("val", Descriptor::Entity("Val")),
    ("constraint", schema::CONSTRAINT),
]);

/// A `PointEditInfo`.
const POINT_EDIT_INFO: Descriptor = Descriptor::Fields(&[("edit", schema::EDIT)]);

/// An `EdgeEditInfo`.
const EDGE_EDIT_INFO: Descriptor = Descriptor::Fields(&[("edit", schema::EDIT)]);

#[cfg(test)]
mod tests {
    use super::*;

    /// A weight the allocator computed out of an infinite block frequency has
    /// to reach the page as a number.
    #[test]
    fn non_finite_weights_clamp() {
        // What `finite` is guarding against: `serde_json` writes a JSON
        // `null` for a non-finite float, and `null` is not a number on the
        // other side -- every arithmetic the page does on it yields `NaN`,
        // and no error says why.
        assert_eq!(serde_json::to_string(&f32::INFINITY).unwrap(), "null");

        for weight in [f32::INFINITY, f32::NEG_INFINITY, f32::NAN] {
            assert_eq!(serde_json::to_string(&finite(weight)).unwrap(), "0.0");
        }
    }
}
