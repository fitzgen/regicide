//! The IR skeleton and the register file.
//!
//! Everything the function pane and the details pane draw, built once from
//! the final allocation state: the input function, the machine description,
//! and the passes' results.

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
    output::{Allocation, Edit, RegAllocation},
    spill_slot_allocation::{SpillSlot, SpillSlotGroup},
};
use alloc::vec::Vec;

fn finite(x: f32) -> f32 {
    if x.is_finite() { x } else { 0.0 }
}

#[derive(Debug, serde::Serialize)]
pub(crate) struct MachineInfo {
    banks: Vec<BankInfo>,
    classes: Vec<ClassInfo>,
    regs: Vec<RegInfo>,
    #[serde(rename = "regGroups")]
    reg_groups: Vec<RegGroupInfo>,
}

#[derive(Debug, serde::Serialize)]
struct BankInfo {
    classes: Vec<RegClass>,
    regs: Vec<Reg>,
    #[serde(rename = "nonAllocatable")]
    non_allocatable: Vec<Reg>,
    size: u16,
}

#[derive(Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
struct ClassInfo {
    bank: RegBank,
    regs: Vec<Reg>,
    groups: Vec<RegGroup>,
    is_group: bool,
    spill_cost: f32,
    derived: bool,
}

#[derive(Debug, serde::Serialize)]
struct RegInfo {
    bank: RegBank,
    classes: Vec<RegClass>,
    groups: Vec<RegGroup>,
    allocatable: bool,
}

#[derive(Debug, serde::Serialize)]
struct RegGroupInfo {
    bank: RegBank,
    members: Vec<Reg>,
}

impl MachineInfo {
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

#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
#[serde(rename_all = "camelCase")]
pub(crate) struct FunctionInfo<E>
where
    E: EntityRepr,
{
    blocks: Vec<BlockInfo<E>>,
    insts: Vec<InstInfo<E>>,
    regions: Vec<Option<RegionInfo<E>>>,
    spans: Vec<SpanInfo<E>>,
    bundles: Vec<BundleInfo<E>>,
    uses: Vec<UseInfo<E>>,
    spill_slots: Vec<SpillSlotInfo<E>>,
}

#[derive(Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
enum BlockKind {
    Entry,
    Normal,
    Cold,
    Hot,
    Freq(f32),
}

#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
#[serde(rename_all = "camelCase")]
struct BlockInfo<E>
where
    E: EntityRepr,
{
    frequency: f32,
    kind: BlockKind,
    successors: Vec<Block<E>>,
    predecessors: Vec<Block<E>>,
    insts: Vec<Inst<E>>,
    params: Vec<Val<E>>,
    call_args: Vec<Vec<Val<E>>>,
    live_in: Vec<Val<E>>,
    live_out: Vec<Val<E>>,
    live_in_spans: Vec<LiveSpan<E>>,
    live_out_spans: Vec<LiveSpan<E>>,
    edge_edits: Vec<EdgeEditInfo<E>>,
}

#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
struct EdgeEditInfo<E>
where
    E: EntityRepr,
{
    succ: usize,
    edit: Edit<E>,
}

#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
struct InstInfo<E>
where
    E: EntityRepr,
{
    block: Block<E>,
    operands: Vec<OperandInfo<E>>,
    edits: Vec<PointEditInfo<E>>,
}

#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
#[serde(rename_all = "camelCase")]
struct OperandInfo<E>
where
    E: EntityRepr,
{
    val: Option<Val<E>>,
    def_use: DefUse,
    pos: Position,
    constraint: OperandConstraint,
}

#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
struct PointEditInfo<E>
where
    E: EntityRepr,
{
    at: LivePoint<E>,
    edit: Edit<E>,
}

#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
struct RegionInfo<E>
where
    E: EntityRepr,
{
    parent: Option<Region<E>>,
    children: Vec<Region<E>>,
    blocks: Vec<Block<E>>,
    bundles: Vec<LiveBundle<E>>,
    depth: u32,
}

#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
#[serde(rename_all = "camelCase")]
struct SpanInfo<E>
where
    E: EntityRepr,
{
    val: Val<E>,
    start: LivePoint<E>,
    end: LivePoint<E>,
    block: Block<E>,
    bundle: Option<LiveBundle<E>>,
    allocation: Option<Allocation<E>>,
    uses: Vec<Use<E>>,
    constraint: OperandConstraint,
    parent: Option<SpanParent<E>>,
}

#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
#[serde(rename_all = "camelCase")]
struct BundleInfo<E>
where
    E: EntityRepr,
{
    region: Region<E>,
    spans: Vec<LiveSpan<E>>,
    constraint: OperandConstraint,
    preference: RegSet,
    allocation: Option<RegAllocation<E>>,
    spill_weight: f32,
    is_minimal: bool,
    parent: Option<LiveBundle<E>>,
}

#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
struct UseInfo<E>
where
    E: EntityRepr,
{
    span: LiveSpan<E>,
    point: LivePoint<E>,
    operand: usize,
    weight: f32,
}

#[derive(Debug, serde::Serialize)]
#[serde(bound = "")]
struct SpillSlotInfo<E>
where
    E: EntityRepr,
{
    size: u16,
    emergency: bool,
    group: Option<SpillSlotGroup<E>>,
}

impl<E> FunctionInfo<E>
where
    E: EntityRepr,
{
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
        let indices = &index.indices;

        let widen = |block: Block| {
            block
                .with_repr::<E>()
                .expect("every block index already fit in `E` in the earlier passes")
        };
        let widen_val = |val: Val| {
            val.with_repr::<E>()
                .expect("every value index already fit in `E` in the earlier passes")
        };

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
                    val: operand.val().map(widen_val),
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

        let spans = Vec::from_iter(live_ranges.spans().map(|span| {
            SpanInfo {
                val: span.val(live_ranges),
                start: span.start(live_ranges),
                end: span.end(live_ranges),
                block: span.block(func, live_ranges),
                bundle: span.bundle(live_ranges),
                allocation: span
                    .bundle(live_ranges)
                    .map(|_| span.allocation(live_ranges, spill_slots)),
                uses: Vec::from_iter(span.uses(live_ranges)),
                constraint: span.constraint(live_ranges, input),
                parent: indices.span_parent(span),
            }
        }));

        let bundles = Vec::from_iter(live_ranges.bundles().map(|bundle| BundleInfo {
            region: bundle.region(live_ranges),
            spans: Vec::from_iter(bundle.spans(live_ranges)),
            constraint: bundle.constraint(live_ranges),
            preference: bundle.preference(live_ranges).clone(),
            allocation: bundle.reg_allocation(live_ranges),
            spill_weight: finite(bundle.spill_weight(live_ranges)),
            is_minimal: bundle.is_minimal(live_ranges),
            parent: indices.bundle_parent(bundle),
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
            ("allocation", Some(schema::ALLOCATION)),
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

const SPAN_PARENT: Descriptor = Descriptor::Fields(&[("parent", Descriptor::Entity("LiveSpan"))]);

const OPERAND: Descriptor = Descriptor::Fields(&[
    ("val", Descriptor::Entity("Val")),
    ("constraint", schema::CONSTRAINT),
]);

const POINT_EDIT_INFO: Descriptor = Descriptor::Fields(&[("edit", schema::EDIT)]);

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
