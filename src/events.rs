//! The event log: what the register allocator did, in order.

use crate::{
    entity::{Block, EntityRepr, Region, Val},
    input::OperandConstraint,
    live_ranges::{LiveBundle, LivePoint, LiveSpan, Use},
    machine::{Reg, RegSet},
    move_generation::PackedMovePosition,
    output::EdgeEdit,
    output::RegAllocation,
    output::StackAllocation,
    output::{Allocation, Move, ScalarAllocation},
    parallel_moves::ParallelMove,
    region_allocation::{Phase, Priority},
    spill_slot_allocation::{SpillSlot, SpillSlotGroup, SpillSlotSize},
};
use alloc::vec::Vec;

/// Why two spans were considered for coalescing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
pub enum Affinity {
    /// A block-call argument and the parameter it is passed to.
    BlockCallArg,

    /// A definition tied to one of its own operands.
    ReuseOperand,

    /// The two pieces on either side of an overwrite split.
    OverwriteSplit,

    /// A value flowing along a control-flow edge.
    CrossEdge,
}

/// Why a coalesce was refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
pub enum RefusedReason {
    /// The two sets' uses want disjoint locations.
    ConstraintConflict,

    /// The two sets hold spans that are live at the same time.
    Overlap,
}

/// Which kind of split was attempted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
pub enum SplitKind {
    /// Cutting a bundle between two of its spans.
    BetweenSpans,

    /// Cutting a bundle between two uses inside one of its spans.
    WithinSpan,
}

/// Why a scratch location was needed while sequentializing a batch of moves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
pub enum ScratchReason {
    /// Neither end of the move is a register, and the machine cannot move
    /// memory to memory directly.
    StackToStack,

    /// The move is part of a cycle, which has to be broken somewhere.
    CycleBreak,
}

/// Something the register allocator did.
#[derive(Debug)]
#[cfg_attr(
    not(any(feature = "visualizer", feature = "serialize")),
    expect(
        dead_code,
        reason = "without the visualizer or serialization an event is only ever \
                  `Debug`-formatted for `trace!`"
    )
)]
#[cfg_attr(feature = "serialize", derive(serde::Serialize))]
#[cfg_attr(feature = "serialize", serde(tag = "kind"))]
#[cfg_attr(feature = "serialize", serde(bound = ""))]
pub enum Event<E>
where
    E: EntityRepr,
{
    /// A live span was created.
    SpanConstructed {
        /// The new span.
        span: LiveSpan<E>,
        /// The value it holds.
        val: Val<E>,
        /// Where it begins.
        start: LivePoint<E>,
        /// Where it ends, exclusive.
        end: LivePoint<E>,
        /// The block it lies within.
        block: Block<E>,
        /// How many uses it covers.
        num_uses: usize,
        /// The merged constraint of those uses.
        constraint: OperandConstraint,
        /// Does some use demand one particular register?
        has_fixed_use: bool,
    },

    /// A span was split where carrying one more use would have cost the uses
    /// before it their location: either the two constraints do not merge at
    /// all, or they merge only onto the stack.
    EagerSplit {
        /// The value being split.
        val: Val<E>,
        /// The use whose constraint did not fit.
        at: LivePoint<E>,
        /// The piece that was just flushed.
        before: LiveSpan<E>,
        /// The constraint accumulated over that piece.
        constraint: OperandConstraint,
        /// The constraint that would not merge into it, or would only merge
        /// into it on the stack.
        conflicting: OperandConstraint,
    },

    /// A span was split around a definition that overwrites one of its uses.
    ///
    /// Either a definition tied to that use by a `Reuse`, or one pinned to the
    /// single register the use is pinned to.
    OverwriteSplit {
        /// The value being split.
        val: Val<E>,
        /// The overwriting instruction's early half.
        at: LivePoint<E>,
        /// The use whose register the definition takes.
        target_use: Use<E>,
        /// The piece running up to that use, if it is not empty.
        before: Option<LiveSpan<E>>,
        /// The one-point span that exists only to be overwritten.
        copy: LiveSpan<E>,
    },

    /// Two spans were merged into the same set.
    SpansCoalesced {
        /// One span.
        a: LiveSpan<E>,
        /// The other.
        b: LiveSpan<E>,
        /// Why they were considered.
        affinity: Affinity,
    },

    /// Two spans were considered and refused.
    CoalesceRefused {
        /// One span.
        a: LiveSpan<E>,
        /// The other.
        b: LiveSpan<E>,
        /// Why they were considered.
        affinity: Affinity,
        /// Why they were refused.
        reason: RefusedReason,
    },

    /// An affinity crossed a region boundary, so it became a hint instead.
    CrossRegionAffinity {
        /// One span.
        a: LiveSpan<E>,
        /// The other.
        b: LiveSpan<E>,
    },

    /// A bundle was formed out of a merged span set.
    BundleConstructed {
        /// The new bundle.
        bundle: LiveBundle<E>,
        /// The region it is allocated within.
        region: Region<E>,
        /// How many spans it holds.
        num_spans: usize,
        /// How many distinct values those spans hold.
        num_vals: usize,
        /// The merged constraint of all of its uses.
        constraint: OperandConstraint,
    },

    /// A bundle was pushed onto the allocation queue.
    BundleQueued {
        /// The bundle.
        bundle: LiveBundle<E>,
        /// The region it is allocated within.
        region: Region<E>,
        /// Its priority.
        priority: Priority,
        /// The phase it will be processed in.
        phase: Phase,
    },

    /// A bundle was popped off the allocation queue.
    BundleQueuePopped {
        /// The bundle.
        bundle: LiveBundle<E>,
        /// The region it is allocated within.
        region: Region<E>,
        /// Its priority.
        priority: Priority,
        /// The phase it is being processed in.
        phase: Phase,
    },

    /// A bundle got one of the registers it was hinted towards.
    BundleAssignedPreferred {
        /// The bundle.
        bundle: LiveBundle<E>,
        /// What it got.
        alloc: RegAllocation<E>,
    },

    /// A bundle got a register it was not hinted towards.
    BundleAssignedNonPreferred {
        /// The bundle.
        bundle: LiveBundle<E>,
        /// What it got.
        alloc: RegAllocation<E>,
        /// What it wanted and did not get.
        preference: RegSet,
    },

    /// A bundle got a register only by throwing another bundle out of it.
    BundleAssignedViaEviction {
        /// The bundle.
        bundle: LiveBundle<E>,
        /// What it got.
        alloc: RegAllocation<E>,
        /// The bundle it displaced.
        evicted: LiveBundle<E>,
    },

    /// A bundle lost its register to a higher-priority bundle.
    BundleEvicted {
        /// The victim.
        bundle: LiveBundle<E>,
        /// The bundle that took its register.
        by: LiveBundle<E>,
        /// The register that changed hands.
        alloc: RegAllocation<E>,
    },

    /// A bundle was cut in two between two of its spans.
    BundleSplitBetweenSpans {
        /// The bundle, which keeps the spans before the cut.
        bundle: LiveBundle<E>,
        /// The new bundle holding the spans after it.
        suffix: LiveBundle<E>,
        /// Where the suffix begins.
        at: LivePoint<E>,
        /// Which of the bundle's spans the suffix begins at.
        index: usize,
    },

    /// A bundle was cut in two inside one of its spans.
    BundleSplitWithinSpan {
        /// The bundle, which keeps everything before the cut.
        bundle: LiveBundle<E>,
        /// The new bundle holding everything after it.
        suffix: LiveBundle<E>,
        /// The span that was cut.
        span: LiveSpan<E>,
        /// Where it was cut.
        at: LivePoint<E>,
    },

    /// A split phase found nothing it was allowed to cut.
    BundleSplitFailed {
        /// The bundle.
        bundle: LiveBundle<E>,
        /// The kind of cut that was not available. Not named `kind`, which
        /// the serialized form uses for the event's own name.
        split: SplitKind,
    },

    /// A bundle was shredded into minimal pieces, as the last thing to try
    /// before spilling.
    BundleSplitIntoMinimal {
        /// The bundle, which keeps the first piece.
        bundle: LiveBundle<E>,
        /// How many bundles it became, counting that first piece.
        num_pieces: usize,
    },

    /// A bundle will live in memory rather than in a register.
    BundleSpilledToStack {
        /// The bundle.
        bundle: LiveBundle<E>,
        /// The region it is allocated within.
        region: Region<E>,
        /// Was it a constraint that put it there, rather than a failure to
        /// find it a register?
        forced: bool,
    },

    /// A bundle will live nowhere at all: it has no uses of its own, and
    /// recomputing its values beats reloading them from a slot.
    BundleRematerialized {
        /// The bundle.
        bundle: LiveBundle<E>,
        /// The region it was being allocated within.
        region: Region<E>,
    },

    /// A bundle was biased towards a set of registers.
    BundleHint {
        /// The bundle.
        bundle: LiveBundle<E>,
        /// The registers it is now biased towards.
        hint: RegSet,
        /// The bundle in the region below that wanted the same registers, if
        /// the hint crossed a region boundary.
        from: Option<LiveBundle<E>>,
    },

    /// A bundle came from splitting another one.
    ///
    /// The only record of bundle parentage: nothing in the bundle itself says
    /// where it came from.
    BundleSplit {
        /// The bundle that was split, which keeps the first piece.
        parent: LiveBundle<E>,
        /// The new bundle holding the second piece.
        child: LiveBundle<E>,
        /// The region both are allocated within.
        region: Region<E>,
    },

    /// A stack slot was created.
    SpillSlotCreated {
        /// The new slot.
        slot: SpillSlot<E>,
        /// How many bytes it holds.
        size: SpillSlotSize,
        /// Was it created for move generation to borrow, rather than to be a
        /// spilled value's home?
        emergency: bool,
    },

    /// A group of stack slots was created to hold one value of a register
    /// group class.
    SpillSlotGroupCreated {
        /// The new group.
        group: SpillSlotGroup<E>,
        /// Its slots, in group-member order.
        members: Vec<SpillSlot<E>>,
        /// How many bytes each of them holds.
        size: SpillSlotSize,
    },

    /// A spilled value was given its home on the stack.
    SpillSlotAssigned {
        /// The value.
        val: Val<E>,
        /// Where it lives.
        slot: StackAllocation<E>,
    },

    /// A value will live in memory, because every bundle covering it is on the
    /// stack.
    ValueSpilled {
        /// The value.
        val: Val<E>,
        /// How many of its spans put it there.
        num_spans: usize,
    },

    /// A store of a value into its stack slot was placed.
    SpillPlaced {
        /// The value being stored.
        val: Val<E>,
        /// The span that is live in a register at the store, which is also
        /// what names the bundle the spill is charged to.
        span: LiveSpan<E>,
        /// Where the store goes.
        at: LivePoint<E>,
        /// The block it goes in.
        block: Block<E>,
        /// Where it stores to.
        slot: StackAllocation<E>,
    },

    /// A block where a value may legally be spilled.
    SpillBlockChosen {
        /// The value.
        val: Val<E>,
        /// A block it is live and in a register at the start of.
        block: Block<E>,
        /// How many such blocks it has in total.
        num_candidates: usize,
    },

    /// A span was cut in two by a bundle split.
    ///
    /// The first piece is written over the parent in place, so `first` is
    /// always `parent`; only `second` is a new span.
    SpanSplit {
        /// The span that was cut.
        parent: LiveSpan<E>,
        /// The piece before the cut.
        first: LiveSpan<E>,
        /// The piece after it.
        second: LiveSpan<E>,
        /// Where it was cut.
        at: LivePoint<E>,
        /// The value both pieces hold.
        val: Val<E>,
    },

    /// A value was recorded as available somewhere, so that moves at that
    /// position can read it from there.
    HalfMoveSource {
        /// Where it is available.
        pos: PackedMovePosition<E>,
        /// The value.
        val: Val<E>,
        /// Where it is.
        alloc: Allocation<E>,
        /// The source this one displaced, if it is not the first one here.
        replaced: Option<Allocation<E>>,
    },

    /// A value was recorded as wanted somewhere.
    HalfMoveDest {
        /// Where it is wanted.
        pos: PackedMovePosition<E>,
        /// The value.
        val: Val<E>,
        /// Where it is wanted.
        alloc: Allocation<E>,
    },

    /// A wanted destination was joined with a source, making a whole move.
    MoveResolved {
        /// Where the move goes.
        pos: PackedMovePosition<E>,
        /// The value it moves.
        val: Val<E>,
        /// Where it reads from.
        src: Allocation<E>,
        /// Where it writes to.
        dst: Allocation<E>,
    },

    /// A value was rematerialized instead of moved.
    RematEmitted {
        /// Where it is rematerialized.
        pos: PackedMovePosition<E>,
        /// The value.
        val: Val<E>,
        /// The register it is rematerialized into.
        dest: Reg<E>,
    },

    /// A scratch location was found for a move that could not be done directly.
    ScratchRegChosen {
        /// Where the batch is.
        pos: PackedMovePosition<E>,
        /// The move that needed the scratch.
        mv: ParallelMove<E>,
        /// The scratch location, which is a stack slot when no register was
        /// free.
        scratch: ScalarAllocation<E>,
        /// Why it was needed.
        reason: ScratchReason,
    },

    /// No scratch location could be found, which fails the whole allocation.
    ScratchRegUnavailable {
        /// Where the batch is.
        pos: PackedMovePosition<E>,
        /// The move that needed the scratch.
        mv: ParallelMove<E>,
    },

    /// A position's parallel moves were sequentialized.
    ParallelMoveBatchSolved {
        /// Where the batch is.
        pos: PackedMovePosition<E>,
        /// How many parallel moves went in.
        num_input_moves: usize,
        /// How many sequential moves came out.
        num_solved_moves: usize,
    },

    /// A sequentialized move became an edit.
    MoveEmitted {
        /// Where the move goes.
        pos: PackedMovePosition<E>,
        /// The move.
        #[cfg_attr(feature = "serialize", serde(rename = "move"))]
        move_: Move<E>,
        /// Its index in the finished edit list, so that the visualizer can
        /// map an edit it renders back to the event that made it.
        //
        // Recorded as the position in `self.edits` at the time of emission,
        // then renumbered once the edits are sorted. Stable only because move
        // elimination never removes an edit; if it ever does, add a
        // `MoveEliminated { index }` event and fold it in the visualizer
        // rather than renumbering again here.
        index: usize,
    },

    /// An edit was placed on a critical edge, which the client has to split.
    CriticalEdgeEdit {
        /// The predecessor the edge leaves.
        pred: Block<E>,
        /// Which of the predecessor's successors it is.
        succ: usize,
        /// The successor the edge enters.
        target: Block<E>,
        /// What goes on the edge.
        edit: EdgeEdit<E>,
    },
}

#[cfg(feature = "visualizer")]
pub use self::viz_enabled::*;
#[cfg(feature = "visualizer")]
mod viz_enabled {
    use super::*;
    use crate::{
        entity::{Entity, Inst, PrimaryMap},
        machine::{RegClass, RegGroup},
        move_generation::MovePosition,
        output::Remat,
        visualizer::schema::{
            ALLOCATION, CONSTRAINT, Descriptor, EDGE_EDIT, MOVE, MOVE_POSITION, PARALLEL_MOVE,
            REG_ALLOCATION, REG_SET, SCALAR_ALLOCATION, STACK_ALLOCATION,
        },
    };

    define_entities! {
        /// An event in the event log.
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct EventIndex = "event";
    }

    /// An entity that an event names, for the visualizer's per-entity event
    /// index.
    ///
    /// The machine-level kinds are not generic over `E`: registers, register
    /// groups, and register classes come from the machine description, which one
    /// entity representation does not narrow.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub(crate) enum EntityRef<E>
    where
        E: EntityRepr,
    {
        /// A value.
        Val(Val<E>),

        /// A live span.
        Span(LiveSpan<E>),

        /// A live bundle.
        Bundle(LiveBundle<E>),

        /// A basic block.
        Block(Block<E>),

        /// A region of the region tree.
        Region(Region<E>),

        /// An instruction.
        Inst(Inst<E>),

        /// A use of a value.
        Use(Use<E>),

        /// A stack slot.
        SpillSlot(SpillSlot<E>),

        /// A group of stack slots.
        SpillSlotGroup(SpillSlotGroup<E>),

        /// A register.
        Reg(Reg),

        /// A register group.
        RegGroup(RegGroup),

        /// A register class.
        RegClass(RegClass),
    }

    impl<E> Event<E>
    where
        E: EntityRepr,
    {
        /// This event's name, which is also its serialized `kind` tag.
        ///
        /// The match has no `_` arm, so a new variant does not get to keep the
        /// wrong name.
        pub(crate) fn kind(&self) -> &'static str {
            match self {
                Self::SpanConstructed { .. } => "SpanConstructed",
                Self::EagerSplit { .. } => "EagerSplit",
                Self::OverwriteSplit { .. } => "OverwriteSplit",
                Self::SpansCoalesced { .. } => "SpansCoalesced",
                Self::CoalesceRefused { .. } => "CoalesceRefused",
                Self::CrossRegionAffinity { .. } => "CrossRegionAffinity",
                Self::BundleConstructed { .. } => "BundleConstructed",
                Self::BundleQueued { .. } => "BundleQueued",
                Self::BundleQueuePopped { .. } => "BundleQueuePopped",
                Self::BundleAssignedPreferred { .. } => "BundleAssignedPreferred",
                Self::BundleAssignedNonPreferred { .. } => "BundleAssignedNonPreferred",
                Self::BundleAssignedViaEviction { .. } => "BundleAssignedViaEviction",
                Self::BundleEvicted { .. } => "BundleEvicted",
                Self::BundleSplitBetweenSpans { .. } => "BundleSplitBetweenSpans",
                Self::BundleSplitWithinSpan { .. } => "BundleSplitWithinSpan",
                Self::BundleSplitFailed { .. } => "BundleSplitFailed",
                Self::BundleSplitIntoMinimal { .. } => "BundleSplitIntoMinimal",
                Self::BundleSpilledToStack { .. } => "BundleSpilledToStack",
                Self::BundleRematerialized { .. } => "BundleRematerialized",
                Self::BundleHint { .. } => "BundleHint",
                Self::BundleSplit { .. } => "BundleSplit",
                Self::SpillSlotCreated { .. } => "SpillSlotCreated",
                Self::SpillSlotGroupCreated { .. } => "SpillSlotGroupCreated",
                Self::SpillSlotAssigned { .. } => "SpillSlotAssigned",
                Self::ValueSpilled { .. } => "ValueSpilled",
                Self::SpillPlaced { .. } => "SpillPlaced",
                Self::SpillBlockChosen { .. } => "SpillBlockChosen",
                Self::SpanSplit { .. } => "SpanSplit",
                Self::HalfMoveSource { .. } => "HalfMoveSource",
                Self::HalfMoveDest { .. } => "HalfMoveDest",
                Self::MoveResolved { .. } => "MoveResolved",
                Self::RematEmitted { .. } => "RematEmitted",
                Self::ScratchRegChosen { .. } => "ScratchRegChosen",
                Self::ScratchRegUnavailable { .. } => "ScratchRegUnavailable",
                Self::ParallelMoveBatchSolved { .. } => "ParallelMoveBatchSolved",
                Self::MoveEmitted { .. } => "MoveEmitted",
                Self::CriticalEdgeEdit { .. } => "CriticalEdgeEdit",
            }
        }

        /// Call `f` with every entity this event names.
        ///
        /// Every variant is destructured field by field, with no `..` and no `_`
        /// arm, so that a new variant *or a new field on an existing variant*
        /// fails to compile rather than going quietly unindexed.
        ///
        /// Fields that name no entity — points, weights, counts, ordinals, and
        /// plain enums — contribute nothing, except that a `LivePoint`
        /// contributes the instruction it lies in.
        pub(crate) fn visit_entities(&self, f: &mut impl FnMut(EntityRef<E>)) {
            match self {
                Self::SpanConstructed {
                    span,
                    val,
                    start,
                    end,
                    block,
                    num_uses: _,
                    constraint,
                    has_fixed_use: _,
                } => {
                    f(EntityRef::Span(*span));
                    f(EntityRef::Val(*val));
                    visit_point(*start, f);
                    visit_point(*end, f);
                    f(EntityRef::Block(*block));
                    visit_constraint(*constraint, f);
                }

                Self::EagerSplit {
                    val,
                    at,
                    before,
                    constraint,
                    conflicting,
                } => {
                    f(EntityRef::Val(*val));
                    visit_point(*at, f);
                    f(EntityRef::Span(*before));
                    visit_constraint(*constraint, f);
                    visit_constraint(*conflicting, f);
                }

                Self::OverwriteSplit {
                    val,
                    at,
                    target_use,
                    before,
                    copy,
                } => {
                    f(EntityRef::Val(*val));
                    visit_point(*at, f);
                    f(EntityRef::Use(*target_use));
                    if let Some(before) = *before {
                        f(EntityRef::Span(before));
                    }
                    f(EntityRef::Span(*copy));
                }

                Self::SpansCoalesced { a, b, affinity: _ } => {
                    f(EntityRef::Span(*a));
                    f(EntityRef::Span(*b));
                }

                Self::CoalesceRefused {
                    a,
                    b,
                    affinity: _,
                    reason: _,
                } => {
                    f(EntityRef::Span(*a));
                    f(EntityRef::Span(*b));
                }

                Self::CrossRegionAffinity { a, b } => {
                    f(EntityRef::Span(*a));
                    f(EntityRef::Span(*b));
                }

                Self::BundleConstructed {
                    bundle,
                    region,
                    num_spans: _,
                    num_vals: _,
                    constraint,
                } => {
                    f(EntityRef::Bundle(*bundle));
                    f(EntityRef::Region(*region));
                    visit_constraint(*constraint, f);
                }

                Self::BundleQueued {
                    bundle,
                    region,
                    priority: _,
                    phase: _,
                } => {
                    f(EntityRef::Bundle(*bundle));
                    f(EntityRef::Region(*region));
                }

                Self::BundleQueuePopped {
                    bundle,
                    region,
                    priority: _,
                    phase: _,
                } => {
                    f(EntityRef::Bundle(*bundle));
                    f(EntityRef::Region(*region));
                }

                Self::BundleAssignedPreferred { bundle, alloc } => {
                    f(EntityRef::Bundle(*bundle));
                    visit_reg_allocation(*alloc, f);
                }

                Self::BundleAssignedNonPreferred {
                    bundle,
                    alloc,
                    preference,
                } => {
                    f(EntityRef::Bundle(*bundle));
                    visit_reg_allocation(*alloc, f);
                    visit_reg_set(preference, f);
                }

                Self::BundleAssignedViaEviction {
                    bundle,
                    alloc,
                    evicted,
                } => {
                    f(EntityRef::Bundle(*bundle));
                    visit_reg_allocation(*alloc, f);
                    f(EntityRef::Bundle(*evicted));
                }

                Self::BundleEvicted { bundle, by, alloc } => {
                    f(EntityRef::Bundle(*bundle));
                    f(EntityRef::Bundle(*by));
                    visit_reg_allocation(*alloc, f);
                }

                Self::BundleSplitBetweenSpans {
                    bundle,
                    suffix,
                    at,
                    index: _,
                } => {
                    f(EntityRef::Bundle(*bundle));
                    f(EntityRef::Bundle(*suffix));
                    visit_point(*at, f);
                }

                Self::BundleSplitWithinSpan {
                    bundle,
                    suffix,
                    span,
                    at,
                } => {
                    f(EntityRef::Bundle(*bundle));
                    f(EntityRef::Bundle(*suffix));
                    f(EntityRef::Span(*span));
                    visit_point(*at, f);
                }

                Self::BundleSplitFailed { bundle, split: _ } => {
                    f(EntityRef::Bundle(*bundle));
                }

                Self::BundleSplitIntoMinimal {
                    bundle,
                    num_pieces: _,
                } => {
                    f(EntityRef::Bundle(*bundle));
                }

                Self::BundleSpilledToStack {
                    bundle,
                    region,
                    forced: _,
                } => {
                    f(EntityRef::Bundle(*bundle));
                    f(EntityRef::Region(*region));
                }

                Self::BundleRematerialized { bundle, region } => {
                    f(EntityRef::Bundle(*bundle));
                    f(EntityRef::Region(*region));
                }

                Self::BundleHint { bundle, hint, from } => {
                    f(EntityRef::Bundle(*bundle));
                    visit_reg_set(hint, f);
                    if let Some(from) = *from {
                        f(EntityRef::Bundle(from));
                    }
                }

                Self::BundleSplit {
                    parent,
                    child,
                    region,
                } => {
                    f(EntityRef::Bundle(*parent));
                    f(EntityRef::Bundle(*child));
                    f(EntityRef::Region(*region));
                }

                Self::SpillSlotCreated {
                    slot,
                    size: _,
                    emergency: _,
                } => {
                    f(EntityRef::SpillSlot(*slot));
                }

                Self::SpillSlotGroupCreated {
                    group,
                    members,
                    size: _,
                } => {
                    f(EntityRef::SpillSlotGroup(*group));
                    for slot in members {
                        f(EntityRef::SpillSlot(*slot));
                    }
                }

                Self::SpillSlotAssigned { val, slot } => {
                    f(EntityRef::Val(*val));
                    visit_stack_allocation(*slot, f);
                }

                Self::ValueSpilled { val, num_spans: _ } => {
                    f(EntityRef::Val(*val));
                }

                Self::SpillPlaced {
                    val,
                    span,
                    at,
                    block,
                    slot,
                } => {
                    f(EntityRef::Val(*val));
                    f(EntityRef::Span(*span));
                    visit_point(*at, f);
                    f(EntityRef::Block(*block));
                    visit_stack_allocation(*slot, f);
                }

                Self::SpillBlockChosen {
                    val,
                    block,
                    num_candidates: _,
                } => {
                    f(EntityRef::Val(*val));
                    f(EntityRef::Block(*block));
                }

                Self::SpanSplit {
                    parent,
                    first,
                    second,
                    at,
                    val,
                } => {
                    f(EntityRef::Span(*parent));
                    f(EntityRef::Span(*first));
                    f(EntityRef::Span(*second));
                    visit_point(*at, f);
                    f(EntityRef::Val(*val));
                }

                Self::HalfMoveSource {
                    pos,
                    val,
                    alloc,
                    replaced,
                } => {
                    visit_move_position(*pos, f);
                    f(EntityRef::Val(*val));
                    visit_allocation(*alloc, f);
                    if let Some(replaced) = *replaced {
                        visit_allocation(replaced, f);
                    }
                }

                Self::HalfMoveDest { pos, val, alloc } => {
                    visit_move_position(*pos, f);
                    f(EntityRef::Val(*val));
                    visit_allocation(*alloc, f);
                }

                Self::MoveResolved { pos, val, src, dst } => {
                    visit_move_position(*pos, f);
                    f(EntityRef::Val(*val));
                    visit_allocation(*src, f);
                    visit_allocation(*dst, f);
                }

                Self::RematEmitted { pos, val, dest } => {
                    visit_move_position(*pos, f);
                    f(EntityRef::Val(*val));
                    f(EntityRef::Reg(dest.with_repr32()));
                }

                Self::ScratchRegChosen {
                    pos,
                    mv,
                    scratch,
                    reason: _,
                } => {
                    visit_move_position(*pos, f);
                    visit_parallel_move(*mv, f);
                    visit_scalar_allocation(*scratch, f);
                }

                Self::ScratchRegUnavailable { pos, mv } => {
                    visit_move_position(*pos, f);
                    visit_parallel_move(*mv, f);
                }

                Self::ParallelMoveBatchSolved {
                    pos,
                    num_input_moves: _,
                    num_solved_moves: _,
                } => {
                    visit_move_position(*pos, f);
                }

                Self::MoveEmitted {
                    pos,
                    move_,
                    index: _,
                } => {
                    visit_move_position(*pos, f);
                    visit_move(*move_, f);
                }

                Self::CriticalEdgeEdit {
                    pred,
                    succ: _,
                    target,
                    edit,
                } => {
                    f(EntityRef::Block(*pred));
                    f(EntityRef::Block(*target));
                    visit_edge_edit(*edit, f);
                }
            }
        }
    }

    /// The `events` half of the blob's `schema` table: which field of which event
    /// holds which kind of entity.
    ///
    /// Every variant lists *every* field, with the ones that name no entity
    /// spelled `_`, and the expansion feeds that list to a match as exhaustive as
    /// [`Event::visit_entities`]'s. A new variant, or a new field on an existing
    /// variant, is therefore a compile error here as well as there, rather than a
    /// field that quietly stops being a link.
    macro_rules! event_schema {
    ( $(
        $variant:ident { $( $field:ident $( as $name:literal )? : $desc:tt , )* }
    )* ) => {
        /// What each event kind's fields hold.
        pub(crate) const EVENT_SCHEMA: crate::visualizer::schema::Table = &[ $(
            (stringify!($variant), &[ $(
                (event_schema_name!($field $( as $name )?), event_schema_desc!($desc)),
            )* ]),
        )* ];

        /// Never called: it exists so that the field lists above have to be
        /// complete.
        #[allow(dead_code, reason = "a compile-time exhaustiveness check")]
        fn schema_lists_every_field<E>(event: &Event<E>)
        where
            E: EntityRepr,
        {
            match event {
                $( Event::$variant { $( $field: _, )* } => {} )*
            }
        }
    };
}

    /// The name a schema field serializes under, which is its serde name and not
    /// always its Rust name.
    macro_rules! event_schema_name {
        ( $field:ident as $name:literal ) => {
            $name
        };
        ( $field:ident ) => {
            stringify!($field)
        };
    }

    /// One field's descriptor: `_` for a field that names no entity, `[Thing]` for
    /// a list of them, `(EXPR)` for a named composite, and a bare entity type name
    /// otherwise.
    macro_rules! event_schema_desc {
        ( _ ) => {
            None
        };
        ( [$inner:ident] ) => {
            Some(Descriptor::List(&Descriptor::Entity(stringify!($inner))))
        };
        ( ($descriptor:expr) ) => {
            Some($descriptor)
        };
        ( $kind:ident ) => {
            Some(Descriptor::Entity(stringify!($kind)))
        };
    }

    event_schema! {
        SpanConstructed {
            span: LiveSpan,
            val: Val,
            start: _,
            end: _,
            block: Block,
            num_uses: _,
            constraint: (CONSTRAINT),
            has_fixed_use: _,
        }
        EagerSplit {
            val: Val,
            at: _,
            before: LiveSpan,
            constraint: (CONSTRAINT),
            conflicting: (CONSTRAINT),
        }
        OverwriteSplit {
            val: Val,
            at: _,
            target_use: Use,
            before: LiveSpan,
            copy: LiveSpan,
        }
        SpansCoalesced {
            a: LiveSpan,
            b: LiveSpan,
            affinity: _,
        }
        CoalesceRefused {
            a: LiveSpan,
            b: LiveSpan,
            affinity: _,
            reason: _,
        }
        CrossRegionAffinity {
            a: LiveSpan,
            b: LiveSpan,
        }
        BundleConstructed {
            bundle: LiveBundle,
            region: Region,
            num_spans: _,
            num_vals: _,
            constraint: (CONSTRAINT),
        }
        BundleQueued {
            bundle: LiveBundle,
            region: Region,
            priority: _,
            phase: _,
        }
        BundleQueuePopped {
            bundle: LiveBundle,
            region: Region,
            priority: _,
            phase: _,
        }
        BundleAssignedPreferred {
            bundle: LiveBundle,
            alloc: (REG_ALLOCATION),
        }
        BundleAssignedNonPreferred {
            bundle: LiveBundle,
            alloc: (REG_ALLOCATION),
            preference: (REG_SET),
        }
        BundleAssignedViaEviction {
            bundle: LiveBundle,
            alloc: (REG_ALLOCATION),
            evicted: LiveBundle,
        }
        BundleEvicted {
            bundle: LiveBundle,
            by: LiveBundle,
            alloc: (REG_ALLOCATION),
        }
        BundleSplitBetweenSpans {
            bundle: LiveBundle,
            suffix: LiveBundle,
            at: _,
            index: _,
        }
        BundleSplitWithinSpan {
            bundle: LiveBundle,
            suffix: LiveBundle,
            span: LiveSpan,
            at: _,
        }
        BundleSplitFailed {
            bundle: LiveBundle,
            split: _,
        }
        BundleSplitIntoMinimal {
            bundle: LiveBundle,
            num_pieces: _,
        }
        BundleSpilledToStack {
            bundle: LiveBundle,
            region: Region,
            forced: _,
        }
        BundleRematerialized {
            bundle: LiveBundle,
            region: Region,
        }
        BundleHint {
            bundle: LiveBundle,
            hint: (REG_SET),
            from: LiveBundle,
        }
        BundleSplit {
            parent: LiveBundle,
            child: LiveBundle,
            region: Region,
        }
        SpillSlotCreated {
            slot: SpillSlot,
            size: _,
            emergency: _,
        }
        SpillSlotGroupCreated {
            group: SpillSlotGroup,
            members: [SpillSlot],
            size: _,
        }
        SpillSlotAssigned {
            val: Val,
            slot: (STACK_ALLOCATION),
        }
        ValueSpilled {
            val: Val,
            num_spans: _,
        }
        SpillPlaced {
            val: Val,
            span: LiveSpan,
            at: _,
            block: Block,
            slot: (STACK_ALLOCATION),
        }
        SpillBlockChosen {
            val: Val,
            block: Block,
            num_candidates: _,
        }
        SpanSplit {
            parent: LiveSpan,
            first: LiveSpan,
            second: LiveSpan,
            at: _,
            val: Val,
        }
        HalfMoveSource {
            pos: (MOVE_POSITION),
            val: Val,
            alloc: (ALLOCATION),
            replaced: (ALLOCATION),
        }
        HalfMoveDest {
            pos: (MOVE_POSITION),
            val: Val,
            alloc: (ALLOCATION),
        }
        MoveResolved {
            pos: (MOVE_POSITION),
            val: Val,
            src: (ALLOCATION),
            dst: (ALLOCATION),
        }
        RematEmitted {
            pos: (MOVE_POSITION),
            val: Val,
            dest: Reg,
        }
        ScratchRegChosen {
            pos: (MOVE_POSITION),
            mv: (PARALLEL_MOVE),
            scratch: (SCALAR_ALLOCATION),
            reason: _,
        }
        ScratchRegUnavailable {
            pos: (MOVE_POSITION),
            mv: (PARALLEL_MOVE),
        }
        ParallelMoveBatchSolved {
            pos: (MOVE_POSITION),
            num_input_moves: _,
            num_solved_moves: _,
        }
        MoveEmitted {
            pos: (MOVE_POSITION),
            move_ as "move": (MOVE),
            index: _,
        }
        CriticalEdgeEdit {
            pred: Block,
            succ: _,
            target: Block,
            edit: (EDGE_EDIT),
        }
    }

    /// A point names the instruction it lies in; which half of it does not name
    /// anything.
    fn visit_point<E>(point: LivePoint<E>, f: &mut impl FnMut(EntityRef<E>))
    where
        E: EntityRepr,
    {
        f(EntityRef::Inst(point.inst()));
    }

    /// A move position is either a point in a block or an outgoing edge of one;
    /// the edge's `succ` is an ordinal, not an entity.
    fn visit_move_position<E>(pos: PackedMovePosition<E>, f: &mut impl FnMut(EntityRef<E>))
    where
        E: EntityRepr,
    {
        match pos.unpack() {
            MovePosition::Point(point) | MovePosition::Departure(point) => visit_point(point, f),
            MovePosition::CriticalEdge { pred, succ: _ } => f(EntityRef::Block(pred)),
        }
    }

    /// A `Reg` constraint names the class it allows; the rest name nothing.
    fn visit_constraint<E>(constraint: OperandConstraint, f: &mut impl FnMut(EntityRef<E>))
    where
        E: EntityRepr,
    {
        match constraint {
            OperandConstraint::Reg(class) => f(EntityRef::RegClass(class)),
            OperandConstraint::Any | OperandConstraint::Stack | OperandConstraint::Reuse(_) => {}
        }
    }

    /// A set of registers names every one of its members, which is what makes
    /// "who wanted `r3`?" answerable.
    fn visit_reg_set<E>(regs: &RegSet, f: &mut impl FnMut(EntityRef<E>))
    where
        E: EntityRepr,
    {
        for reg in regs.iter() {
            f(EntityRef::Reg(reg));
        }
    }

    fn visit_allocation<E>(alloc: Allocation<E>, f: &mut impl FnMut(EntityRef<E>))
    where
        E: EntityRepr,
    {
        match alloc {
            Allocation::Reg(alloc) => visit_reg_allocation(alloc, f),
            Allocation::Stack(alloc) => visit_stack_allocation(alloc, f),
        }
    }

    fn visit_reg_allocation<E>(alloc: RegAllocation<E>, f: &mut impl FnMut(EntityRef<E>))
    where
        E: EntityRepr,
    {
        match alloc {
            RegAllocation::Reg(reg) => f(EntityRef::Reg(reg.with_repr32())),
            RegAllocation::RegGroup(group) => f(EntityRef::RegGroup(group)),
        }
    }

    fn visit_stack_allocation<E>(alloc: StackAllocation<E>, f: &mut impl FnMut(EntityRef<E>))
    where
        E: EntityRepr,
    {
        match alloc {
            StackAllocation::SpillSlot(slot) => f(EntityRef::SpillSlot(slot)),
            StackAllocation::SpillSlotGroup(group) => f(EntityRef::SpillSlotGroup(group)),
        }
    }

    fn visit_scalar_allocation<E>(alloc: ScalarAllocation<E>, f: &mut impl FnMut(EntityRef<E>))
    where
        E: EntityRepr,
    {
        match alloc {
            ScalarAllocation::Reg(reg) => f(EntityRef::Reg(reg.with_repr32())),
            ScalarAllocation::Stack(slot) => f(EntityRef::SpillSlot(slot)),
        }
    }

    fn visit_parallel_move<E>(mv: ParallelMove<E>, f: &mut impl FnMut(EntityRef<E>))
    where
        E: EntityRepr,
    {
        let ParallelMove { src, dst } = mv;
        visit_scalar_allocation(src, f);
        visit_scalar_allocation(dst, f);
    }

    fn visit_move<E>(move_: Move<E>, f: &mut impl FnMut(EntityRef<E>))
    where
        E: EntityRepr,
    {
        match move_ {
            Move::RegReg { from, to } => {
                f(EntityRef::Reg(from.with_repr32()));
                f(EntityRef::Reg(to.with_repr32()));
            }
            Move::Spill { from, to } => {
                f(EntityRef::Reg(from.with_repr32()));
                f(EntityRef::SpillSlot(to));
            }
            Move::Reload { from, to } => {
                f(EntityRef::SpillSlot(from));
                f(EntityRef::Reg(to.with_repr32()));
            }
        }
    }

    fn visit_edge_edit<E>(edit: EdgeEdit<E>, f: &mut impl FnMut(EntityRef<E>))
    where
        E: EntityRepr,
    {
        match edit {
            EdgeEdit::Move(move_) => visit_move(move_, f),
            EdgeEdit::Remat(Remat { val, dest }) => {
                f(EntityRef::Val(val));
                f(EntityRef::Reg(dest.with_repr32()));
            }
        }
    }

    /// Every event the register allocator recorded, in the order it recorded
    /// them.
    #[derive(Debug, serde::Serialize)]
    #[serde(transparent)]
    #[serde(bound = "")]
    pub struct EventsLog<E>
    where
        E: EntityRepr,
    {
        events: PrimaryMap<EventIndex, Event<E>>,
    }

    impl<E> EventsLog<E>
    where
        E: EntityRepr,
    {
        /// Create a new, empty log.
        pub const fn new() -> Self {
            Self {
                events: PrimaryMap::new(),
            }
        }

        /// Reset the log to its empty state.
        pub fn reset(&mut self) {
            let Self { events } = self;
            events.reset();
        }

        /// Is this log in its reset state?
        pub fn is_reset(&self) -> bool {
            let Self { events } = self;
            events.is_reset()
        }

        /// Record `event` into this log.
        pub fn push(&mut self, event: Event<E>) -> EventIndex {
            self.events.push_unwrap(event)
        }

        /// How many events have been recorded?
        pub fn len(&self) -> usize {
            self.events.len()
        }

        /// Iterate mutably over the events recorded since the log held `from`
        /// events.
        pub fn iter_mut_from(&mut self, from: usize) -> impl Iterator<Item = &mut Event<E>> {
            self.events.as_mut_slice()[from..].iter_mut()
        }

        /// Iterate over the recorded events and their indices.
        pub fn iter(&self) -> impl Iterator<Item = (EventIndex, &Event<E>)> {
            self.events.iter()
        }
    }
}

#[cfg(not(feature = "visualizer"))]
pub use self::viz_disabled::*;
#[cfg(not(feature = "visualizer"))]
mod viz_disabled {
    use crate::entity::EntityRepr;
    use core::marker::PhantomData;

    /// Does nothing, holds nothing.
    #[derive(Debug)]
    pub struct EventsLog<E>(PhantomData<E>)
    where
        E: EntityRepr;

    impl<E> EventsLog<E>
    where
        E: EntityRepr,
    {
        /// Create a new log.
        pub const fn new() -> Self {
            EventsLog(PhantomData)
        }

        /// Reset the log to its empty state.
        pub fn reset(&mut self) {}

        /// Is this log in its reset state?
        pub fn is_reset(&self) -> bool {
            true
        }
    }
}

/// Record an event.
///
/// Traces always; logs only under the `visualizer` feature.
macro_rules! event {
    ( $events:expr, $event:expr ) => {{
        let events = &mut *$events;
        let _ = &events;

        if cfg!(any(
            feature = "trace-log",
            debug_assertions,
            feature = "visualizer",
        )) {
            use $crate::events::Event::*;

            let event = $event;
            $crate::trace!("event: {event:?}");

            #[cfg(feature = "visualizer")]
            events.push(event);
        }
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_log_is_reset() {
        let mut events = EventsLog::<u32>::new();
        assert!(events.is_reset());
        events.reset();
        assert!(events.is_reset());

        #[cfg(feature = "visualizer")]
        assert_eq!(events.len(), 0);
    }
}
