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

define_entities! {
    /// An event in the event log.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[allow(dead_code, reason = "only the visualizer names events by index")]
    pub struct EventIndex = "event";
}

/// Why two spans were considered for coalescing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "visualizer", derive(serde::Serialize))]
pub enum Affinity {
    /// A block-call argument and the parameter it is passed to.
    BlockCallArg,

    /// A definition tied to one of its own operands.
    ReuseOperand,

    /// The two pieces on either side of a reuse split.
    ReuseSplit,

    /// A value flowing along a control-flow edge.
    CrossEdge,
}

/// Why a coalesce was refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "visualizer", derive(serde::Serialize))]
pub enum RefusedReason {
    /// The two sets' uses want disjoint locations.
    ConstraintConflict,

    /// The two sets hold spans that are live at the same time.
    Overlap,
}

/// Which kind of split was attempted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "visualizer", derive(serde::Serialize))]
pub enum SplitKind {
    /// Cutting a bundle between two of its spans.
    BetweenSpans,

    /// Cutting a bundle between two uses inside one of its spans.
    WithinSpan,
}

/// Why a scratch location was needed while sequentializing a batch of moves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "visualizer", derive(serde::Serialize))]
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
    not(feature = "visualizer"),
    allow(
        dead_code,
        reason = "without the visualizer an event is only ever `Debug`-formatted for `trace!`"
    )
)]
#[cfg_attr(feature = "visualizer", derive(serde::Serialize))]
#[cfg_attr(feature = "visualizer", serde(tag = "kind"))]
#[cfg_attr(feature = "visualizer", serde(bound = ""))]
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

    /// A span was split because two of its uses' constraints conflict.
    EagerSplit {
        /// The value being split.
        val: Val<E>,
        /// The use whose constraint did not fit.
        at: LivePoint<E>,
        /// The piece that was just flushed.
        before: LiveSpan<E>,
        /// The constraint accumulated over that piece.
        constraint: OperandConstraint,
        /// The constraint that would not merge into it.
        conflicting: OperandConstraint,
    },

    /// A span was split around a definition that overwrites one of its uses.
    ReuseSplit {
        /// The value being split.
        val: Val<E>,
        /// The tied instruction's early half.
        at: LivePoint<E>,
        /// The use the definition ties itself to.
        target_use: Use<E>,
        /// The piece running up to the tie, if it is not empty.
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
        #[cfg_attr(feature = "visualizer", serde(rename = "move"))]
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
pub use self::enabled::EventsLog;
#[cfg(not(feature = "visualizer"))]
pub use crate::events_disabled::EventsLog;

#[cfg(feature = "visualizer")]
mod enabled {
    use super::*;
    use crate::entity::PrimaryMap;

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

        /// Record `event`.
        ///
        /// Panics after `u32::MAX - 1` events, which is well past the point
        /// where a visualization would be useful.
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
        #[allow(dead_code, reason = "not read until commit 05")]
        pub fn iter(&self) -> impl Iterator<Item = (EventIndex, &Event<E>)> {
            self.events.iter()
        }
    }
}

/// Record an event.
///
/// Traces always; logs only under the `visualizer` feature.
macro_rules! event {
    ( $events:expr, $variant:ident { $( $body:tt )* } ) => {{
        let events = &mut *$events;
        let _ = &events;
        if cfg!(any(
            feature = "trace-log",
            debug_assertions,
            feature = "visualizer",
        )) {
            let event = $crate::events::Event::$variant { $( $body )* };
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
