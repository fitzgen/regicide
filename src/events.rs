//! The event log: what the register allocator did, in order.

use crate::{
    entity::{Block, EntityRepr, Region, Val},
    input::OperandConstraint,
    live_ranges::{LiveBundle, LivePoint, LiveSpan, Use},
};

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
