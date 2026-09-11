//! The event log: what the register allocator did, in order.

define_entities! {
    /// An event in the event log.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[allow(dead_code, reason = "only the visualizer names events by index")]
    pub struct EventIndex = "event";
}

/// Something the register allocator did.
#[derive(Debug)]
#[allow(dead_code, reason = "no variants until commit 01")]
#[cfg_attr(feature = "visualizer", derive(serde::Serialize))]
#[cfg_attr(feature = "visualizer", serde(tag = "kind"))]
pub enum Event {}

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
    pub struct EventsLog {
        events: PrimaryMap<EventIndex, Event>,
    }

    impl EventsLog {
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
        #[allow(dead_code, reason = "no `Event` variants exist yet")]
        pub fn push(&mut self, event: Event) -> EventIndex {
            self.events.push_unwrap(event)
        }

        /// How many events have been recorded?
        #[allow(dead_code, reason = "not read until commit 05")]
        pub fn len(&self) -> usize {
            self.events.len()
        }

        /// Iterate over the recorded events and their indices.
        #[allow(dead_code, reason = "not read until commit 05")]
        pub fn iter(&self) -> impl Iterator<Item = (EventIndex, &Event)> {
            self.events.iter()
        }
    }
}

/// Record an event.
///
/// Traces always; logs only under the `visualizer` feature.
#[allow(unused_macros, reason = "no events are recorded until commit 01")]
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
        let mut events = EventsLog::new();
        assert!(events.is_reset());
        events.reset();
        assert!(events.is_reset());

        #[cfg(feature = "visualizer")]
        assert_eq!(events.len(), 0);
    }
}
