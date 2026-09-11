//! A zero-sized stand-in for `EventsLog`, so that signatures need no `cfg`.

/// Does nothing, holds nothing.
#[derive(Debug)]
pub struct EventsLog;

impl EventsLog {
    /// Create a new log.
    pub const fn new() -> Self {
        EventsLog
    }

    /// Reset the log to its empty state.
    pub fn reset(&mut self) {}

    /// Is this log in its reset state?
    pub fn is_reset(&self) -> bool {
        true
    }
}

const _: () = assert!(core::mem::size_of::<EventsLog>() == 0);
