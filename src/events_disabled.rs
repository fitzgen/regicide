//! A zero-sized stand-in for `EventsLog`, so that signatures need no `cfg`.

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

const _: () = assert!(core::mem::size_of::<EventsLog<u32>>() == 0);
