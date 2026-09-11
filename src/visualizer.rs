//! Writing the register allocation visualization HTML.

use crate::{
    context::ContextInner,
    entity::{Block, EntityRepr, Inst, Region, Val, VisualizedEntity},
    events::EventIndex,
    input::{Input, InputFunction},
    live_ranges::{LiveBundle, LiveSpan, Use},
    machine::{Reg, RegBank, RegClass, RegGroup, RegUnit},
    spill_slot_allocation::{SpillSlot, SpillSlotGroup},
};

/// Write a self-contained HTML visualization of `context`'s results to `path`.
pub(crate) fn write_html<E, F>(
    context: &ContextInner<E>,
    input: &Input<'_, F>,
    path: &std::path::Path,
) -> std::io::Result<()>
where
    E: EntityRepr,
    F: InputFunction,
{
    let _ = (context, input, path);
    todo!("commit 07")
}

#[allow(dead_code, reason = "the table it builds is emitted in commit 07")]
const fn kind<T: VisualizedEntity>() -> (&'static str, &'static str) {
    (T::KIND, T::PREFIX)
}

/// The entity types the visualizer names, and nothing else: the macros also
/// declare cursor and storage-index types that nobody will ever search for.
macro_rules! entity_kinds {
    ( $( $ty:ty ),* $(,)? ) => {
        #[allow(dead_code, reason = "emitted as `entityKinds` in commit 07")]
        const ENTITY_KINDS: &[(&str, &str)] = &[ $( kind::<$ty>() ),* ];

        #[cfg(test)]
        const ENTITY_KIND_DEBUG_CHECKS: &[fn()] = &[ $( debug_matches_prefix::<$ty> ),* ];
    };
}

entity_kinds! {
    Val<u32>,
    Block<u32>,
    Inst<u32>,
    Region<u32>,
    LiveSpan<u32>,
    LiveBundle<u32>,
    Use<u32>,
    SpillSlot<u32>,
    SpillSlotGroup<u32>,
    Reg<u32>,
    RegUnit,
    RegGroup,
    RegClass,
    RegBank,
    EventIndex,
}

#[cfg(test)]
fn debug_matches_prefix<T: VisualizedEntity>() {
    use std::format;
    let e = T::try_new(3).unwrap();
    assert_eq!(format!("{e:?}"), format!("{}3", T::PREFIX));
}

#[cfg(test)]
mod tests {
    use super::*;

    /// If a prefix ever drifts from the `Debug` impl the rest of the crate
    /// uses, the visualizer's labels start lying.
    #[test]
    fn entity_kinds_match_debug_impls() {
        for check in ENTITY_KIND_DEBUG_CHECKS {
            check();
        }
    }

    #[test]
    fn entity_kinds_are_unique() {
        for (i, (kind, _)) in ENTITY_KINDS.iter().enumerate() {
            assert!(
                !ENTITY_KINDS[..i].iter().any(|(k, _)| k == kind),
                "duplicate entity kind {kind}"
            );
        }
    }
}
