use crate::{
    coalescing::Coalescing, counts::Counts, dfs::Dfs, entity::EntityRepr, live_ranges::LiveRanges,
    liveness::Liveness, move_generation::MoveGeneration, region_allocation::RegionAllocation,
    region_tree::RegionTree, rpo::Rpo, spill_placement::SpillPlacement,
    spill_slot_allocation::SpillSlots,
};

/// TODO FITZGEN
pub struct Context {
    #[cfg(feature = "entity-repr-8")]
    pub(crate) context8: ContextInner<u8>,
    #[cfg(feature = "entity-repr-16")]
    pub(crate) context16: ContextInner<u16>,
    pub(crate) context32: ContextInner<u32>,
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

impl Context {
    /// TODO FITZGEN
    pub const fn new() -> Self {
        Self {
            #[cfg(feature = "entity-repr-8")]
            context8: ContextInner::new(),
            #[cfg(feature = "entity-repr-16")]
            context16: ContextInner::new(),
            context32: ContextInner::new(),
        }
    }

    /// TODO FITZGEN
    pub fn reset(&mut self) {
        let Self {
            #[cfg(feature = "entity-repr-8")]
            context8,
            #[cfg(feature = "entity-repr-16")]
            context16,
            context32,
        } = self;
        #[cfg(feature = "entity-repr-8")]
        context8.reset();
        #[cfg(feature = "entity-repr-16")]
        context16.reset();
        context32.reset();
    }

    /// TODO FITZGEN
    pub fn is_reset(&self) -> bool {
        let Self {
            #[cfg(feature = "entity-repr-8")]
            context8,
            #[cfg(feature = "entity-repr-16")]
            context16,
            context32,
        } = self;

        #[cfg(feature = "entity-repr-8")]
        if !context8.is_reset() {
            return false;
        }

        #[cfg(feature = "entity-repr-16")]
        if !context16.is_reset() {
            return false;
        }

        context32.is_reset()
    }
}

pub(crate) struct ContextInner<E: EntityRepr> {
    pub counts: Counts,
    pub rpo: Rpo<E>,
    pub region_tree: RegionTree<E>,
    pub liveness: Liveness<E>,
    pub live_ranges: LiveRanges<E>,
    pub dfs: Dfs<E>,
    pub coalescing: Coalescing<E>,
    pub region_allocation: RegionAllocation<E>,
    pub spill_slots: SpillSlots<E>,
    pub spill_placement: SpillPlacement<E>,
    pub move_generation: MoveGeneration<E>,
}

impl<E: EntityRepr> ContextInner<E> {
    const fn new() -> Self {
        Self {
            counts: Counts::new(),
            rpo: Rpo::new(),
            region_tree: RegionTree::new(),
            liveness: Liveness::new(),
            live_ranges: LiveRanges::new(),
            dfs: Dfs::new(),
            coalescing: Coalescing::new(),
            region_allocation: RegionAllocation::new(),
            spill_slots: SpillSlots::new(),
            spill_placement: SpillPlacement::new(),
            move_generation: MoveGeneration::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            counts,
            rpo,
            region_tree,
            liveness,
            live_ranges,
            dfs,
            coalescing,
            region_allocation,
            spill_slots,
            spill_placement,
            move_generation,
        } = self;
        counts.reset();
        rpo.reset();
        region_tree.reset();
        liveness.reset();
        live_ranges.reset();
        dfs.reset();
        coalescing.reset();
        region_allocation.reset();
        spill_slots.reset();
        spill_placement.reset();
        move_generation.reset();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            counts,
            rpo,
            region_tree,
            liveness,
            live_ranges,
            dfs,
            coalescing,
            region_allocation,
            spill_slots,
            spill_placement,
            move_generation,
        } = self;
        counts.is_reset()
            && rpo.is_reset()
            && region_tree.is_reset()
            && liveness.is_reset()
            && live_ranges.is_reset()
            && dfs.is_reset()
            && coalescing.is_reset()
            && region_allocation.is_reset()
            && spill_slots.is_reset()
            && spill_placement.is_reset()
            && move_generation.is_reset()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn context_is_send_sync() {
        fn assert_send<T: Send>() {}
        fn assert_sync<T: Sync>() {}
        assert_send::<Context>();
        assert_sync::<Context>();
    }
}
