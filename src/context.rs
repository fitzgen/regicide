use crate::{
    btree::{BTreeSet, BTreeSetArena},
    counts::Counts,
    dfs::Dfs,
    entity::{
        Block, Bundle, Entity, EntityRepr, Inst, LiveRange, PrimaryMap, Region, Scc, SecondaryMap,
        Val,
    },
    live_ranges::{BundleData, LiveRangeData, LiveRanges, ProgramPoint},
    liveness::Liveness,
    output::Allocation,
    region_tree::RegionTree,
    sccs::StronglyConnectedComponents,
    union_find::UnionFind,
};
use alloc::vec::Vec;
use core::ops::Range;

/// TODO FITZGEN
pub struct Context {
    pub(crate) context8: ContextInner<u8>,
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
            context8: ContextInner::new(),
            context16: ContextInner::new(),
            context32: ContextInner::new(),
        }
    }

    /// TODO FITZGEN
    pub fn reset(&mut self) {
        let Self {
            context8,
            context16,
            context32,
        } = self;
        context8.reset();
        context16.reset();
        context32.reset();
    }

    /// TODO FITZGEN
    pub fn is_reset(&self) -> bool {
        let Self {
            context8,
            context16,
            context32,
        } = self;
        context8.is_reset() && context16.is_reset() && context32.is_reset()
    }
}

pub(crate) struct ContextInner<E: EntityRepr> {
    pub counts: Counts,
    pub region_tree: RegionTree<E>,
    pub liveness: Liveness<E>,
    pub live_ranges: LiveRanges<E>,
    pub sccs: StronglyConnectedComponents<E>,
    pub dfs: Dfs<E>,
}

impl<E: EntityRepr> ContextInner<E> {
    const fn new() -> Self {
        Self {
            counts: Counts::new(),
            region_tree: RegionTree::new(),
            liveness: Liveness::new(),
            live_ranges: LiveRanges::new(),
            sccs: StronglyConnectedComponents::new(),
            dfs: Dfs::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            counts,
            region_tree,
            liveness,
            live_ranges,
            sccs,
            dfs,
        } = self;
        counts.reset();
        region_tree.reset();
        liveness.reset();
        live_ranges.reset();
        sccs.reset();
        dfs.reset();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            counts,
            region_tree,
            liveness,
            live_ranges,
            sccs,
            dfs,
        } = self;
        counts.is_reset()
            && region_tree.is_reset()
            && liveness.is_reset()
            && live_ranges.is_reset()
            && sccs.is_reset()
            && dfs.is_reset()
    }
}
