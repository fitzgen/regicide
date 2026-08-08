use core::ops::Range;

use alloc::vec::Vec;

use crate::{
    btree::{BTreeSet, BTreeSetArena},
    entity::{
        Allocation, Block, Bundle, Entity, EntityRepr, Inst, LiveRange, PrimaryMap, Region, Scc,
        SecondaryMap, Val,
    },
    live_ranges::{BundleData, LiveRangeData, ProgramPoint},
    liveness::Liveness,
    union_find::UnionFind,
};

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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct EntityRange<K: Entity> {
    pub start: K,
    pub end: K,
}

impl<K> Default for EntityRange<K>
where
    K: Entity,
{
    fn default() -> Self {
        Self::empty()
    }
}

impl<K> EntityRange<K>
where
    K: Entity,
{
    pub const fn empty() -> Self {
        Self {
            start: K::MAX,
            end: K::MAX,
        }
    }
}

/// TODO FITZGEN: make a real type; number of bits is the maximum number of live
/// ranges in a bundle
type ScalarBitSet = [u32; 8];

type Priority = u16;

pub(crate) struct ContextInner<E: EntityRepr> {
    liveness: Liveness<E>,

    live_ranges: PrimaryMap<LiveRange<E>, Range<ProgramPoint<E>>>,
    live_range_bundle: SecondaryMap<LiveRange<E>, Option<Bundle<E>>>,
    live_range_val: SecondaryMap<LiveRange<E>, Val<E>>,

    bundles: PrimaryMap<Bundle<E>, BundleData>,
    bundle_pinned_ranges: SecondaryMap<Bundle<E>, ScalarBitSet>,
    bundle_allocation: SecondaryMap<Bundle<E>, Option<Allocation<E>>>,
    bundle_priority: SecondaryMap<Bundle<E>, Priority>,

    inst_live_ranges: SecondaryMap<Inst<E>, EntityRange<LiveRange<E>>>,

    /// TODO FITZGEN
    sccs_arena: BTreeSetArena<E, Block<E>>,
    /// TODO FITZGEN
    sccs: PrimaryMap<Scc<E>, BTreeSet<E, Block<E>>>,
    /// Map from a strongly-connected component to its region representative.
    scc_region_representative: UnionFind<Scc<E>>,
    /// Map from a region representative to its region; allows regions to be
    /// densely packed.
    scc_to_region: SecondaryMap<Scc<E>, Option<Region<E>>>,
}

impl<E: EntityRepr> ContextInner<E> {
    const fn new() -> Self {
        Self {
            liveness: Liveness::new(),

            live_ranges: PrimaryMap::new(),
            live_range_bundle: SecondaryMap::new(None),
            live_range_val: SecondaryMap::new(Val::MAX),

            bundles: PrimaryMap::new(),
            bundle_pinned_ranges: SecondaryMap::new([0; 8]),
            bundle_allocation: SecondaryMap::new(None),
            bundle_priority: SecondaryMap::new(0),

            inst_live_ranges: SecondaryMap::new(EntityRange::empty()),

            sccs_arena: BTreeSetArena::new(),
            sccs: PrimaryMap::new(),
            scc_region_representative: UnionFind::new(),
            scc_to_region: SecondaryMap::new(None),
        }
    }

    pub(crate) fn reset(&mut self) {
        let Self {
            liveness,

            live_ranges,
            live_range_bundle,
            live_range_val,

            bundles,
            bundle_pinned_ranges,
            bundle_allocation,
            bundle_priority,

            inst_live_ranges,

            sccs_arena,
            sccs,
            scc_region_representative,
            scc_to_region,
        } = self;

        liveness.reset();

        live_ranges.reset();
        live_range_bundle.reset();
        live_range_val.reset();

        bundles.reset();
        bundle_pinned_ranges.reset();
        bundle_allocation.reset();
        bundle_priority.reset();

        inst_live_ranges.reset();

        sccs_arena.reset();
        sccs.reset();
        scc_region_representative.reset();
        scc_to_region.reset();
    }

    pub(crate) fn is_reset(&self) -> bool {
        let Self {
            liveness,

            live_ranges,
            live_range_bundle,
            live_range_val,

            bundles,
            bundle_pinned_ranges,
            bundle_allocation,
            bundle_priority,

            inst_live_ranges,

            sccs_arena,
            sccs,
            scc_region_representative,
            scc_to_region,
        } = self;

        liveness.is_reset()
            && live_ranges.is_reset()
            && live_range_bundle.is_reset()
            && live_range_val.is_reset()
            && bundles.is_reset()
            && bundle_pinned_ranges.is_reset()
            && bundle_allocation.is_reset()
            && bundle_priority.is_reset()
            && inst_live_ranges.is_reset()
            && sccs_arena.is_reset()
            && sccs.is_reset()
            && scc_region_representative.is_reset()
            && scc_to_region.is_reset()
    }
}
