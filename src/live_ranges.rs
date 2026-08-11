//! Constructs live ranges and bundles.

use crate::context::ContextInner;
use crate::entity::{
    Bundle, Entity, EntityRange, EntityRepr, Inst, LiveRange, PrimaryMap, SecondaryMap, Val,
};
use crate::error::IResult;
use crate::input::InputFunction;
use crate::liveness::Liveness;
use crate::output::Allocation;
use crate::region_tree::RegionTree;
use crate::timing::Timing;
use core::range::Range;

pub enum ProgramPoint<E>
where
    E: EntityRepr,
{
    Before(Inst<E>),
    After(Inst<E>),
}

pub struct LiveRangeData<E>
where
    E: EntityRepr,
{
    pub start: ProgramPoint<E>,
    pub end: ProgramPoint<E>,
}

pub struct BundleData {
    // TODO
}

/// TODO FITZGEN: make a real type; number of bits is the maximum number of live
/// ranges in a bundle
type ScalarBitSet = [u32; 8];

type Priority = u16;

pub struct LiveRanges<E>
where
    E: EntityRepr,
{
    ranges: PrimaryMap<LiveRange<E>, Range<ProgramPoint<E>>>,
    range_bundle: SecondaryMap<LiveRange<E>, Option<Bundle<E>>>,
    range_val: SecondaryMap<LiveRange<E>, Val<E>>,

    bundles: PrimaryMap<Bundle<E>, BundleData>,
    bundle_pinned_ranges: SecondaryMap<Bundle<E>, ScalarBitSet>,
    bundle_allocation: SecondaryMap<Bundle<E>, Option<Allocation<E>>>,
    bundle_priority: SecondaryMap<Bundle<E>, Priority>,

    inst_ranges: SecondaryMap<Inst<E>, EntityRange<LiveRange<E>>>,
}

impl<E> LiveRanges<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        LiveRanges {
            ranges: PrimaryMap::new(),
            range_bundle: SecondaryMap::new(None),
            range_val: SecondaryMap::new(Val::MAX),

            bundles: PrimaryMap::new(),
            bundle_pinned_ranges: SecondaryMap::new([0; 8]),
            bundle_allocation: SecondaryMap::new(None),
            bundle_priority: SecondaryMap::new(0),

            inst_ranges: SecondaryMap::new(EntityRange::empty()),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            ranges,
            range_bundle,
            range_val,
            bundles,
            bundle_pinned_ranges,
            bundle_allocation,
            bundle_priority,
            inst_ranges,
        } = self;
        ranges.reset();
        range_bundle.reset();
        range_val.reset();
        bundles.reset();
        bundle_pinned_ranges.reset();
        bundle_allocation.reset();
        bundle_priority.reset();
        inst_ranges.reset();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            ranges,
            range_bundle,
            range_val,
            bundles,
            bundle_pinned_ranges,
            bundle_allocation,
            bundle_priority,
            inst_ranges,
        } = self;
        ranges.is_reset()
            && range_bundle.is_reset()
            && range_val.is_reset()
            && bundles.is_reset()
            && bundle_pinned_ranges.is_reset()
            && bundle_allocation.is_reset()
            && bundle_priority.is_reset()
            && inst_ranges.is_reset()
    }

    pub fn construct(
        &mut self,
        func: &impl InputFunction,
        region_tree: &RegionTree<E>,
        liveness: &Liveness<E>,
    ) -> IResult<()> {
        let _timing = Timing::new("live ranges");
        // TODO
        let _ = (func, region_tree, liveness);
        Ok(())
    }
}
