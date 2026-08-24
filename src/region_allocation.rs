//! Region-based allocation.
//!
//! We do a bottom-up walk of the region tree, allocating registers within each
//! region.

mod assignments;

use crate::{
    Entity, Input, InputFunction, InputValue, OperandConstraint, RegClass,
    context::ContextInner,
    entity::{EntityRepr, Region},
    error::IResult,
    live_ranges::{LiveBundle, LiveRanges, LiveSpan},
    machine::RegClassMembers,
    region_tree::RegionTree,
    timing::Timing,
};
use alloc::{collections::BinaryHeap, vec::Vec};
use assignments::Assignments;
use core::{fmt, marker::PhantomData};

pub fn region_allocate<E>(
    context: &mut ContextInner<E>,
    input: &Input<'_, impl InputFunction>,
) -> IResult<()>
where
    E: EntityRepr,
{
    let _timing = Timing::new("region allocate");

    let ContextInner {
        region_tree,
        live_ranges,
        region_allocation,
        ..
    } = context;

    let mut region_pre_order = core::mem::take(&mut region_allocation.region_pre_order);
    find_region_pre_order(&mut region_pre_order, region_tree);

    for region in region_pre_order.iter().copied().rev() {
        region_allocation.allocate_region(input, live_ranges, region);
    }

    region_pre_order.clear();
    debug_assert!(region_allocation.region_pre_order.is_empty());
    region_allocation.region_pre_order = region_pre_order;

    // TODO: add final counts of spans and bundles

    Ok(())
}

fn find_region_pre_order<E>(region_pre_order: &mut Vec<Region<E>>, region_tree: &RegionTree<E>)
where
    E: EntityRepr,
{
    let _ = (region_pre_order, region_tree);
    todo!("fill `region_pre_order` with a pre-order traversal of the region tree")
}

pub struct RegionAllocation<E>
where
    E: EntityRepr,
{
    /// The register allocation assignments we've committed to, across all regions.
    assignments: Assignments<E>,

    /// The work-in-progress register allocation assignments for the current
    /// region.
    region_assignments: Assignments<E>,

    /// The main work queue of bundles that still need assignment.
    queue: BinaryHeap<PqEntry<E>>,

    /// Scratch space to hold a pre-order traversal of the region tree.
    region_pre_order: Vec<Region<E>>,

    /// The set of bundles that must be allocated to stack slots.
    ///
    /// We just remember the set for now, and actually allocate the stack slots
    /// in later passes.
    stack_bundles: Vec<LiveBundle<E>>,
}

impl<E> RegionAllocation<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        Self {
            assignments: Assignments::new(),
            region_assignments: Assignments::new(),
            queue: BinaryHeap::new(),
            region_pre_order: Vec::new(),
            stack_bundles: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        let RegionAllocation {
            assignments,
            region_assignments,
            queue,
            region_pre_order,
            stack_bundles,
        } = self;
        assignments.reset();
        region_assignments.reset();
        queue.clear();
        region_pre_order.clear();
        stack_bundles.clear();
    }

    pub fn is_reset(&self) -> bool {
        let RegionAllocation {
            assignments,
            region_assignments,
            queue,
            region_pre_order,
            stack_bundles,
        } = self;
        assignments.is_reset()
            && region_assignments.is_reset()
            && queue.is_empty()
            && region_pre_order.is_empty()
            && stack_bundles.is_empty()
    }

    fn allocate_region(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        live_ranges: &mut LiveRanges<E>,
        region: Region<E>,
    ) {
        debug_assert!(self.queue.is_empty());

        // Insert each bundle in this region into the queue.
        //
        // Okay to call `region_bundles` because we haven't split any of this
        // region's bundles yet, because we haven't allocated registers within
        // this region yet.
        for bundle in region.bundles(live_ranges) {
            self.push_bundle(input, live_ranges, bundle, Phase::default());
        }

        // Keep processing bundles until they've all been assigned!
        while let Some(entry) = self.queue.pop() {
            debug_assert_eq!(entry.priority(), self.get_bundle_priority(entry.bundle()));

            // TODO: increment `counts.queue_pops`

            let phase = entry.phase();

            if self.assign_to_preferred(input, live_ranges, entry) {
                // TODO: increment `counts.preferred_assignments`
                continue;
            }

            if self.assign_to_non_preferred(input, live_ranges, entry) {
                // TODO: increment `counts.non_preferred_assignments`
                continue;
            }

            if phase <= Phase::AssignEvict && self.assign_via_eviction(entry) {
                // TODO: increment `counts.evictions`
                continue;
            }

            if phase <= Phase::SplitOnce {
                self.split_once(entry);
                // TODO: increment `counts.split_once`
                continue;
            }

            if phase <= Phase::SplitAtBlocks {
                self.split_at_blocks(entry);
                // TODO: increment `counts.split_at_blocks`
                continue;
            }

            debug_assert_eq!(phase, Phase::SplitIntoMinimalOrSpill);
            self.split_into_minimal_or_spill(entry);
            // TODO: increment `counts.split_into_minimal_or_spill`
        }
    }

    fn push_bundle(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        live_ranges: &LiveRanges<E>,
        bundle: LiveBundle<E>,
        phase: Phase,
    ) {
        let priority = compute_bundle_priority(input, live_ranges, bundle);
        self.set_bundle_priority(bundle, priority);
        self.queue.push(PqEntry::new(phase, priority, bundle));
    }

    fn set_bundle_priority(&mut self, bundle: LiveBundle<E>, priority: Priority) {
        let _ = (bundle, priority);
        todo!("SecondaryMap<LiveBundle<E>, Priority> on self")
    }

    fn get_bundle_priority(&self, bundle: LiveBundle<E>) -> Priority {
        let _ = bundle;
        todo!("SecondaryMap<LiveBundle<E>, Priority> on self")
    }

    fn assign_to_preferred(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        live_ranges: &LiveRanges<E>,
        entry: PqEntry<E>,
    ) -> bool {
        let machine = input.machine;
        let bundle = entry.bundle();
        let pref = bundle.preference(live_ranges);

        if pref.is_empty() {
            return false;
        }

        // If this bundle has a register preference, then that preference had
        // better match its constraints.
        if cfg!(debug_assertions) {
            match bundle.constraint(live_ranges) {
                OperandConstraint::Any => {
                    let class = bundle_reg_class(input, live_ranges, bundle);
                    debug_assert!(pref.is_subset_of(class.member_set(machine)));
                    debug_assert!(matches!(class.members(machine), RegClassMembers::Regs(_)));
                }
                OperandConstraint::Reg(rc) => {
                    debug_assert!(pref.is_subset_of(rc.member_set(machine)));
                    debug_assert!(matches!(rc.members(machine), RegClassMembers::Regs(_)));
                }
                OperandConstraint::Stack => {
                    panic!("should not have reg preference with stack constraint")
                }
                OperandConstraint::Reuse(_) => unreachable!("already resolved reuse constraints"),
            }
        }

        self.region_assignments.try_assign_to_reg(
            bundle,
            pref.iter(),
            |r| r.units(machine),
            bundle
                .spans(live_ranges)
                .map(|s| s.start(live_ranges)..s.end(live_ranges)),
        )
    }

    fn assign_to_non_preferred(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        live_ranges: &LiveRanges<E>,
        entry: PqEntry<E>,
    ) -> bool {
        let bundle = entry.bundle();

        let pref = bundle.preference(live_ranges);

        let rc = match bundle.constraint(live_ranges) {
            OperandConstraint::Any => {
                // No use constrained this bundle any further than the default
                // register class of its values, so use that default class.
                bundle_reg_class(input, live_ranges, bundle)
            }
            OperandConstraint::Reg(rc) => rc,
            OperandConstraint::Stack => {
                self.stack_bundles.push(bundle);
                return true;
            }
            OperandConstraint::Reuse(_) => unreachable!("already resolved reuse constraints"),
        };

        match rc.members(input.machine) {
            RegClassMembers::Regs(regs) => self.region_assignments.try_assign_to_reg(
                bundle,
                regs.iter().copied().filter(|r| !pref.contains(*r)),
                |r| r.units(input.machine),
                bundle
                    .spans(live_ranges)
                    .map(|s| s.start(live_ranges)..s.end(live_ranges)),
            ),
            RegClassMembers::Groups(groups) => {
                debug_assert!(pref.is_empty());
                self.region_assignments.try_assign_to_reg_group(
                    bundle,
                    groups.iter().copied(),
                    |g| {
                        g.members(input.machine)
                            .iter()
                            .map(|r| r.units(input.machine))
                    },
                    bundle
                        .spans(live_ranges)
                        .map(|s| s.start(live_ranges)..s.end(live_ranges)),
                )
            }
        }
    }

    fn assign_via_eviction(&mut self, entry: PqEntry<E>) -> bool {
        let bundle = entry.bundle();
        let _ = bundle;

        // TODO: otherwise, find the bundle with the least priority in any of
        // this bundle's assignable registers where this bundle would be
        // allocatable to the associated register if that other bundle were
        // evicted. if there is no such bundle, or that bundle's priority is
        // higher than this bundle's priority, then re-push this bundle with an
        // `entry.priority().phase().inc()` phase. otherwise, if that bundle's
        // priority is less than this bundle's priority, evict it, push it onto
        // the queue with phase `AssignEvict`, and assign this bundle to that
        // now-available register.

        todo!()
    }

    fn split_once(&mut self, entry: PqEntry<E>) {
        let bundle = entry.bundle();
        let _ = bundle;
        todo!()
    }

    fn split_at_blocks(&mut self, entry: PqEntry<E>) {
        let bundle = entry.bundle();
        let _ = bundle;
        todo!()
    }

    fn split_into_minimal_or_spill(&mut self, entry: PqEntry<E>) {
        let bundle = entry.bundle();
        let _ = bundle;
        todo!()
    }
}

impl<E> Default for RegionAllocation<E>
where
    E: EntityRepr,
{
    fn default() -> Self {
        Self::new()
    }
}

fn compute_bundle_priority<E>(
    input: &Input<'_, impl InputFunction>,
    live_ranges: &LiveRanges<E>,
    bundle: LiveBundle<E>,
) -> Priority
where
    E: EntityRepr,
{
    Priority::new(
        bundle.has_fixed_uses(live_ranges),
        bundle.is_minimal(live_ranges),
        bundle_group_size(input, live_ranges, bundle),
        bundle.spans(live_ranges).len(),
    )
}

fn bundle_group_size<E>(
    input: &Input<'_, impl InputFunction>,
    live_ranges: &LiveRanges<E>,
    bundle: LiveBundle<E>,
) -> usize
where
    E: EntityRepr,
{
    let machine = input.machine;

    // An `Any` bundle is assignable within the class its values live in, which
    // may itself be a class of register groups, so it has to answer the same
    // question that a `Reg` bundle does.
    let rc = match bundle.constraint(live_ranges) {
        OperandConstraint::Any => bundle_reg_class(input, live_ranges, bundle),
        OperandConstraint::Reg(rc) => rc,
        OperandConstraint::Stack => return 0,
        OperandConstraint::Reuse(_) => unreachable!(),
    };

    match rc.members(machine) {
        RegClassMembers::Groups(groups) => groups[0].members(machine).len(),
        RegClassMembers::Regs(_) => 0,
    }
}

/// The register class that `bundle`'s values naturally belong within.
fn bundle_reg_class<E>(
    input: &Input<'_, impl InputFunction>,
    live_ranges: &LiveRanges<E>,
    bundle: LiveBundle<E>,
) -> RegClass
where
    E: EntityRepr,
{
    let class_of = |span: LiveSpan<E>| {
        let val = span.val(live_ranges).with_repr32();
        input.func.value(val).reg_class()
    };

    let mut spans = bundle.spans(live_ranges);
    let first = spans
        .next()
        .expect("a bundle always holds at least one span");
    let rc = class_of(first);

    debug_assert!(
        spans.all(|span| class_of(span) == rc),
        "the values in one bundle always share a register class",
    );

    rc
}

/// What phase of allocation is the associated bundle in?
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Phase {
    /// The initial phase.
    ///
    /// Try to assign the bundle, evicting another lower-priority bundle if
    /// necessary.
    #[default]
    AssignEvict = 0,

    /// The first split attempt.
    ///
    /// Split the bundle to resolve a conflict and then try allocating each half
    /// again. This optimistically keeps bundles as large as possible, while
    /// resolving the conflict.
    SplitOnce = 1,

    /// The second split attempt.
    ///
    /// We don't want to spend `N` queue-popping iterations on incrementally
    /// splitting a large bundle into `N` pieces in a high-conflict scenario, so
    /// eagerly split at basic block boundaries in addition to splitting to
    /// resolve the current conflict, with the hope that this allows us to skip
    /// a bunch of conflicts with a single step.
    SplitAtBlocks = 2,

    /// The final phase.
    ///
    /// If this is not a minimal bundle yet, we can still split on conflict, and
    /// in this case we'll split into minimal bundles.
    ///
    /// If this is a minimal bundle, then we have to resort to spilling either
    /// this bundle or one of the others it conflicts with to the stack.
    SplitIntoMinimalOrSpill = 3,
}

impl Phase {
    /// Get the next phase after this one.
    #[allow(dead_code, reason = "will use it soon")]
    fn next(self) -> Self {
        Self::from_raw((self as u8) + 1).unwrap()
    }

    /// Construct a `Phase` from its raw bits.
    fn from_raw(raw: u8) -> Option<Self> {
        match raw {
            0 => Some(Self::AssignEvict),
            1 => Some(Self::SplitOnce),
            2 => Some(Self::SplitAtBlocks),
            3 => Some(Self::SplitIntoMinimalOrSpill),
            _ => None,
        }
    }
}

/// A bundle's allocation priority.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Priority {
    ///    Bit:   31   ...  30   29                28             27  ...   25   24  ...  0
    ///         +--------------+-----------------+--------------+--------------+------------+
    /// Fields: | (reserved):2 | has_fixed_use:1 | is_minimal:1 | group_size:3 |   size:25  |
    ///         +--------------+-----------------+--------------+--------------+------------+
    ///
    /// Packed so that we sort/prioritize bundles by:
    ///
    /// 1. Those with fixed register uses (as they have the hardest constraints
    ///    to satisfy)
    ///
    /// 2. Minimal bundles (as these can't be split any further, so allocating
    ///    to a register, rather than a spill slot, is now-or-never).
    ///
    /// 3. The size of its register group constraint (because assigning a
    ///    register groups assigns N registers at once, not just 1, so they are
    ///    harder to place and have more constraints than regular bundles).
    ///
    /// 4. Finally, by the bundle's size (number of spans) because if we assign
    ///    a larger bundle, then we get fewer moves and better codegen (and if
    ///    assigning it fails, we can always split it and try again).
    ///
    /// NB: the upper bits are reserved for encoding a `Phase` when this is
    /// packed inside a `PqEntry`.
    bits: u32,
}

const PRIORITY_SIZE_BITS: u32 = 25;
const PRIORITY_SIZE_SHIFT: u32 = 0;
const PRIORITY_SIZE_MASK: u32 = ((1 << PRIORITY_SIZE_BITS) - 1) << PRIORITY_SIZE_SHIFT;

const PRIORITY_GROUP_SIZE_BITS: u32 = 3;
const PRIORITY_GROUP_SIZE_SHIFT: u32 = PRIORITY_SIZE_SHIFT + PRIORITY_SIZE_BITS;
const PRIORITY_GROUP_SIZE_MASK: u32 =
    ((1 << PRIORITY_GROUP_SIZE_BITS) - 1) << PRIORITY_GROUP_SIZE_SHIFT;
const PRIORITY_GROUP_SIZE_MAX: usize = (1 << PRIORITY_GROUP_SIZE_BITS) - 1;

const PRIORITY_IS_MINIMAL_BITS: u32 = 1;
const PRIORITY_IS_MINIMAL_SHIFT: u32 = PRIORITY_GROUP_SIZE_SHIFT + PRIORITY_GROUP_SIZE_BITS;
const PRIORITY_IS_MINIMAL_MASK: u32 =
    ((1 << PRIORITY_IS_MINIMAL_BITS) - 1) << PRIORITY_IS_MINIMAL_SHIFT;

const PRIORITY_HAS_FIXED_USE_BITS: u32 = 1;
const PRIORITY_HAS_FIXED_USE_SHIFT: u32 = PRIORITY_IS_MINIMAL_SHIFT + PRIORITY_IS_MINIMAL_BITS;
const PRIORITY_HAS_FIXED_USE_MASK: u32 =
    ((1 << PRIORITY_HAS_FIXED_USE_BITS) - 1) << PRIORITY_HAS_FIXED_USE_SHIFT;

/// A priority queue entry.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct PqEntry<E> {
    ///    Bit:   63   62   61  ...  32   31  ...  0
    ///         +---------+-------------+------------+
    /// Fields: | phase:2 | priority:30 |  bundle:32 |
    ///         +---------+-------------+------------+
    ///
    /// Packed so that sort/prioritize by phase, then bundle priority, and
    /// finally break ties with the bundle index.
    bits: u64,

    _phantom: PhantomData<E>,
}

const PQ_ENTRY_BUNDLE_BITS: u64 = 32;
const PQ_ENTRY_BUNDLE_SHIFT: u64 = 0;
const PQ_ENTRY_BUNDLE_MASK: u64 = ((1 << PQ_ENTRY_BUNDLE_BITS) - 1) << PQ_ENTRY_BUNDLE_SHIFT;

const PQ_ENTRY_PRIORITY_BITS: u64 = 30;
const PQ_ENTRY_PRIORITY_SHIFT: u64 = PQ_ENTRY_BUNDLE_SHIFT + PQ_ENTRY_BUNDLE_BITS;
const PQ_ENTRY_PRIORITY_MASK: u64 = ((1 << PQ_ENTRY_PRIORITY_BITS) - 1) << PQ_ENTRY_PRIORITY_SHIFT;

const PQ_ENTRY_PHASE_BITS: u64 = 2;
const PQ_ENTRY_PHASE_SHIFT: u64 = PQ_ENTRY_PRIORITY_SHIFT + PQ_ENTRY_PRIORITY_BITS;
const PQ_ENTRY_PHASE_MASK: u64 = ((1 << PQ_ENTRY_PHASE_BITS) - 1) << PQ_ENTRY_PHASE_SHIFT;

impl fmt::Debug for Priority {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Priority")
            .field("has_fixed_use", &self.has_fixed_use())
            .field("is_minimal", &self.is_minimal())
            .field("group_size", &self.group_size())
            .field("size", &self.size())
            .finish()
    }
}

impl<E> fmt::Debug for PqEntry<E>
where
    E: EntityRepr,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PqEntry")
            .field("phase", &self.phase())
            .field("priority", &self.priority())
            .field("bundle", &self.bundle())
            .finish()
    }
}

impl Priority {
    fn new(has_fixed_use: bool, is_minimal: bool, group_size: usize, size: usize) -> Self {
        let has_fixed_use = u32::from(has_fixed_use) << PRIORITY_HAS_FIXED_USE_SHIFT;
        debug_assert_eq!(has_fixed_use & PRIORITY_HAS_FIXED_USE_MASK, has_fixed_use);

        let is_minimal = u32::from(is_minimal) << PRIORITY_IS_MINIMAL_SHIFT;
        debug_assert_eq!(is_minimal & PRIORITY_IS_MINIMAL_MASK, is_minimal);

        let group_size = u32::try_from(group_size.min(PRIORITY_GROUP_SIZE_MAX)).unwrap();
        let group_size = group_size << PRIORITY_GROUP_SIZE_SHIFT;
        debug_assert_eq!(group_size & PRIORITY_GROUP_SIZE_MASK, group_size);

        let max_size = (1 << PRIORITY_SIZE_BITS) - 1;
        debug_assert!(size <= max_size);
        let size = u32::try_from(size).unwrap();
        let size = size << PRIORITY_SIZE_SHIFT;
        debug_assert_eq!(size & PRIORITY_SIZE_MASK, size);

        Priority {
            bits: has_fixed_use | is_minimal | group_size | size,
        }
    }

    #[inline]
    fn has_fixed_use(&self) -> bool {
        self.bits & PRIORITY_HAS_FIXED_USE_MASK != 0
    }

    #[inline]
    fn is_minimal(&self) -> bool {
        self.bits & PRIORITY_IS_MINIMAL_MASK != 0
    }

    #[inline]
    fn group_size(&self) -> usize {
        let group_size = (self.bits & PRIORITY_GROUP_SIZE_MASK) >> PRIORITY_GROUP_SIZE_SHIFT;
        usize::try_from(group_size).unwrap()
    }

    #[inline]
    fn size(&self) -> usize {
        let size = (self.bits & PRIORITY_SIZE_MASK) >> PRIORITY_SIZE_SHIFT;
        usize::try_from(size).unwrap()
    }
}

impl<E> PqEntry<E>
where
    E: EntityRepr,
{
    fn new(phase: Phase, priority: Priority, bundle: LiveBundle<E>) -> Self {
        let phase = u64::from(phase as u8);
        let phase = phase << PQ_ENTRY_PHASE_SHIFT;
        debug_assert_eq!(phase & PQ_ENTRY_PHASE_MASK, phase);

        let priority = u64::from(priority.bits);
        let priority = priority << PQ_ENTRY_PRIORITY_SHIFT;
        debug_assert_eq!(priority & PQ_ENTRY_PRIORITY_MASK, priority);

        let bundle = u32::try_from(bundle.index()).unwrap();
        let bundle = u64::from(bundle);
        debug_assert_eq!(bundle & PQ_ENTRY_BUNDLE_MASK, bundle);

        Self {
            bits: phase | priority | bundle,
            _phantom: PhantomData,
        }
    }

    #[inline]
    fn phase(&self) -> Phase {
        let phase = (self.bits & PQ_ENTRY_PHASE_MASK) >> PQ_ENTRY_PHASE_SHIFT;
        let phase = u8::try_from(phase).unwrap();
        Phase::from_raw(phase).expect("every value of the two-bit field is a phase")
    }

    #[inline]
    fn priority(&self) -> Priority {
        let priority = (self.bits & PQ_ENTRY_PRIORITY_MASK) >> PQ_ENTRY_PRIORITY_SHIFT;
        Priority {
            bits: u32::try_from(priority).unwrap(),
        }
    }

    #[inline]
    fn bundle(&self) -> LiveBundle<E> {
        let bundle = (self.bits & PQ_ENTRY_BUNDLE_MASK) >> PQ_ENTRY_BUNDLE_SHIFT;
        let bundle = usize::try_from(bundle).unwrap();
        LiveBundle::try_new(bundle).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::RegGroup;
    use std::{vec, vec::Vec};

    const MAX_SIZE: usize = (1 << PRIORITY_SIZE_BITS) - 1;
    const MAX_GROUP_SIZE: usize = PRIORITY_GROUP_SIZE_MAX;

    /// Every phase, in ascending order.
    const PHASES: [Phase; 4] = [
        Phase::AssignEvict,
        Phase::SplitOnce,
        Phase::SplitAtBlocks,
        Phase::SplitIntoMinimalOrSpill,
    ];

    fn bundle(index: usize) -> LiveBundle<u32> {
        LiveBundle::try_new(index).unwrap()
    }

    /// A priority's fields survive the round trip through its packed bits.
    #[test]
    fn priority_round_trips_its_fields() {
        for has_fixed_use in [false, true] {
            for is_minimal in [false, true] {
                for group_size in [0, 1, 2, MAX_GROUP_SIZE, RegGroup::MAX_SIZE] {
                    for size in [0, 1, 1000, MAX_SIZE] {
                        let p = Priority::new(has_fixed_use, is_minimal, group_size, size);
                        assert_eq!(p.has_fixed_use(), has_fixed_use, "{p:?}");
                        assert_eq!(p.is_minimal(), is_minimal, "{p:?}");
                        assert_eq!(p.group_size(), group_size.min(MAX_GROUP_SIZE), "{p:?}");
                        assert_eq!(p.size(), size.min(MAX_SIZE), "{p:?}");
                    }
                }
            }
        }
    }

    /// Priorities compare by fixed uses first, then minimality, then register
    /// group size, and only then by the bundle's own size.
    #[test]
    fn priority_compares_by_tier() {
        let ascending = [
            Priority::new(false, false, 0, 0),
            Priority::new(false, false, 0, 1),
            Priority::new(false, false, 0, MAX_SIZE),
            Priority::new(false, false, 1, 0),
            Priority::new(false, false, MAX_GROUP_SIZE, MAX_SIZE),
            Priority::new(false, true, 0, 0),
            Priority::new(false, true, MAX_GROUP_SIZE, MAX_SIZE),
            Priority::new(true, false, 0, 0),
            Priority::new(true, true, MAX_GROUP_SIZE, MAX_SIZE),
        ];
        for w in ascending.windows(2) {
            assert!(w[0] < w[1], "{:?} should sort below {:?}", w[0], w[1]);
        }
    }

    /// A queue entry's fields survive the round trip through its packed bits,
    /// including the largest bundle index a `LiveBundle<u32>` can name.
    #[test]
    fn pq_entry_round_trips_its_fields() {
        let priorities = [
            Priority::new(false, false, 0, 0),
            Priority::new(true, true, MAX_GROUP_SIZE, MAX_SIZE),
            Priority::new(false, true, 2, 1000),
        ];
        for phase in PHASES {
            for priority in priorities {
                for index in [0, 1, 1000, LiveBundle::<u32>::MAX_REPRESENTABLE.index()] {
                    let entry = PqEntry::new(phase, priority, bundle(index));
                    assert_eq!(entry.phase(), phase, "{entry:?}");
                    assert_eq!(entry.priority(), priority, "{entry:?}");
                    assert_eq!(entry.bundle(), bundle(index), "{entry:?}");
                }
            }
        }
    }

    /// Queue entries compare by phase first, then by priority, and break
    /// remaining ties with the bundle index.
    #[test]
    fn pq_entry_compares_by_phase_then_priority_then_bundle() {
        let low = Priority::new(false, false, 0, 0);
        let high = Priority::new(true, true, MAX_GROUP_SIZE, MAX_SIZE);
        let max_index = LiveBundle::<u32>::MAX_REPRESENTABLE.index();

        let mut ascending = vec![
            PqEntry::new(Phase::AssignEvict, low, bundle(0)),
            PqEntry::new(Phase::AssignEvict, low, bundle(1)),
            PqEntry::new(Phase::AssignEvict, low, bundle(max_index)),
            PqEntry::new(Phase::AssignEvict, high, bundle(0)),
        ];
        // A later phase outranks any priority in an earlier one.
        for phase in PHASES.into_iter().skip(1) {
            ascending.push(PqEntry::new(phase, low, bundle(0)));
            ascending.push(PqEntry::new(phase, high, bundle(max_index)));
        }

        for w in ascending.windows(2) {
            assert!(w[0] < w[1], "{:?} should sort below {:?}", w[0], w[1]);
        }

        // And the queue pops the greatest entry first.
        let mut queue: BinaryHeap<PqEntry<u32>> = ascending.iter().copied().collect();
        let popped: Vec<_> = core::iter::from_fn(|| queue.pop()).collect();
        assert!(ascending.iter().rev().eq(popped.iter()));
    }
}
