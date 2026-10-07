//! The region tree.
//!
//! A region is a set of basic blocks whose contained live ranges are allocated
//! together. We never allocate across regions.
//!
//! To make this effective, we create regions for each cycle in the control-flow
//! graph, and for the function's top level.
//!
//! The cycles we find are natural loops (single-entry) when control flow is
//! reducible and a traversal-dependent but valid nesting when it is not. A
//! block's region is the innermost cycle containing it; blocks in no cycle,
//! unreachable ones included, belong to the top-level region.
//!
//! Cycle membership is *not* the same as (transitive) domination: a block after
//! a loop exits belongs to the enclosing region even though the loop dominates
//! it.
//!
//! Each region's cold blocks, other than the block naming it, are split off
//! into a *cold region* of their own, a child of that region. A cold region is
//! not a loop, and region allocation visits every cold region after every
//! other region, so that what happens on a cold path cannot constrain the
//! allocation of the paths that matter.

use crate::counts::Counts;
use crate::dfs::{Dfs, DfsEvent};
use crate::entity::{
    EntityRange, EntityRepr, EntitySet, PrimaryMap, Region, RegionBlocksStorageIndex,
    RegionChildrenStorageIndex, SecondaryMap,
};
use crate::error::IResult;
use crate::input::InputFunction;
use crate::output::OutputInner;
use crate::timing::Timing;
use crate::union_find::UnionFind;
use crate::{Block, Entity, InputBlock};
use alloc::vec::Vec;

/// Where a block sits in the depth-first traversal of the control-flow graph.
///
/// `start` is the one-based pre-order number, so zero means "never reached".
///
/// `end` is the largest pre-order number in the block's subtree.
///
/// A subtree's numbers are contiguous, so `start..=end` is exactly the
/// associated block's subtree.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct DfsInfo {
    start: u32,
    end: u32,
}

impl DfsInfo {
    /// Did the depth-first traversal reach this block at all?
    fn is_reached(&self) -> bool {
        self.start != 0
    }

    /// Is this block an ancestor of `other` in the depth-first tree?
    fn is_ancestor_of(&self, other: &DfsInfo) -> bool {
        self.start <= other.start && other.end <= self.end
    }
}

/// The region tree for a function.
pub struct RegionTree<E>
where
    E: EntityRepr,
{
    /// The root of the region tree: the function entry block's region.
    root: Option<Region<E>>,

    /// Map from a block to the innermost region containing it.
    ///
    /// `None` until `construct_block_regions` fills in the blocks in no cycle.
    block_region: SecondaryMap<Block<E>, Option<Region<E>>>,

    /// Map from a block to its position in the depth-first traversal.
    dfs_info: SecondaryMap<Block<E>, DfsInfo>,

    /// Map from a region to the enclosing region in the cycle nest, or `None`
    /// for the top-level region.
    region_parent: SecondaryMap<Region<E>, Option<Region<E>>>,

    /// Map from a region to how many loops enclose its blocks: zero for the
    /// top-level region.
    region_depth: SecondaryMap<Region<E>, u32>,

    /// Map from a region to the outermost region currently containing it.
    ///
    /// A new cycle absorbing a block an inner cycle already claimed must
    /// reparent that inner cycle's whole nest at once; this finds its top.
    top_level: UnionFind<Region<E>>,

    /// Map from a region to the indices within `region_blocks_storage` that
    /// contain this region's blocks.
    region_blocks: SecondaryMap<Region<E>, EntityRange<RegionBlocksStorageIndex<E>>>,

    /// The contiguous storage for the blocks that belong to each region.
    region_blocks_storage: PrimaryMap<RegionBlocksStorageIndex<E>, Block<E>>,

    /// Map from a region to the indices within `region_children_storage` that
    /// contain this region's immediate children.
    region_children: SecondaryMap<Region<E>, EntityRange<RegionChildrenStorageIndex<E>>>,

    /// The contiguous storage for the children that belong to each region.
    region_children_storage: PrimaryMap<RegionChildrenStorageIndex<E>, Region<E>>,

    /// A pre-order traversal of the region tree: every region appears exactly
    /// once, and always before any of its descendants.
    pre_order: Vec<Region<E>>,

    /// The regions holding only cold blocks split off from their parent.
    cold_regions: EntitySet<Region<E>>,

    /// Scratch space: each region's cold region, once it has one.
    cold_child: SecondaryMap<Region<E>, Option<Region<E>>>,

    /// Scratch space: the blocks in depth-first pre-order.
    dfs_pre_order: Vec<Block<E>>,

    /// Scratch space: each cycle's entry blocks, paired with the cycle.
    ///
    /// An entry is a block with a predecessor outside the cycle, i.e. one
    /// control can enter at. Only an irreducible cycle has more than one.
    cycle_entries: Vec<(Region<E>, Block<E>)>,

    /// Scratch space: the backward worklist used to grow a cycle from its
    /// header.
    worklist: Vec<Block<E>>,

    /// Scratch space: the depth-first stack used to build `pre_order`.
    pre_order_stack: Vec<Region<E>>,

    /// Scratch space: each block paired with its region, sorted by region so that
    /// we can lay each region's blocks out contiguously.
    blocks_by_region: Vec<(Region<E>, Block<E>)>,

    /// Scratch space: the distinct regions, in increasing index order.
    distinct_regions: Vec<Region<E>>,

    /// Scratch space: each non-top-level region paired with its parent, sorted by
    /// parent so that we can lay each region's children out contiguously.
    children_by_parent: Vec<(Region<E>, Region<E>)>,
}

impl<E> RegionTree<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        RegionTree {
            root: None,
            block_region: SecondaryMap::new(None),
            dfs_info: SecondaryMap::new(DfsInfo { start: 0, end: 0 }),
            region_parent: SecondaryMap::new(None),
            region_depth: SecondaryMap::new(0),
            top_level: UnionFind::new(),
            region_blocks: SecondaryMap::new(EntityRange::empty()),
            region_blocks_storage: PrimaryMap::new(),
            region_children: SecondaryMap::new(EntityRange::empty()),
            region_children_storage: PrimaryMap::new(),
            pre_order: Vec::new(),
            cold_regions: EntitySet::new(),
            cold_child: SecondaryMap::new(None),
            dfs_pre_order: Vec::new(),
            cycle_entries: Vec::new(),
            worklist: Vec::new(),
            pre_order_stack: Vec::new(),
            blocks_by_region: Vec::new(),
            distinct_regions: Vec::new(),
            children_by_parent: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            root,
            block_region,
            dfs_info,
            region_parent,
            region_depth,
            top_level,
            region_blocks,
            region_blocks_storage,
            region_children,
            region_children_storage,
            pre_order,
            cold_regions,
            cold_child,
            dfs_pre_order,
            cycle_entries,
            worklist,
            pre_order_stack,
            blocks_by_region,
            distinct_regions,
            children_by_parent,
        } = self;
        *root = None;
        block_region.reset();
        dfs_info.reset();
        region_parent.reset();
        region_depth.reset();
        top_level.reset();
        region_blocks.reset();
        region_blocks_storage.reset();
        region_children.reset();
        region_children_storage.reset();
        pre_order.clear();
        cold_regions.reset();
        cold_child.reset();
        dfs_pre_order.clear();
        cycle_entries.clear();
        worklist.clear();
        pre_order_stack.clear();
        blocks_by_region.clear();
        distinct_regions.clear();
        children_by_parent.clear();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            root,
            block_region,
            dfs_info,
            region_parent,
            region_depth,
            top_level,
            region_blocks,
            region_blocks_storage,
            region_children,
            region_children_storage,
            pre_order,
            cold_regions,
            cold_child,
            dfs_pre_order,
            cycle_entries,
            worklist,
            pre_order_stack,
            blocks_by_region,
            distinct_regions,
            children_by_parent,
        } = self;
        root.is_none()
            && block_region.is_reset()
            && dfs_info.is_reset()
            && region_parent.is_reset()
            && region_depth.is_reset()
            && top_level.is_reset()
            && region_blocks.is_reset()
            && region_blocks_storage.is_reset()
            && region_children.is_reset()
            && region_children_storage.is_reset()
            && pre_order.is_empty()
            && cold_regions.is_reset()
            && cold_child.is_reset()
            && dfs_pre_order.is_empty()
            && cycle_entries.is_empty()
            && worklist.is_empty()
            && pre_order_stack.is_empty()
            && blocks_by_region.is_empty()
            && distinct_regions.is_empty()
            && children_by_parent.is_empty()
    }

    /// Is every field that only holds state mid-construction empty?
    fn scratch_is_empty(&self) -> bool {
        self.dfs_pre_order.is_empty()
            && self.cold_child.is_reset()
            && self.cycle_entries.is_empty()
            && self.worklist.is_empty()
            && self.pre_order_stack.is_empty()
            && self.blocks_by_region.is_empty()
            && self.distinct_regions.is_empty()
            && self.children_by_parent.is_empty()
    }

    pub fn construct(
        &mut self,
        func: &impl InputFunction,
        counts: &mut Counts,
        dfs: &mut Dfs<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        let _timing = Timing::new("region tree");

        debug_assert!(self.pre_order.is_empty());
        debug_assert!(self.scratch_is_empty());

        self.construct_dfs_info(func, dfs, output)?;
        self.construct_cycles(func, output)?;
        self.construct_block_regions(func, output)?;
        self.construct_cold_regions(func, output)?;
        self.construct_region_blocks(func, output)?;
        self.construct_region_tree(output)?;
        self.construct_pre_order();

        counts.regions += self.distinct_regions.len();
        self.distinct_regions.clear();
        debug_assert!(
            self.scratch_is_empty(),
            "a completed construction leaves no scratch behind",
        );
        Ok(())
    }

    /// Run a depth-first traversal of the control-flow graph, recording each
    /// block's `DfsInfo` and filling `dfs_pre_order`.
    fn construct_dfs_info(
        &mut self,
        func: &impl InputFunction,
        dfs: &mut Dfs<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        self.dfs_pre_order.reserve(func.len_blocks());

        let mut counter: u32 = 0;
        dfs.construct(func, output)?;
        while let Some(event) = dfs.next(func, output, |block| self.dfs_info[block].is_reached())? {
            match event {
                DfsEvent::Pre(block) => {
                    debug_assert!(!self.dfs_info[block].is_reached());
                    debug_assert_eq!(counter, u32::try_from(self.dfs_pre_order.len()).unwrap());
                    counter += 1;
                    self.dfs_info[block].start = counter;
                    self.dfs_pre_order.push(block);
                }
                DfsEvent::AfterEdge(..) => {}
                DfsEvent::Post(block) => {
                    debug_assert!(self.dfs_info[block].is_reached());
                    self.dfs_info[block].end = counter;
                }
            }
        }

        dfs.reset();
        Ok(())
    }

    /// Discover the control-flow graph's cycles, filling in `block_region` and
    /// `region_parent`.
    ///
    /// Reverse pre-order finds every cycle before any cycle containing it, so
    /// an outer cycle adopts any inner cycles it runs into.
    fn construct_cycles(
        &mut self,
        func: &impl InputFunction,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        for i in (0..self.dfs_pre_order.len()).rev() {
            let header = self.dfs_pre_order[i];
            let header_info = self.dfs_info[header];

            // A block heads a cycle exactly when a predecessor lies within its
            // own depth-first subtree, i.e. when an edge back to it closes a
            // loop.
            debug_assert!(self.worklist.is_empty());
            for pred in func.block(header.with_repr32()).predecessors() {
                let pred = output.with_repr(pred)?;
                if header_info.is_ancestor_of(&self.dfs_info[pred]) {
                    self.worklist.push(pred);
                }
            }
            if self.worklist.is_empty() {
                continue;
            }

            // Name the cycle by its header.
            let cycle = output.entity::<Region<E>>(header.index())?;
            debug_assert!(self.block_region[header].is_none());
            self.block_region[header] = Some(cycle);
            self.cycle_entries.push((cycle, header));

            // Absorb everything that reaches the header without leaving its
            // depth-first subtree.
            while let Some(block) = self.worklist.pop() {
                if block == header {
                    continue;
                }

                match self.block_region[block] {
                    // Already claimed, so the outermost cycle containing it
                    // becomes our child, and its entries are where we continue
                    // looking for our own predecessors.
                    Some(inner) => {
                        let inner_top = self.top_level.find(inner);
                        if inner_top == cycle {
                            continue;
                        }

                        self.region_parent[inner_top] = Some(cycle);
                        let rep = self.top_level.union(cycle, inner_top);
                        debug_assert_eq!(rep, cycle);

                        // `process_predecessors` appends only entries of
                        // `cycle`, which never match `inner_top`, so skipping
                        // any newly pushed entries (when `len` becomes stale)
                        // loses nothing.
                        let len = self.cycle_entries.len();
                        for j in 0..len {
                            let (region, entry) = self.cycle_entries[j];
                            if region == inner_top {
                                self.process_predecessors(func, output, header, cycle, entry)?;
                            }
                        }
                    }

                    None => {
                        self.block_region[block] = Some(cycle);
                        self.process_predecessors(func, output, header, cycle, block)?;
                    }
                }
            }
        }

        self.dfs_pre_order.clear();
        self.cycle_entries.clear();

        Ok(())
    }

    /// Follow `block`'s predecessors while growing the cycle headed by
    /// `header`.
    ///
    /// A predecessor within the header's subtree joins the worklist; one
    /// outside it makes `block` an entry. An unreachable predecessor is
    /// ignored, since control never arrives along that edge.
    fn process_predecessors(
        &mut self,
        func: &impl InputFunction,
        output: &mut OutputInner<E>,
        header: Block<E>,
        cycle: Region<E>,
        block: Block<E>,
    ) -> IResult<()> {
        let header_info = self.dfs_info[header];

        let mut is_entry = false;
        for pred in func.block(block.with_repr32()).predecessors() {
            let pred = output.with_repr(pred)?;
            let pred_info = self.dfs_info[pred];
            if header_info.is_ancestor_of(&pred_info) {
                self.worklist.push(pred);
            } else if pred_info.is_reached() {
                is_entry = true;
            }
        }

        if is_entry {
            debug_assert!(!self.cycle_entries.contains(&(cycle, block)));
            self.cycle_entries.push((cycle, block));
        }

        Ok(())
    }

    /// Assign every block that cycle-discovery left unclaimed the top-level
    /// region, so that regions partition all of the function's blocks.
    ///
    /// Unreachable blocks land here too: we have nothing better to say about
    /// them, and giving them a region keeps every later pass total.
    fn construct_block_regions(
        &mut self,
        func: &impl InputFunction,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        let entry = output.with_repr(func.entry_block())?;

        let root = output.entity::<Region<E>>(entry.index())?;
        debug_assert!(self.block_region[entry].is_none_or(|r| r == root));
        self.root = Some(root);
        self.block_region[entry] = Some(root);

        for (block, _) in func.blocks() {
            let block = output.with_repr(block)?;
            if self.block_region[block].is_none() {
                self.block_region[block] = Some(root);
            }
        }

        // A cycle nothing adopted sits directly inside the top level.
        for (block, _) in func.blocks() {
            let block = output.with_repr(block)?;
            let region = self.block_region[block].unwrap();
            if region != root && self.region_parent[region].is_none() {
                self.region_parent[region] = Some(root);
            }
        }

        debug_assert!(self.region_parent[root].is_none());
        Ok(())
    }

    /// Move each region's cold blocks into a cold child region.
    ///
    /// The block naming a region stays in it, which also keeps every cold
    /// region's own name, its first cold block, distinct from every other
    /// region's.
    fn construct_cold_regions(
        &mut self,
        func: &impl InputFunction,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        for (block, input_block) in func.blocks() {
            if !input_block.frequency().is_cold() {
                continue;
            }
            let block = output.with_repr(block)?;
            let region = block.region(self);
            if region.index() == block.index() {
                continue;
            }

            let cold = match self.cold_child[region] {
                Some(cold) => cold,
                None => {
                    let cold = output.entity::<Region<E>>(block.index())?;
                    self.cold_child[region] = Some(cold);
                    self.region_parent[cold] = Some(region);
                    self.cold_regions.insert(cold);
                    cold
                }
            };
            self.block_region[block] = Some(cold);
        }

        self.cold_child.reset();
        Ok(())
    }

    /// Lay each region's blocks out contiguously within
    /// `region_blocks_storage`.
    fn construct_region_blocks(
        &mut self,
        func: &impl InputFunction,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        // We learn each block's region in layout order, but any one region's
        // blocks are scattered throughout that order, so sort the blocks by
        // region before copying them into their contiguous storage.
        self.blocks_by_region.reserve(func.len_blocks());
        for (block, _) in func.blocks() {
            let block = output.with_repr(block)?;
            let region = block.region(&self);
            self.blocks_by_region.push((region, block));
        }
        self.blocks_by_region.sort_unstable();

        self.region_blocks_storage
            .reserve(self.blocks_by_region.len());

        let mut i = 0;
        while i < self.blocks_by_region.len() {
            let region = self.blocks_by_region[i].0;
            self.distinct_regions.push(region);

            let start = self.region_blocks_storage.next_key(output)?;
            while i < self.blocks_by_region.len() && self.blocks_by_region[i].0 == region {
                let block = self.blocks_by_region[i].1;
                self.region_blocks_storage.push(output, block)?;
                i += 1;
            }
            let end = self.region_blocks_storage.next_key(output)?;

            self.region_blocks[region] = EntityRange { start, end };
        }

        self.blocks_by_region.clear();
        Ok(())
    }

    /// Lay each region's children out contiguously within
    /// `region_children_storage`.
    fn construct_region_tree(&mut self, output: &mut OutputInner<E>) -> IResult<()> {
        self.children_by_parent.reserve(self.distinct_regions.len());
        for i in 0..self.distinct_regions.len() {
            let region = self.distinct_regions[i];
            if let Some(parent) = self.region_parent[region] {
                self.children_by_parent.push((parent, region));
            }
        }

        // As with a region's blocks, we learn about children before we know how
        // many any given parent has, so sort by parent to lay each parent's
        // children out contiguously.
        self.children_by_parent.sort_unstable();

        self.region_children_storage
            .reserve(self.children_by_parent.len());

        let mut i = 0;
        while i < self.children_by_parent.len() {
            let parent = self.children_by_parent[i].0;

            let start = self.region_children_storage.next_key(output)?;
            while i < self.children_by_parent.len() && self.children_by_parent[i].0 == parent {
                let child = self.children_by_parent[i].1;
                self.region_children_storage.push(output, child)?;
                i += 1;
            }
            let end = self.region_children_storage.next_key(output)?;

            self.region_children[parent] = EntityRange { start, end };
        }

        self.children_by_parent.clear();
        Ok(())
    }

    /// Fill `pre_order` with a pre-order traversal of the region tree, and
    /// `region_depth` along the way.
    fn construct_pre_order(&mut self) {
        let mut pre_order = core::mem::take(&mut self.pre_order);
        let mut stack = core::mem::take(&mut self.pre_order_stack);
        debug_assert!(pre_order.is_empty());
        debug_assert!(stack.is_empty());

        pre_order.reserve(self.distinct_regions.len());

        stack.push(self.root());
        while let Some(region) = stack.pop() {
            pre_order.push(region);

            // A parent is always visited before its children. A cold region
            // is not a loop, so it has its parent's depth.
            self.region_depth[region] = match region.parent(self) {
                Some(parent) if self.is_cold(region) => self.region_depth[parent],
                Some(parent) => self.region_depth[parent] + 1,
                None => 0,
            };

            // Push the children in reverse so that they are popped, and
            // therefore visited, in order.
            stack.extend(region.children(self).rev());
        }

        self.pre_order = pre_order;
        self.pre_order_stack = stack;
    }

    /// Get the root of the region tree: the function entry block's region.
    #[allow(dead_code, reason = "will probably need it")]
    pub fn root(&self) -> Region<E> {
        self.root
            .expect("should always have a root after construction")
    }

    /// Is this one of the cold regions split off from their parent?
    pub(crate) fn is_cold(&self, region: Region<E>) -> bool {
        self.cold_regions.contains(region)
    }

    /// Is `inner` the same region as `outer`, or nested inside it?
    pub(crate) fn encloses(&self, outer: Region<E>, inner: Region<E>) -> bool {
        let mut region = Some(inner);
        while let Some(r) = region {
            if r == outer {
                return true;
            }
            region = r.parent(self);
        }
        false
    }

    /// Iterate over this tree's regions in pre-order: every region appears
    /// exactly once, and always before any of its descendants.
    ///
    /// Iterating in reverse therefore gives a bottom-up order, where every
    /// region appears after all of its descendants.
    pub(crate) fn pre_order_iter(
        &self,
    ) -> impl ExactSizeIterator<Item = Region<E>> + DoubleEndedIterator + '_ {
        self.pre_order.iter().copied()
    }
}

impl<E> Block<E>
where
    E: EntityRepr,
{
    /// Get the region containing this block.
    pub(crate) fn region(self, region_tree: &RegionTree<E>) -> Region<E> {
        region_tree.block_region[self].expect("every block has a region after construction")
    }

    /// How many loops contain this block: the number of ancestors of its loop
    /// region.
    ///
    /// A cycle headed by the entry block is the top-level region itself, so its
    /// blocks are at depth zero.
    pub(crate) fn loop_depth(self, region_tree: &RegionTree<E>) -> u32 {
        self.region(region_tree).loop_depth(region_tree)
    }
}

impl<E> Region<E>
where
    E: EntityRepr,
{
    /// Get the blocks in this region.
    pub(crate) fn blocks(
        self,
        region_tree: &RegionTree<E>,
    ) -> impl ExactSizeIterator<Item = Block<E>> + '_ {
        region_tree.region_blocks[self].indices().map(move |i| {
            let i = RegionBlocksStorageIndex::try_new(i).unwrap();
            region_tree.region_blocks_storage[i]
        })
    }

    /// Get the innermost loop region holding this region's blocks: the region
    /// itself, or for a cold region, its parent.
    pub(crate) fn loop_region(self, region_tree: &RegionTree<E>) -> Region<E> {
        match region_tree.is_cold(self) {
            true => self.parent(region_tree).unwrap(),
            false => self,
        }
    }

    /// Get the parent of this region, or `None` if this is the top-level
    /// region.
    pub(crate) fn parent(self, region_tree: &RegionTree<E>) -> Option<Region<E>> {
        region_tree.region_parent[self]
    }

    /// How many cycles of the control-flow graph contain this region's blocks:
    /// zero for the top-level region. A cold region is not a cycle of its own.
    ///
    /// A cycle headed by the entry block is the top-level region itself, so
    /// its blocks are at depth zero. An irreducible cycle's nesting depends on
    /// traversal order.
    pub(crate) fn loop_depth(self, region_tree: &RegionTree<E>) -> u32 {
        region_tree.region_depth[self]
    }

    /// Get the immediate child regions of this region.
    pub(crate) fn children(
        self,
        region_tree: &RegionTree<E>,
    ) -> impl ExactSizeIterator<Item = Region<E>> + DoubleEndedIterator + '_ {
        region_tree.region_children[self].indices().map(move |i| {
            let i = RegionChildrenStorageIndex::try_new(i).unwrap();
            region_tree.region_children_storage[i]
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test::TestFunction;
    use mutatis::check::{Check, CheckResult};
    use std::{
        collections::{BTreeMap, BTreeSet, HashMap},
        format,
        string::{String, ToString},
    };

    /// A construction that bailed with `EntityReprTooSmall` never reached the cleanup
    /// at the end of its walk, and `Context::reset` resets that abandoned
    /// context too, so `reset` has to clear the scratch rather than assume it.
    #[test]
    fn reset_clears_scratch_from_an_abandoned_construction() {
        let mut region_tree = RegionTree::<u8>::new();

        region_tree.dfs_pre_order.push(Block::try_new(0).unwrap());
        region_tree.worklist.push(Block::try_new(1).unwrap());
        region_tree
            .distinct_regions
            .push(Region::try_new(0).unwrap());
        assert!(!region_tree.is_reset());

        region_tree.reset();
        assert!(region_tree.is_reset());
    }

    /// A region, identified by the blocks of the cycle that defines it plus
    /// those of every cycle nested inside it.
    ///
    /// Identifying regions this way keeps the tests independent of how the
    /// region tree numbers things.
    type RegionId = BTreeSet<Block>;

    /// Construct the region tree for `func`.
    fn construct(func: &TestFunction) -> Result<RegionTree<u32>, String> {
        let mut counts = Counts::new();
        let mut output = OutputInner::<u32>::new();
        let mut dfs = Dfs::<u32>::new();

        let mut tree = RegionTree::<u32>::new();
        assert!(tree.is_reset());
        if tree
            .construct(func, &mut counts, &mut dfs, &mut output)
            .is_err()
        {
            return Err(format!(
                "`RegionTree::construct` failed: {:?}",
                output.take_error()
            ));
        }
        if tree.is_reset() {
            return Err("`is_reset` is true after a successful `construct`".to_string());
        }

        Ok(tree)
    }

    /// Compute the set of blocks reachable from the entry block without ever
    /// entering `avoid`.
    ///
    /// A plain worklist over `successors()`, so that the oracles built on top
    /// of it depend on neither `Dfs`, `StronglyConnectedComponents`,
    /// `DominatorTree`, nor `RegionTree`.
    fn reachable_avoiding(func: &TestFunction, avoid: Option<Block>) -> BTreeSet<Block> {
        let mut visited = BTreeSet::new();

        let entry = func.entry_block();
        if Some(entry) == avoid {
            return visited;
        }
        visited.insert(entry);

        let mut worklist = alloc::vec![entry];
        while let Some(block) = worklist.pop() {
            for succ in func.block(block).successors() {
                if Some(succ) == avoid {
                    continue;
                }
                if visited.insert(succ) {
                    worklist.push(succ);
                }
            }
        }

        visited
    }

    /// Compute the set of blocks reachable from `start`, including `start`
    /// itself.
    fn reachable_from(func: &TestFunction, start: Block) -> BTreeSet<Block> {
        let mut visited = BTreeSet::new();
        visited.insert(start);

        let mut worklist = alloc::vec![start];
        while let Some(block) = worklist.pop() {
            for succ in func.block(block).successors() {
                if visited.insert(succ) {
                    worklist.push(succ);
                }
            }
        }

        visited
    }

    /// For each block, compute the set of blocks that dominate it: `a`
    /// dominates `b` when every control-flow path from the entry block to `b`
    /// goes through `a`, which is exactly when `b` becomes unreachable once `a`
    /// is removed from the CFG.
    fn dominators_oracle(func: &TestFunction) -> HashMap<Block, BTreeSet<Block>> {
        let reachable = reachable_avoiding(func, None);

        let mut dominators: HashMap<Block, BTreeSet<Block>> =
            reachable.iter().map(|&b| (b, BTreeSet::new())).collect();

        for (a, _) in func.blocks() {
            let without_a = reachable_avoiding(func, Some(a));
            for &b in reachable.difference(&without_a) {
                dominators.get_mut(&b).unwrap().insert(a);
            }
        }

        dominators
    }

    /// Derive each block's immediate dominator from the dominance relation: it
    /// is the strict dominator of the block that every other strict dominator
    /// of the block also dominates.
    fn idoms_oracle(dominators: &HashMap<Block, BTreeSet<Block>>) -> HashMap<Block, Option<Block>> {
        dominators
            .iter()
            .map(|(&b, doms)| {
                let strict: BTreeSet<Block> = doms.iter().copied().filter(|&d| d != b).collect();
                let idom = strict
                    .iter()
                    .copied()
                    .find(|&d| strict.iter().all(|s| dominators[&d].contains(s)));
                (b, idom)
            })
            .collect()
    }

    /// For each block, compute the set of blocks making up its
    /// strongly-connected component: the blocks that it and they can reach each
    /// other from.
    fn sccs_oracle(func: &TestFunction) -> HashMap<Block, BTreeSet<Block>> {
        let reachable: HashMap<Block, BTreeSet<Block>> = func
            .blocks()
            .map(|(b, _)| (b, reachable_from(func, b)))
            .collect();

        reachable
            .keys()
            .map(|a| {
                let component = reachable
                    .keys()
                    .copied()
                    .filter(|b| reachable[a].contains(b) && reachable[b].contains(a))
                    .collect();
                (*a, component)
            })
            .collect()
    }

    /// Is this control-flow graph reducible?
    ///
    /// Hecht and Ullman's characterization: every strongly-connected component
    /// has exactly one entry, and the component minus that header is itself
    /// reducible. The recursion is needed because a single-entry cycle can
    /// still hold an irreducible one.
    ///
    /// Phrased in edges and reachability alone, with no depth-first traversal,
    /// which is what makes it usable against a traversal-dependent
    /// decomposition.
    fn is_reducible(func: &TestFunction) -> bool {
        let entry = func.entry_block();
        let all: BTreeSet<Block> = reachable_avoiding(func, None);

        // Reachability within `nodes`, by plain worklist so that it depends on
        // nothing under test.
        fn reachable_within(
            func: &TestFunction,
            nodes: &BTreeSet<Block>,
            from: Block,
        ) -> BTreeSet<Block> {
            let mut seen = BTreeSet::from([from]);
            let mut worklist = alloc::vec![from];
            while let Some(b) = worklist.pop() {
                for succ in func.block(b).successors() {
                    if nodes.contains(&succ) && seen.insert(succ) {
                        worklist.push(succ);
                    }
                }
            }
            seen
        }

        // Is the subgraph induced by `nodes` reducible?
        fn check(func: &TestFunction, entry: Block, nodes: &BTreeSet<Block>) -> bool {
            // Two blocks share a component when each reaches the other without
            // leaving `nodes`.
            let forward: BTreeMap<Block, BTreeSet<Block>> = nodes
                .iter()
                .map(|&b| (b, reachable_within(func, nodes, b)))
                .collect();

            let mut remaining: BTreeSet<Block> = nodes.clone();
            while let Some(&a) = remaining.iter().next() {
                let component: BTreeSet<Block> = nodes
                    .iter()
                    .copied()
                    .filter(|b| forward[&a].contains(b) && forward[b].contains(&a))
                    .collect();
                for b in &component {
                    remaining.remove(b);
                }

                // A single block with no edge to itself is not a cycle.
                let has_self_edge = func.block(a).successors().any(|s| s == a);
                if component.len() == 1 && !has_self_edge {
                    continue;
                }

                // Control enters at the function's entry block and at any
                // member with a predecessor outside the component.
                let entries: BTreeSet<Block> = component
                    .iter()
                    .copied()
                    .filter(|&b| {
                        b == entry
                            || func
                                .block(b)
                                .predecessors()
                                .any(|p| !component.contains(&p))
                    })
                    .collect();
                if entries.len() != 1 {
                    return false;
                }

                // Dropping the header exposes an inner cycle that is
                // irreducible even when this one is not.
                let header = *entries.iter().next().unwrap();
                let rest: BTreeSet<Block> =
                    component.iter().copied().filter(|&b| b != header).collect();
                if !rest.is_empty() && !check(func, entry, &rest) {
                    return false;
                }
            }

            true
        }

        check(func, entry, &all)
    }

    /// For each block that heads a natural loop, compute that loop's blocks.
    ///
    /// A back edge `u -> h` is one whose target dominates its source, and its
    /// loop body is `h` plus every block reaching such a `u` without passing
    /// through `h`.
    ///
    /// Only meaningful for a reducible CFG, whose cycles are all induced by
    /// back edges.
    fn natural_loops_oracle(
        func: &TestFunction,
        dominators: &HashMap<Block, BTreeSet<Block>>,
    ) -> BTreeMap<Block, BTreeSet<Block>> {
        // Computed from `successors` alone, so it depends on nothing under
        // test.
        let can_reach_avoiding = |from: Block, to: Block, avoid: Block| -> bool {
            if from == avoid {
                return false;
            }
            let mut visited = BTreeSet::from([from]);
            let mut worklist = alloc::vec![from];
            while let Some(b) = worklist.pop() {
                if b == to {
                    return true;
                }
                for succ in func.block(b).successors() {
                    if succ != avoid && visited.insert(succ) {
                        worklist.push(succ);
                    }
                }
            }
            from == to
        };

        let mut loops: BTreeMap<Block, BTreeSet<Block>> = BTreeMap::new();
        for (u, data) in func.blocks() {
            for h in data.successors() {
                // Only a back edge induces a loop.
                if !dominators[&u].contains(&h) {
                    continue;
                }
                let body = loops.entry(h).or_insert_with(|| BTreeSet::from([h]));
                for (b, _) in func.blocks() {
                    if b != h && can_reach_avoiding(b, u, h) {
                        body.insert(b);
                    }
                }
            }
        }
        loops
    }

    /// For each block, compute the region containing it: the innermost natural
    /// loop that contains it, or the top level when none does.
    ///
    /// A loop headed by the entry block *is* the top-level region, since both
    /// are named by that block, so blocks after such a loop stay in it.
    ///
    /// Only meaningful for a reducible CFG; see `natural_loops_oracle`.
    fn regions_oracle(
        func: &TestFunction,
        loops: &BTreeMap<Block, BTreeSet<Block>>,
    ) -> HashMap<Block, RegionId> {
        let entry = func.entry_block();
        let all: BTreeSet<Block> = func.blocks().map(|(b, _)| b).collect();

        func.blocks()
            .map(|(b, _)| {
                // Loops are well nested, so innermost is smallest.
                let innermost = loops
                    .iter()
                    .filter(|(_, body)| body.contains(&b))
                    .min_by_key(|(_, body)| body.len());
                match innermost {
                    Some((header, body)) if *header != entry => (b, body.clone()),
                    _ => (b, all.clone()),
                }
            })
            .collect()
    }

    /// Build a region tree with the given shape directly, without going through
    /// a control-flow graph: `children[i]` holds the child regions of region
    /// `i`, and region `0` is the root.
    ///
    /// The generated `TestFunction`s are small enough that their region trees
    /// are never more than a root and a single child, which is not enough to
    /// tell a pre-order traversal apart from any other order that visits
    /// parents first. This lets us check the traversal itself against shapes
    /// that do.
    fn tree_with_shape(children: &[&[usize]]) -> RegionTree<u32> {
        let mut output = OutputInner::<u32>::new();
        let mut tree = RegionTree::<u32>::new();

        let region = |i: usize| Region::<u32>::try_new(i).unwrap();
        tree.root = Some(region(0));

        for (parent, kids) in children.iter().enumerate() {
            let start = tree.region_children_storage.next_key(&mut output).unwrap();
            for &kid in *kids {
                tree.region_parent[region(kid)] = Some(region(parent));
                tree.region_children_storage
                    .push(&mut output, region(kid))
                    .unwrap();
            }
            let end = tree.region_children_storage.next_key(&mut output).unwrap();
            tree.region_children[region(parent)] = EntityRange { start, end };
        }

        tree.construct_pre_order();
        tree
    }

    /// `pre_order_iter` is depth-first, visiting each region's children in
    /// order, and not merely parents-before-children.
    #[test]
    fn pre_order_iter_is_depth_first() {
        // region0
        // ├── region1
        // │   ├── region2
        // │   └── region3
        // └── region4
        //     └── region5
        let tree = tree_with_shape(&[&[1, 4], &[2, 3], &[], &[], &[5], &[]]);

        let actual: Vec<usize> = tree.pre_order_iter().map(|r| r.index()).collect();
        assert_eq!(actual, alloc::vec![0, 1, 2, 3, 4, 5]);

        let backwards: Vec<usize> = tree.pre_order_iter().rev().map(|r| r.index()).collect();
        assert_eq!(backwards, alloc::vec![5, 4, 3, 2, 1, 0]);
    }

    /// Each region's memoized depth is how many ancestors it has.
    #[test]
    fn loop_depth_counts_ancestors() {
        // Same shape as `pre_order_iter_is_depth_first`.
        let tree = tree_with_shape(&[&[1, 4], &[2, 3], &[], &[], &[5], &[]]);
        let actual: Vec<u32> = tree.pre_order_iter().map(|r| r.loop_depth(&tree)).collect();
        assert_eq!(actual, alloc::vec![0, 1, 2, 2, 1, 2]);
    }

    /// The memoized depth counts the loops enclosing a region's blocks, which
    /// a cold region does not add to.
    #[test]
    fn loop_depth_counts_enclosing_loops() -> CheckResult<TestFunction> {
        Check::new()
            .min_iters(2_000)
            .run(|func: &TestFunction| -> Result<(), String> {
                let tree = construct(func)?;
                for region in tree.pre_order_iter() {
                    let mut walk = region.loop_region(&tree);
                    let mut want = 0;
                    while let Some(parent) = walk.parent(&tree) {
                        walk = parent.loop_region(&tree);
                        want += 1;
                    }
                    if region.loop_depth(&tree) != want {
                        return Err(format!(
                            "{region:?} has memoized depth {}, but {want} enclosing loops",
                            region.loop_depth(&tree),
                        ));
                    }
                }
                Ok(())
            })
    }

    /// A tree that is a single chain, and one that is a single region.
    #[test]
    fn pre_order_iter_degenerate_shapes() {
        let tree = tree_with_shape(&[&[1], &[2], &[]]);
        let actual: Vec<usize> = tree.pre_order_iter().map(|r| r.index()).collect();
        assert_eq!(actual, alloc::vec![0, 1, 2]);

        let tree = tree_with_shape(&[&[]]);
        let actual: Vec<usize> = tree.pre_order_iter().map(|r| r.index()).collect();
        assert_eq!(actual, alloc::vec![0]);
    }

    #[test]
    fn pre_order_iter_properties() -> CheckResult<TestFunction> {
        Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run(|func: &TestFunction| -> Result<(), String> {
                let tree = construct(func)?;

                let pre_order: Vec<Region> = tree.pre_order_iter().collect();

                // Property 1: the traversal visits every region exactly once.
                let mut seen = BTreeSet::new();
                for region in &pre_order {
                    if !seen.insert(*region) {
                        return Err(format!(
                            "`pre_order_iter` visits {region:?} more than once: {pre_order:?}"
                        ));
                    }
                }
                let expected: BTreeSet<Region> =
                    func.blocks().map(|(b, _)| b.region(&tree)).collect();
                if seen != expected {
                    return Err(format!(
                        "`pre_order_iter` visits {seen:?} but the function's regions are \
                         {expected:?}"
                    ));
                }

                // Property 2: the iterator reports its length correctly, and
                // iterating from the back gives the same sequence reversed.
                if tree.pre_order_iter().len() != pre_order.len() {
                    return Err(format!(
                        "`pre_order_iter().len()` is {} but it yields {} regions",
                        tree.pre_order_iter().len(),
                        pre_order.len(),
                    ));
                }
                let mut backwards: Vec<Region> = tree.pre_order_iter().rev().collect();
                backwards.reverse();
                if backwards != pre_order {
                    return Err(format!(
                        "`pre_order_iter` yields {pre_order:?} forwards but {:?} backwards",
                        backwards.iter().rev().collect::<Vec<_>>(),
                    ));
                }

                // Property 3: the root comes first, and every other region comes
                // after its parent.
                let position: HashMap<Region, usize> = pre_order
                    .iter()
                    .enumerate()
                    .map(|(i, &region)| (region, i))
                    .collect();
                let root = tree.root();
                if pre_order.first() != Some(&root) {
                    return Err(format!(
                        "`pre_order_iter` starts with {:?} but the root region is {root:?}",
                        pre_order.first(),
                    ));
                }
                for (i, region) in pre_order.iter().enumerate() {
                    if let Some(parent) = region.parent(&tree) {
                        if position[&parent] >= i {
                            return Err(format!(
                                "{region:?} is at index {i} but its parent {parent:?} is at \
                                 index {}, so the traversal is not a pre-order",
                                position[&parent],
                            ));
                        }
                    }
                }

                // Property 4: the traversal is depth-first, not merely
                // parent-before-child: each region's descendants occupy the
                // entries immediately following it.
                let mut descendants: HashMap<Region, BTreeSet<Region>> =
                    pre_order.iter().map(|&r| (r, BTreeSet::new())).collect();
                for region in &pre_order {
                    let mut curr = region.parent(&tree);
                    while let Some(ancestor) = curr {
                        descendants.get_mut(&ancestor).unwrap().insert(*region);
                        curr = ancestor.parent(&tree);
                    }
                }
                for (i, region) in pre_order.iter().enumerate() {
                    let subtree = &descendants[region];
                    let actual: BTreeSet<Region> = pre_order[i + 1..][..subtree.len()]
                        .iter()
                        .copied()
                        .collect();
                    if actual != *subtree {
                        return Err(format!(
                            "{region:?}'s descendants are {subtree:?}, but the {} entries \
                             following it in {pre_order:?} are {actual:?}",
                            subtree.len(),
                        ));
                    }
                }

                Ok(())
            })
    }

    #[test]
    fn region_tree_properties() -> CheckResult<TestFunction> {
        Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run(|func: &TestFunction| -> Result<(), String> {
                let entry = func.entry_block();
                let blocks: Vec<Block> = func.blocks().map(|(b, _)| b).collect();

                // `TestFunction::fixup` is supposed to make every block reachable
                // from the entry block. If it didn't, that's a bug in the generator
                // rather than in the region tree, so check it on its own.
                let reachable = reachable_avoiding(func, None);
                if reachable.len() != blocks.len() {
                    return Err(format!(
                        "only {} of this function's {} blocks are reachable from {entry:?}; \
                         `TestFunction::fixup` should have made them all reachable",
                        reachable.len(),
                        blocks.len(),
                    ));
                }

                let tree = construct(func)?;

                let dominators = dominators_oracle(func);
                let idoms = idoms_oracle(&dominators);
                let oracle_sccs = sccs_oracle(func);

                // An irreducible graph's decomposition depends on the
                // depth-first traversal's choices, so there is no oracle for
                // it. A reducible one has canonical natural loops.
                let reducible = is_reducible(func);
                let oracle_loops = natural_loops_oracle(func, &dominators);
                let oracle_regions = regions_oracle(func, &oracle_loops);

                // A region's blocks plus those of every region nested inside
                // it. This, not `Region::blocks`, is what corresponds to a
                // cycle: `blocks` reports only the blocks whose *innermost*
                // region this is.
                let closure = |tree: &RegionTree<u32>, region: Region| -> BTreeSet<Block> {
                    let mut blocks = BTreeSet::new();
                    let mut stack = alloc::vec![region];
                    while let Some(r) = stack.pop() {
                        blocks.extend(r.blocks(tree));
                        stack.extend(r.children(tree));
                    }
                    blocks
                };

                // Property 1: the regions partition the blocks, and, when
                // there is a canonical answer to compare against, the loop
                // regions group them exactly as the oracle does.
                //
                // `blocks()` covering every block once and agreeing with
                // `Block::region` gives the partition; comparing the groupings
                // gives the agreement.
                let mut actual_groups: BTreeMap<Region, BTreeSet<Block>> = BTreeMap::new();
                let mut loop_groups: BTreeMap<Region, BTreeSet<Block>> = BTreeMap::new();
                for b in &blocks {
                    actual_groups
                        .entry(b.region(&tree))
                        .or_default()
                        .insert(*b);
                    loop_groups
                        .entry(b.region(&tree).loop_region(&tree))
                        .or_default()
                        .insert(*b);
                }
                if reducible {
                    let mut expected_groups: BTreeMap<RegionId, BTreeSet<Block>> = BTreeMap::new();
                    for b in &blocks {
                        expected_groups
                            .entry(oracle_regions[b].clone())
                            .or_default()
                            .insert(*b);
                    }
                    let actual_partition: BTreeSet<&BTreeSet<Block>> =
                        loop_groups.values().collect();
                    let expected_partition: BTreeSet<&BTreeSet<Block>> =
                        expected_groups.values().collect();
                    if actual_partition != expected_partition {
                        return Err(format!(
                            "the regions group the blocks as {actual_partition:?} but should group \
                             them as {expected_partition:?}"
                        ));
                    }
                }

                let regions: Vec<Region> = actual_groups.keys().copied().collect();
                for region in &regions {
                    let listed: BTreeSet<Block> = region.blocks(&tree).collect();
                    if listed.len() != region.blocks(&tree).len() {
                        return Err(format!(
                            "`blocks({region:?})` repeats a block: {:?}",
                            region.blocks(&tree).collect::<Vec<_>>(),
                        ));
                    }
                    if listed != actual_groups[region] {
                        return Err(format!(
                            "`blocks({region:?})` is {listed:?} but the blocks whose `region` \
                             is {region:?} are {:?}",
                            actual_groups[region],
                        ));
                    }
                }

                // Property 2: a region is named by its header block, which is
                // the entry block for the top-level region.
                let entry_region = Region::<u32>::try_new(entry.index()).unwrap();
                if tree.root() != entry_region {
                    return Err(format!(
                        "the root region is {:?} but {entry:?} is the entry block, so it should \
                         be {entry_region:?}",
                        tree.root(),
                    ));
                }
                for region in &regions {
                    let header = Block::try_new(region.index()).unwrap();
                    if !closure(&tree, *region).contains(&header) {
                        return Err(format!(
                            "{region:?} should be named by a block it contains, but its blocks \
                             are {:?}, which does not include {header:?}",
                            closure(&tree, *region),
                        ));
                    }
                    if header.region(&tree) != *region {
                        return Err(format!(
                            "{region:?} is named by {header:?}, but that block's own region is \
                             {:?}; a region's header always belongs to it directly, never to one \
                             of its children",
                            header.region(&tree),
                        ));
                    }
                }

                // Property 3: a natural loop is never split across regions.
                // A strongly-connected component holding a loop nest is split,
                // deliberately; an individual loop is not.
                for (header, body) in &oracle_loops {
                    let region = header.region(&tree);
                    let region_blocks = closure(&tree, region);
                    for b in body {
                        if !region_blocks.contains(b) {
                            return Err(format!(
                                "{b:?} is in the natural loop headed by {header:?}, whose body is \
                                 {body:?}, but that loop's region {region:?} holds only \
                                 {region_blocks:?}"
                            ));
                        }
                    }
                }

                // Property 3b: a region never spans two strongly-connected
                // components, so it splits one only along that component's own
                // structure. Unlike the oracle comparison, this holds for
                // irreducible control flow too.
                for region in &regions {
                    let region = &region.loop_region(&tree);
                    if *region == tree.root() {
                        continue;
                    }
                    let region_blocks = closure(&tree, *region);
                    let header = Block::try_new(region.index()).unwrap();
                    for b in &region_blocks {
                        if !oracle_sccs[&header].contains(b) {
                            return Err(format!(
                                "{region:?} holds {region_blocks:?}, but {b:?} is not in the \
                                 strongly-connected component {:?} of its header {header:?}, so \
                                 the region is not strongly connected",
                                oracle_sccs[&header],
                            ));
                        }
                    }
                }

                // Property 4: the block and children ranges tile their storage
                // contiguously, with no gaps and no overlap.
                let mut next_start = 0;
                for region in &regions {
                    let range = tree.region_blocks[*region];
                    if range.indices().start != next_start {
                        return Err(format!(
                            "{region:?}'s blocks start at {} but the previous region's blocks ended \
                             at {next_start}",
                            range.indices().start,
                        ));
                    }
                    next_start = range.indices().end;
                }
                if next_start != tree.region_blocks_storage.len() {
                    return Err(format!(
                        "the regions' block ranges cover {next_start} blocks but \
                         `region_blocks_storage` holds {}",
                        tree.region_blocks_storage.len(),
                    ));
                }

                let mut next_start = 0;
                for region in &regions {
                    let range = tree.region_children[*region];
                    if range.is_empty() {
                        continue;
                    }
                    if range.indices().start != next_start {
                        return Err(format!(
                            "{region:?}'s children start at {} but the previous region's children \
                             ended at {next_start}",
                            range.indices().start,
                        ));
                    }
                    next_start = range.indices().end;
                }
                if next_start != tree.region_children_storage.len() {
                    return Err(format!(
                        "the regions' children ranges cover {next_start} regions but \
                         `region_children_storage` holds {}",
                        tree.region_children_storage.len(),
                    ));
                }

                // Property 5: the regions form a tree rooted at the region
                // containing the entry block, which is the region that `root`
                // reports.
                let root = tree.root();
                if root != entry.region(&tree) {
                    return Err(format!(
                        "`root()` is {root:?} but {entry:?}'s region is {:?}",
                        entry.region(&tree),
                    ));
                }
                if !root.blocks(&tree).any(|b| b == entry) {
                    return Err(format!(
                        "`root()` is {root:?}, but its blocks are {:?}, which do not include the \
                         entry block {entry:?}",
                        root.blocks(&tree).collect::<Vec<_>>(),
                    ));
                }
                for region in &regions {
                    let parent = region.parent(&tree);
                    if (*region == root) != parent.is_none() {
                        return Err(format!(
                            "`parent({region:?})` is {parent:?}, but {region:?} is {}the region \
                             containing {entry:?}",
                            if *region == root { "" } else { "not " },
                        ));
                    }
                }
                for region in &regions {
                    let mut chain = BTreeSet::new();
                    let mut curr = Some(*region);
                    while let Some(r) = curr {
                        if !chain.insert(r) {
                            return Err(format!(
                                "the parent chain of {region:?} revisits {r:?}, so the regions do \
                                 not form a tree"
                            ));
                        }
                        curr = r.parent(&tree);
                    }
                    if !chain.contains(&root) {
                        return Err(format!(
                            "the parent chain of {region:?} is {chain:?}, which does not reach the \
                             root region {root:?}"
                        ));
                    }
                }

                // Property 6: `children` is exactly the inverse of `parent`.
                let mut children = BTreeSet::new();
                for region in &regions {
                    for child in region.children(&tree) {
                        if !children.insert(child) {
                            return Err(format!("{child:?} is a child of more than one region"));
                        }
                        if child.parent(&tree) != Some(*region) {
                            return Err(format!(
                                "{child:?} is listed as a child of {region:?} but its parent is {:?}",
                                child.parent(&tree),
                            ));
                        }
                    }
                }
                let expected_children: BTreeSet<Region> =
                    regions.iter().copied().filter(|r| *r != root).collect();
                if children != expected_children {
                    return Err(format!(
                        "the regions' children are {children:?}, but every region except the root \
                         {root:?} should be a child of some region"
                    ));
                }

                // Property 7: the region tree is the cycle nest, so a region's
                // parent is the innermost region whose block set strictly
                // contains its own. Stated over `closure`, since a child's
                // `blocks` is disjoint from its parent's, not a subset.
                for region in &regions {
                    let own = closure(&tree, *region);

                    let strict_supersets: Vec<Region> = regions
                        .iter()
                        .copied()
                        .filter(|other| {
                            *other != *region && closure(&tree, *other).is_superset(&own)
                        })
                        .collect();

                    // Cycles nest, so the innermost is the smallest.
                    let expected = strict_supersets
                        .iter()
                        .copied()
                        .min_by_key(|other| closure(&tree, *other).len());

                    if region.parent(&tree) != expected {
                        return Err(format!(
                            "`parent({region:?})` is {:?}, but {region:?} holds {own:?} and the \
                             innermost region strictly containing that is {expected:?}",
                            region.parent(&tree),
                        ));
                    }
                }

                // Property 8: an ancestor region's nearest common dominator
                // dominates every block of a descendant region.
                //
                // Reducible graphs only: an irreducible cycle can be entered at
                // more than one block, and then no block of it dominates the
                // rest.
                let ncd = |a: Block, b: Block| -> Block {
                    let mut a = a;
                    while !dominators[&b].contains(&a) {
                        a = idoms[&a].expect("the entry block dominates every reachable block");
                    }
                    a
                };
                if reducible {
                    for region in &regions {
                        let mut curr = region.parent(&tree);
                        while let Some(ancestor) = curr {
                            let mut ancestor_blocks = ancestor.blocks(&tree);
                            let mut ancestor_ncd =
                                ancestor_blocks.next().expect("regions are never empty");
                            for b in ancestor_blocks {
                                ancestor_ncd = ncd(ancestor_ncd, b);
                            }

                            for b in region.blocks(&tree) {
                                if !dominators[&b].contains(&ancestor_ncd) {
                                    return Err(format!(
                                        "{region:?} is a descendant of {ancestor:?}, whose nearest \
                                         common dominator {ancestor_ncd:?} does not dominate \
                                         {region:?}'s block {b:?}"
                                    ));
                                }
                            }

                            curr = ancestor.parent(&tree);
                        }
                    }
                }

                // Property 8b: a cold region is a leaf holding only cold
                // blocks, split off from a loop region, and every cold block
                // that does not name its region is in one.
                for region in &regions {
                    if !tree.is_cold(*region) {
                        continue;
                    }
                    let parent = region.parent(&tree).unwrap();
                    if tree.is_cold(parent) || region.children(&tree).len() != 0 {
                        return Err(format!(
                            "cold {region:?} has the cold parent {parent:?} or has children"
                        ));
                    }
                    if let Some(b) = region
                        .blocks(&tree)
                        .find(|b| !func.block(*b).frequency().is_cold())
                    {
                        return Err(format!("cold {region:?} holds the non-cold {b:?}"));
                    }
                }
                for b in &blocks {
                    let region = b.region(&tree);
                    if func.block(*b).frequency().is_cold()
                        && region.index() != b.index()
                        && !tree.is_cold(region)
                    {
                        return Err(format!(
                            "{b:?} is cold but is in the non-cold {region:?}, which it does not \
                             name"
                        ));
                    }
                }

                // Property 9: constructing the region tree again gives the same
                // answer, and it resets cleanly.
                let tree_again = construct(func)?;
                if tree_again.root() != root {
                    return Err(format!(
                        "constructing twice gave the roots {root:?} and {:?}",
                        tree_again.root(),
                    ));
                }
                for b in &blocks {
                    if b.region(&tree_again) != b.region(&tree) {
                        return Err(format!(
                            "constructing twice put {b:?} in {:?} and then {:?}",
                            b.region(&tree),
                            b.region(&tree_again),
                        ));
                    }
                }
                for region in &regions {
                    if region.blocks(&tree_again).collect::<Vec<_>>()
                        != region.blocks(&tree).collect::<Vec<_>>()
                    {
                        return Err(format!(
                            "constructing twice gave {region:?} different blocks"
                        ));
                    }
                    if region.parent(&tree_again) != region.parent(&tree) {
                        return Err(format!(
                            "constructing twice gave {region:?} a different parent"
                        ));
                    }
                    if region.children(&tree_again).collect::<Vec<_>>()
                        != region.children(&tree).collect::<Vec<_>>()
                    {
                        return Err(format!(
                            "constructing twice gave {region:?} different children"
                        ));
                    }
                }

                let mut tree = tree;
                tree.reset();
                if !tree.is_reset() {
                    return Err("`is_reset` is false after `reset`".to_string());
                }

                Ok(())
            })
    }
}
