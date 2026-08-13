//! The region tree.
//!
//! A region is a set of basic blocks whose contained live ranges are allocated
//! together. We never allocate across regions.
//!
//! To make this effective, we create regions for each loop in the control-flow
//! graph, and for the function's top level.
//!
//! A block's region is identified by the first strongly-connected component
//! at-or-above that block in the dominator tree that either contains more than
//! one block (i.e. is a loop) or is the entry block's component. Note that this
//! means a block that runs *after* a loop exits is still a member of that
//! loop's region when the loop dominates it.

use crate::counts::Counts;
use crate::entity::{
    EntityRange, EntityRepr, PrimaryMap, Region, RegionBlocksStorageIndex,
    RegionChildrenStorageIndex, Scc, SecondaryMap,
};
use crate::error::IResult;
use crate::input::InputFunction;
use crate::output::OutputInner;
use crate::sccs::StronglyConnectedComponents;
use crate::timing::Timing;
use crate::union_find::UnionFind;
use crate::{Block, Entity, InputBlock};
use alloc::vec::Vec;

/// The region tree for a function.
pub struct RegionTree<E>
where
    E: EntityRepr,
{
    /// The root of the region tree: the function entry block's region.
    root: Option<Region<E>>,

    /// Map from an SCC to the region's SCC representative.
    regions: UnionFind<Scc<E>>,

    /// Map from a region to the indices within `region_blocks_storage` that
    /// contain this region's blocks.
    region_blocks: SecondaryMap<Region<E>, EntityRange<RegionBlocksStorageIndex<E>>>,

    /// The contiguous storage for the blocks that belong to each region.
    region_blocks_storage: PrimaryMap<RegionBlocksStorageIndex<E>, Block<E>>,

    /// Map from a region to its parent region, or `None` for the top-level
    /// region.
    region_parent: SecondaryMap<Region<E>, Option<Region<E>>>,

    /// Map from a region to the indices within `region_children_storage` that
    /// contain this region's immediate children.
    region_children: SecondaryMap<Region<E>, EntityRange<RegionChildrenStorageIndex<E>>>,

    /// The contiguous storage for the children that belong to each region.
    region_children_storage: PrimaryMap<RegionChildrenStorageIndex<E>, Region<E>>,

    /// Scratch space: each block paired with its region, sorted by region so that
    /// we can lay each region's blocks out contiguously.
    ///
    /// Always empty outside of `construct`; a field only so that we reuse its
    /// allocation across resets.
    blocks_by_region: Vec<(Region<E>, Block<E>)>,

    /// Scratch space: the distinct regions, in increasing index order.
    ///
    /// Always empty outside of `construct`; a field only so that we reuse its
    /// allocation across resets.
    distinct_regions: Vec<Region<E>>,

    /// Scratch space: each non-top-level region paired with its parent, sorted by
    /// parent so that we can lay each region's children out contiguously.
    ///
    /// Always empty outside of `construct`; a field only so that we reuse its
    /// allocation across resets.
    children_by_parent: Vec<(Region<E>, Region<E>)>,
}

impl<E> RegionTree<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        RegionTree {
            root: None,
            regions: UnionFind::new(),
            region_blocks: SecondaryMap::new(EntityRange::empty()),
            region_blocks_storage: PrimaryMap::new(),
            region_parent: SecondaryMap::new(None),
            region_children: SecondaryMap::new(EntityRange::empty()),
            region_children_storage: PrimaryMap::new(),
            blocks_by_region: Vec::new(),
            distinct_regions: Vec::new(),
            children_by_parent: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            root,
            regions,
            region_blocks,
            region_blocks_storage,
            region_parent,
            region_children,
            region_children_storage,
            blocks_by_region,
            distinct_regions,
            children_by_parent,
        } = self;
        *root = None;
        regions.reset();
        region_blocks.reset();
        region_blocks_storage.reset();
        region_parent.reset();
        region_children.reset();
        region_children_storage.reset();
        debug_assert!(blocks_by_region.is_empty());
        debug_assert!(distinct_regions.is_empty());
        debug_assert!(children_by_parent.is_empty());
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            root,
            regions,
            region_blocks,
            region_blocks_storage,
            region_parent,
            region_children,
            region_children_storage,
            blocks_by_region,
            distinct_regions,
            children_by_parent,
        } = self;
        root.is_none()
            && regions.is_reset()
            && region_blocks.is_reset()
            && region_blocks_storage.is_reset()
            && region_parent.is_reset()
            && region_children.is_reset()
            && region_children_storage.is_reset()
            && blocks_by_region.is_empty()
            && distinct_regions.is_empty()
            && children_by_parent.is_empty()
    }

    pub fn construct(
        &mut self,
        func: &impl InputFunction,
        counts: &mut Counts,
        sccs: &StronglyConnectedComponents<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        let _timing = Timing::new("region tree");

        debug_assert!(self.blocks_by_region.is_empty());
        debug_assert!(self.distinct_regions.is_empty());
        debug_assert!(self.children_by_parent.is_empty());

        self.construct_regions(func, sccs, output)?;
        self.construct_region_blocks(func, sccs, output)?;
        self.construct_region_tree(func, sccs, output)?;

        counts.regions += self.distinct_regions.len();
        self.distinct_regions.clear();
        Ok(())
    }

    fn construct_regions(
        &mut self,
        func: &impl InputFunction,
        sccs: &StronglyConnectedComponents<E>,
        output: &mut OutputInner<E>,
    ) -> Result<(), ()> {
        let entry = output.with_repr(func.entry_block())?;
        let entry_scc = sccs.scc(entry);
        self.root = Some(Region::try_new(entry_scc.index()).unwrap());

        for (block, _) in func.blocks() {
            let block = output.with_repr(block)?;
            let mut dom: Block<E> = block;
            let mut dom_scc = sccs.scc(block);
            while dom_scc != entry_scc && sccs.blocks(dom_scc).len() == 1 {
                dom = output.with_repr(
                    func.block(dom.with_repr32())
                        .immediate_dominator()
                        .expect("handled root already above"),
                )?;
                let next_dom_scc = sccs.scc(dom);

                // `dom_scc` is a single-block component, so `dom`'s immediate
                // dominator is necessarily in some other component, and the walk
                // strictly ascends the dominator tree.
                debug_assert_ne!(dom_scc, next_dom_scc);

                // Union so that the *outer* component becomes the representative.
                //
                // Either argument order would merge the same components, and so
                // would give the same partition of blocks into regions, but
                // `scc_region` turns the representative into the `Region`, so
                // making the outer component the representative matches the
                // spirit of the region tree.
                self.regions.union(next_dom_scc, dom_scc);

                dom_scc = next_dom_scc;
            }
        }

        Ok(())
    }

    /// Lay each region's blocks out contiguously within
    /// `region_blocks_storage`.
    fn construct_region_blocks(
        &mut self,
        func: &impl InputFunction,
        sccs: &StronglyConnectedComponents<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        // We learn each block's region in layout order, but any one region's
        // blocks are scattered throughout that order, so sort the blocks by
        // region before copying them into their contiguous storage.
        self.blocks_by_region.reserve(func.len_blocks());
        for (block, _) in func.blocks() {
            let block = output.with_repr(block)?;
            let region = self.block_region(sccs, block);
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

    /// Compute each region's parent, and lay each region's children out
    /// contiguously within `region_children_storage`.
    fn construct_region_tree(
        &mut self,
        func: &impl InputFunction,
        sccs: &StronglyConnectedComponents<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        self.children_by_parent.reserve(self.distinct_regions.len());
        for i in 0..self.distinct_regions.len() {
            let region = self.distinct_regions[i];
            let parent = self.compute_parent(func, sccs, region, output)?;
            self.region_parent[region] = parent;
            if let Some(parent) = parent {
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

    /// Compute the given region's parent region.
    ///
    /// This is the region of the nearest common dominator of the region's
    /// blocks, stepping out to that block's immediate dominator when it is
    /// itself a member of this region.
    ///
    /// Note that we deliberately do not use "the immediate dominator of the
    /// region's header". With irreducible control flow a region's component can
    /// be entered at more than one block, and so has no unique header; worse,
    /// the candidate headers' immediate dominators can lie in different regions
    /// that aren't ancestors of one another. The nearest common dominator is
    /// always well defined and always yields a proper tree: it dominates all of
    /// the region's blocks, so stepping outside the region always lands on a
    /// block strictly closer to the dominator tree's root.
    fn compute_parent(
        &self,
        func: &impl InputFunction,
        sccs: &StronglyConnectedComponents<E>,
        region: Region<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<Option<Region<E>>> {
        let mut blocks = self.blocks(region);
        let mut ncd = blocks
            .next()
            .expect("every region contains at least one block");
        for block in blocks {
            ncd = nearest_common_dominator(func, output, ncd, block)?;
        }

        // If the nearest common dominator is a member of this region, then it is
        // this region's single entry point, and our parent is the region of *its*
        // immediate dominator. Only the top-level region contains the function's
        // entry block, and only the entry block has no immediate dominator, so
        // only the top-level region ends up without a parent.
        let outside = if self.block_region(sccs, ncd) == region {
            match func.block(ncd.with_repr32()).immediate_dominator() {
                Some(idom) => output.with_repr(idom)?,
                None => return Ok(None),
            }
        } else {
            ncd
        };

        Ok(Some(self.block_region(sccs, outside)))
    }

    /// Get the region containing the given block.
    pub fn block_region(
        &self,
        sccs: &StronglyConnectedComponents<E>,
        block: Block<E>,
    ) -> Region<E> {
        let scc = sccs.scc(block);
        self.scc_region(scc)
    }

    /// Get the region containing the given SCC.
    pub fn scc_region(&self, scc: Scc<E>) -> Region<E> {
        let region_scc = self.regions.find_without_path_compression(scc);
        Region::try_new(region_scc.index()).unwrap()
    }

    /// Get the blocks in the given region.
    pub fn blocks(&self, region: Region<E>) -> impl ExactSizeIterator<Item = Block<E>> + '_ {
        self.region_blocks[region].indices().map(move |i| {
            let i = RegionBlocksStorageIndex::try_new(i).unwrap();
            self.region_blocks_storage[i]
        })
    }

    /// Get the root of the region tree: the function entry block's region.
    pub fn root(&self) -> Region<E> {
        self.root
            .expect("should always have a root after construction")
    }

    /// Get the parent of the given region, or `None` if this is the top-level
    /// region.
    pub fn parent(&self, region: Region<E>) -> Option<Region<E>> {
        self.region_parent[region]
    }

    /// Get the immediate child regions of the given region.
    pub fn children(&self, region: Region<E>) -> impl ExactSizeIterator<Item = Region<E>> + '_ {
        self.region_children[region].indices().map(move |i| {
            let i = RegionChildrenStorageIndex::try_new(i).unwrap();
            self.region_children_storage[i]
        })
    }
}

/// Compute the nearest common dominator of two blocks.
///
/// Both blocks must be reachable from the function's entry block.
fn nearest_common_dominator<E>(
    func: &impl InputFunction,
    output: &mut OutputInner<E>,
    a: Block<E>,
    b: Block<E>,
) -> IResult<Block<E>>
where
    E: EntityRepr,
{
    // Walk `a` up the dominator tree until it dominates `b`. Because `dominates`
    // is reflexive this stops immediately when `a` already dominates `b`, and it
    // always terminates because the entry block dominates every reachable block.
    let mut a = a;
    while !func.block(a.with_repr32()).dominates(b.with_repr32()) {
        a = output.with_repr(
            func.block(a.with_repr32())
                .immediate_dominator()
                .expect("the entry block dominates every reachable block"),
        )?;
    }
    Ok(a)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dfs::Dfs;
    use crate::test::TestFunction;
    use mutatis::check::{Check, CheckResult};
    use std::{
        collections::{BTreeMap, BTreeSet, HashMap},
        format,
        string::{String, ToString},
    };

    /// A region, as identified by the set of blocks in the strongly-connected
    /// component that defines it.
    ///
    /// The tests identify regions this way, rather than by `Region`, so that
    /// they never depend on how `StronglyConnectedComponents` happens to number
    /// things.
    type RegionId = BTreeSet<Block>;

    /// Construct the strongly-connected components and the region tree for
    /// `func`.
    fn construct(
        func: &TestFunction,
    ) -> Result<(StronglyConnectedComponents<u32>, RegionTree<u32>), String> {
        let mut counts = Counts::new();
        let mut output = OutputInner::<u32>::new();

        let mut dfs = Dfs::<u32>::new();
        let mut sccs = StronglyConnectedComponents::<u32>::new();
        if sccs
            .construct(func, &mut counts, &mut dfs, &mut output)
            .is_err()
        {
            return Err(format!(
                "`StronglyConnectedComponents::construct` failed: {:?}",
                output.take_error()
            ));
        }

        let mut tree = RegionTree::<u32>::new();
        assert!(tree.is_reset());
        if tree
            .construct(func, &mut counts, &sccs, &mut output)
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

        Ok((sccs, tree))
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

    /// For each block, compute the region it belongs to: the first component
    /// at-or-above it in the dominator tree that either holds more than one
    /// block or is the entry block's component.
    fn regions_oracle(
        func: &TestFunction,
        sccs: &HashMap<Block, BTreeSet<Block>>,
        idoms: &HashMap<Block, Option<Block>>,
    ) -> HashMap<Block, RegionId> {
        let entry_scc = &sccs[&func.entry_block()];

        func.blocks()
            .map(|(b, _)| {
                let mut dom = b;
                loop {
                    let scc = &sccs[&dom];
                    if scc == entry_scc || scc.len() > 1 {
                        return (b, scc.clone());
                    }
                    dom = idoms[&dom].expect("the entry block's component stops the walk");
                }
            })
            .collect()
    }

    #[test]
    fn region_tree_properties() -> CheckResult<TestFunction> {
        Check::new().iters(10_000).run(|func: &TestFunction| -> Result<(), String> {
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

            let (sccs, tree) = construct(func)?;

            let dominators = dominators_oracle(func);
            let idoms = idoms_oracle(&dominators);
            let oracle_sccs = sccs_oracle(func);
            let oracle_regions = regions_oracle(func, &oracle_sccs, &idoms);

            // Property 1: the regions partition the blocks, and two blocks
            // share a region exactly when the oracle says they should.
            //
            // `blocks()` covering every block exactly once and agreeing with
            // `block_region` gives the partition; comparing the two groupings
            // gives the agreement.
            let mut actual_groups: BTreeMap<Region, BTreeSet<Block>> = BTreeMap::new();
            for b in &blocks {
                actual_groups
                    .entry(tree.block_region(&sccs, *b))
                    .or_default()
                    .insert(*b);
            }
            let mut expected_groups: BTreeMap<RegionId, BTreeSet<Block>> = BTreeMap::new();
            for b in &blocks {
                expected_groups
                    .entry(oracle_regions[b].clone())
                    .or_default()
                    .insert(*b);
            }
            let actual_partition: BTreeSet<&BTreeSet<Block>> = actual_groups.values().collect();
            let expected_partition: BTreeSet<&BTreeSet<Block>> = expected_groups.values().collect();
            if actual_partition != expected_partition {
                return Err(format!(
                    "the regions group the blocks as {actual_partition:?} but should group them \
                     as {expected_partition:?}"
                ));
            }

            let regions: Vec<Region> = actual_groups.keys().copied().collect();
            for region in &regions {
                let listed: BTreeSet<Block> = tree.blocks(*region).collect();
                if listed.len() != tree.blocks(*region).len() {
                    return Err(format!(
                        "`blocks({region:?})` repeats a block: {:?}",
                        tree.blocks(*region).collect::<Vec<_>>(),
                    ));
                }
                if listed != actual_groups[region] {
                    return Err(format!(
                        "`blocks({region:?})` is {listed:?} but the blocks whose `block_region` \
                         is {region:?} are {:?}",
                        actual_groups[region],
                    ));
                }
            }

            // Property 2: a region is identified by the component that defines
            // it, i.e. a region's index is the index of the first component
            // at-or-above its blocks that is a loop or the entry's component.
            for b in &blocks {
                let defining = *oracle_regions[b]
                    .first()
                    .expect("a region is defined by a non-empty component");
                let expected = Region::try_new(sccs.scc(defining).index()).unwrap();
                if tree.block_region(&sccs, *b) != expected {
                    return Err(format!(
                        "{b:?}'s region is {:?}, but its region is defined by the component \
                         {:?}, so it should be {expected:?}",
                        tree.block_region(&sccs, *b),
                        oracle_regions[b],
                    ));
                }
            }

            // Property 3: a loop is never split across regions.
            for b in &blocks {
                let region = tree.block_region(&sccs, *b);
                for &other in &oracle_sccs[b] {
                    if tree.block_region(&sccs, other) != region {
                        return Err(format!(
                            "{b:?} and {other:?} are in the same strongly-connected component \
                             {:?}, but {b:?} is in {region:?} and {other:?} is in {:?}",
                            oracle_sccs[b],
                            tree.block_region(&sccs, other),
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
            if root != tree.block_region(&sccs, entry) {
                return Err(format!(
                    "`root()` is {root:?} but {entry:?}'s region is {:?}",
                    tree.block_region(&sccs, entry),
                ));
            }
            if !tree.blocks(root).any(|b| b == entry) {
                return Err(format!(
                    "`root()` is {root:?}, but its blocks are {:?}, which do not include the \
                     entry block {entry:?}",
                    tree.blocks(root).collect::<Vec<_>>(),
                ));
            }
            for region in &regions {
                let parent = tree.parent(*region);
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
                    curr = tree.parent(r);
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
                for child in tree.children(*region) {
                    if !children.insert(child) {
                        return Err(format!("{child:?} is a child of more than one region"));
                    }
                    if tree.parent(child) != Some(*region) {
                        return Err(format!(
                            "{child:?} is listed as a child of {region:?} but its parent is {:?}",
                            tree.parent(child),
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

            // Property 7: a region's parent is the region of the nearest common
            // dominator of its blocks, stepping out when that block is itself
            // in the region. This is the tie-break that makes `parent` well
            // defined for irreducible control flow, where a region's component
            // can have several entry points.
            let ncd = |a: Block, b: Block| -> Block {
                let mut a = a;
                while !dominators[&b].contains(&a) {
                    a = idoms[&a].expect("the entry block dominates every reachable block");
                }
                a
            };
            for region in &regions {
                let mut region_blocks = tree.blocks(*region);
                let mut d = region_blocks.next().expect("regions are never empty");
                for b in region_blocks {
                    d = ncd(d, b);
                }

                let expected = if tree.block_region(&sccs, d) == *region {
                    idoms[&d].map(|idom| tree.block_region(&sccs, idom))
                } else {
                    Some(tree.block_region(&sccs, d))
                };

                if tree.parent(*region) != expected {
                    return Err(format!(
                        "`parent({region:?})` is {:?} but the nearest common dominator of its \
                         blocks is {d:?}, which makes the parent {expected:?}",
                        tree.parent(*region),
                    ));
                }
            }

            // Property 8: nesting is consistent with dominance. If one region
            // is a descendant of another, the ancestor's nearest common
            // dominator dominates every one of the descendant's blocks.
            for region in &regions {
                let mut curr = tree.parent(*region);
                while let Some(ancestor) = curr {
                    let mut ancestor_blocks = tree.blocks(ancestor);
                    let mut ancestor_ncd = ancestor_blocks.next().expect("regions are never empty");
                    for b in ancestor_blocks {
                        ancestor_ncd = ncd(ancestor_ncd, b);
                    }

                    for b in tree.blocks(*region) {
                        if !dominators[&b].contains(&ancestor_ncd) {
                            return Err(format!(
                                "{region:?} is a descendant of {ancestor:?}, whose nearest \
                                 common dominator {ancestor_ncd:?} does not dominate \
                                 {region:?}'s block {b:?}"
                            ));
                        }
                    }

                    curr = tree.parent(ancestor);
                }
            }

            // Property 9: constructing the region tree again gives the same
            // answer, and it resets cleanly.
            let (sccs_again, tree_again) = construct(func)?;
            if tree_again.root() != root {
                return Err(format!(
                    "constructing twice gave the roots {root:?} and {:?}",
                    tree_again.root(),
                ));
            }
            for b in &blocks {
                if tree_again.block_region(&sccs_again, *b) != tree.block_region(&sccs, *b) {
                    return Err(format!(
                        "constructing twice put {b:?} in {:?} and then {:?}",
                        tree.block_region(&sccs, *b),
                        tree_again.block_region(&sccs_again, *b),
                    ));
                }
            }
            for region in &regions {
                if tree_again.blocks(*region).collect::<Vec<_>>()
                    != tree.blocks(*region).collect::<Vec<_>>()
                {
                    return Err(format!(
                        "constructing twice gave {region:?} different blocks"
                    ));
                }
                if tree_again.parent(*region) != tree.parent(*region) {
                    return Err(format!(
                        "constructing twice gave {region:?} a different parent"
                    ));
                }
                if tree_again.children(*region).collect::<Vec<_>>()
                    != tree.children(*region).collect::<Vec<_>>()
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
