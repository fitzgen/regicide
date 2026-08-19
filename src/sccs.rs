//! Strongly-connected components.
//!
//! This module implements [Tarjan's algorithm] for finding strongly-connected
//! components.
//!
//! This algorithm takes `O(V+E)` time and uses `O(V+E)` space.
//!
//! Tarjan's algorithm is usually presented as a recursive algorithm, but we do
//! not trust the input and cannot recurse over it for fear of blowing the
//! stack. Therefore, this implementation is iterative.
//!
//! Derived from Wasmtime's implemenation in
//! `wasmtime/crates/environ/src/graphs/scc.rs`.
//!
//! [Tarjan's algorithm]: https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm

use crate::{
    Entity,
    btree::{BTreeSet, BTreeSetArena},
    counts::Counts,
    dfs::{Dfs, DfsEvent},
    entity::{Block, EntityRepr, PrimaryMap, PrimaryMapKeys, Scc, SccBlockIndex, SecondaryMap},
    error::IResult,
    input::InputFunction,
    output::OutputInner,
};
use alloc::vec::Vec;
use core::{cmp, ops::Range};

pub struct StronglyConnectedComponents<E>
where
    E: EntityRepr,
{
    /// A map from each SCC to the range of indices in `self.component_blocks`
    /// that stores this SCC's members.
    components: PrimaryMap<Scc<E>, Range<SccBlockIndex<E>>>,

    /// The storage for the blocks in each SCC.
    component_blocks: PrimaryMap<SccBlockIndex<E>, Block<E>>,

    /// The DFS index of each block.
    indices: SecondaryMap<Block<E>, Option<SccBlockIndex<E>>>,

    /// The earliest on-stack block reachable from each block.
    lowlinks: SecondaryMap<Block<E>, Option<SccBlockIndex<E>>>,

    /// The SCC that each block is a member of, or `None` for blocks that are not
    /// reachable from the entry block.
    block_sccs: SecondaryMap<Block<E>, Option<Scc<E>>>,

    /// The stack of blocks we are currently finding an SCC for. Not the same as
    /// the DFS stack: we only pop from this stack once we find the root of an
    /// SCC.
    scc_stack: Vec<Block<E>>,

    /// The set of blocks on `scc_stack`.
    on_scc_stack: BTreeSet<E, Block<E>>,

    /// Arena storage for `on_scc_stack`.
    on_scc_stack_arena: BTreeSetArena<E, Block<E>>,
}

impl<E> StronglyConnectedComponents<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        StronglyConnectedComponents {
            components: PrimaryMap::new(),
            component_blocks: PrimaryMap::new(),
            indices: SecondaryMap::new(None),
            lowlinks: SecondaryMap::new(None),
            block_sccs: SecondaryMap::new(None),
            scc_stack: Vec::new(),
            on_scc_stack: BTreeSet::new(),
            on_scc_stack_arena: BTreeSetArena::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            components,
            component_blocks,
            indices,
            lowlinks,
            block_sccs,
            scc_stack,
            on_scc_stack,
            on_scc_stack_arena,
        } = self;
        components.reset();
        component_blocks.reset();
        indices.reset();
        lowlinks.reset();
        block_sccs.reset();
        scc_stack.clear();
        *on_scc_stack = BTreeSet::new();
        on_scc_stack_arena.reset();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            components,
            component_blocks,
            indices,
            lowlinks,
            block_sccs,
            scc_stack,
            on_scc_stack,
            on_scc_stack_arena,
        } = self;
        components.is_reset()
            && component_blocks.is_reset()
            && indices.is_reset()
            && lowlinks.is_reset()
            && block_sccs.is_reset()
            && scc_stack.is_empty()
            && on_scc_stack.is_empty()
            && on_scc_stack_arena.is_reset()
    }

    pub fn construct(
        &mut self,
        func: &impl InputFunction,
        counts: &mut Counts,
        dfs: &mut Dfs<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        self.components.reserve(func.len_blocks());
        self.component_blocks.reserve(func.len_blocks());

        // The DFS index counter.
        let mut index = 0;

        dfs.construct(func, output)?;
        while let Some(event) = dfs.next(func, output, |block| self.indices[block].is_some())? {
            match event {
                DfsEvent::Pre(block) => {
                    debug_assert!(self.indices[block].is_none());
                    debug_assert!(self.lowlinks[block].is_none());

                    // Assign an index to this block.
                    let scc_block_index = output.entity(index)?;
                    self.indices[block] = Some(scc_block_index);

                    // Its current lowlink is itself. This will get updated to
                    // be accurate as we visit the block's successors.
                    self.lowlinks[block] = Some(scc_block_index);

                    // Increment the DFS counter.
                    index += 1;

                    // Push the block onto the SCC stack.
                    self.scc_stack.push(block);
                    let is_newly_on_stack = self
                        .on_scc_stack
                        .insert(&mut self.on_scc_stack_arena, block);
                    debug_assert!(is_newly_on_stack);
                }
                DfsEvent::AfterEdge(block, succ) => {
                    debug_assert!(self.indices[block].is_some());
                    debug_assert!(self.lowlinks[block].is_some());
                    debug_assert!(self.lowlinks[block] <= self.indices[block]);
                    debug_assert!(self.indices[succ].is_some());
                    debug_assert!(self.lowlinks[succ].is_some());
                    debug_assert!(self.lowlinks[succ] <= self.indices[succ]);

                    // If the successor is still on the SCC stack, then it is
                    // part of the same SCC as this block, so propagate its
                    // lowlink to this block's lowlink.
                    if self.on_scc_stack.contains(&self.on_scc_stack_arena, &succ) {
                        self.lowlinks[block] = Some(cmp::min(
                            self.lowlinks[block].unwrap(),
                            self.lowlinks[succ].unwrap(),
                        ));
                    }
                }
                DfsEvent::Post(block) => {
                    debug_assert!(self.indices[block].is_some());
                    debug_assert!(self.lowlinks[block].is_some());

                    // If this block's index is the same as its lowlink, then it
                    // is the root of a component. Pop this component's elements
                    // from the SCC stack and push them into our result data
                    // structures.
                    if self.indices[block] == self.lowlinks[block] {
                        let scc = self.components.next_key(output)?;
                        let start = self.component_blocks.next_key(output)?;
                        while let Some(b) = self.scc_stack.pop() {
                            let was_on_stack =
                                self.on_scc_stack.remove(&mut self.on_scc_stack_arena, &b);
                            debug_assert!(was_on_stack);
                            self.component_blocks.push(output, b)?;
                            debug_assert!(self.block_sccs[b].is_none());
                            self.block_sccs[b] = Some(scc);
                            if b == block {
                                break;
                            }
                        }
                        let end = self.component_blocks.next_key(output)?;
                        let pushed = self.components.push(output, start..end)?;
                        debug_assert_eq!(pushed, scc);
                    }
                }
            }
        }

        counts.sccs += self.components.len();
        dfs.reset();
        Ok(())
    }

    /// Get the number of strongly-connected components.
    #[expect(dead_code, reason = "will probably need it")]
    pub fn len(&self) -> usize {
        self.components.len()
    }

    /// Are there no strongly-connected components?
    #[expect(dead_code, reason = "will probably need it")]
    pub fn is_empty(&self) -> bool {
        self.components.is_empty()
    }

    /// Iterate over each strongly-connected component.
    ///
    /// Iteration happens in reverse-topological order: successors are visited
    /// before predecessors in the resulting SCC DAG.
    #[allow(dead_code, reason = "will probably need it")]
    pub fn keys(&self) -> PrimaryMapKeys<Scc<E>> {
        self.components.keys()
    }

    /// Get the blocks that make up the given strongly-connected component.
    pub fn blocks(&self, scc: Scc<E>) -> impl ExactSizeIterator<Item = Block<E>> + '_ {
        let Range { start, end } = self.components[scc].clone();
        (start.index()..end.index()).map(|i| {
            let i = SccBlockIndex::try_new(i).unwrap();
            self.component_blocks[i]
        })
    }

    /// Get the strongly-connected component that the given block is a member
    /// of.
    ///
    /// Panics if the block is not reachable from the entry block, since such
    /// blocks are never assigned to a component.
    pub fn scc(&self, block: Block<E>) -> Scc<E> {
        self.block_sccs[block].expect("block is not reachable from the entry block")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{InputBlock as _, test::TestFunction};
    use mutatis::check::{Check, CheckResult};
    use std::{
        collections::{BTreeSet, HashMap},
        format,
        string::{String, ToString},
    };

    /// Compute the strongly-connected components of `func`, returning each
    /// component's blocks in the order that the components were found.
    ///
    /// Along the way, this checks the invariants of the internal representation
    /// and of `reset`/`is_reset`, since those are not visible through the public
    /// accessors.
    fn components(func: &TestFunction) -> Result<Vec<Vec<Block>>, String> {
        let mut sccs = StronglyConnectedComponents::<u32>::new();
        let mut counts = Counts::new();
        let mut dfs = Dfs::<u32>::new();
        let mut output = OutputInner::<u32>::new();

        assert!(sccs.is_reset());

        if sccs
            .construct(func, &mut counts, &mut dfs, &mut output)
            .is_err()
        {
            return Err(format!("`construct` failed: {:?}", output.take_error()));
        }

        // `construct` is done with the `Dfs` when it returns, and resets it.
        if !dfs.is_reset() {
            return Err("`construct` left the `Dfs` un-reset".to_string());
        }
        if sccs.is_reset() {
            return Err("`is_reset` is true after a successful `construct`".to_string());
        }

        // The components' block ranges must tile `component_blocks`
        // contiguously, with no gaps and no overlap.
        let mut expected_start = 0;
        for scc in sccs.keys() {
            let Range { start, end } = sccs.components[scc].clone();
            if start.index() != expected_start {
                return Err(format!(
                    "{scc:?}'s blocks start at {} but the previous component's blocks \
                     ended at {expected_start}",
                    start.index(),
                ));
            }
            if end.index() < start.index() {
                return Err(format!(
                    "{scc:?}'s block range {start:?}..{end:?} is backwards"
                ));
            }
            expected_start = end.index();
        }
        if expected_start != sccs.component_blocks.len() {
            return Err(format!(
                "the components' block ranges cover {expected_start} blocks but \
                 `component_blocks` holds {}",
                sccs.component_blocks.len(),
            ));
        }

        let result: Vec<Vec<Block>> = sccs.keys().map(|scc| sccs.blocks(scc).collect()).collect();

        // Every block's `scc` must name a component that actually contains it.
        for (block, _) in func.blocks() {
            let scc = sccs.scc(block);
            if !sccs.blocks(scc).any(|b| b == block) {
                return Err(format!(
                    "`scc({block:?})` is {scc:?}, but that component's blocks are {:?}",
                    sccs.blocks(scc).collect::<Vec<_>>(),
                ));
            }
        }

        sccs.reset();
        if !sccs.is_reset() {
            return Err("`is_reset` is false after `reset`".to_string());
        }

        Ok(result)
    }

    /// Compute the reflexive-transitive reachability relation over `func`'s
    /// control-flow graph.
    ///
    /// This deliberately uses neither `Dfs` nor `StronglyConnectedComponents`,
    /// so that it is an independent oracle rather than a restatement of the
    /// code under test.
    fn reachability(func: &TestFunction) -> HashMap<Block, BTreeSet<Block>> {
        let mut reachable = HashMap::new();

        for (block, _) in func.blocks() {
            let mut visited = BTreeSet::new();
            visited.insert(block);

            let mut worklist = alloc::vec![block];
            while let Some(b) = worklist.pop() {
                for succ in func.block(b).successors() {
                    if visited.insert(succ) {
                        worklist.push(succ);
                    }
                }
            }

            reachable.insert(block, visited);
        }

        reachable
    }

    #[test]
    fn scc_properties() -> CheckResult<TestFunction> {
        Check::new().iters(10_000).run(|func: &TestFunction| -> Result<(), String> {
            let entry = func.entry_block();
            let sccs = components(func)?;

            // No component is empty, and no block appears in more than one
            // component.
            let mut scc_of = HashMap::<Block, usize>::new();
            for (i, blocks) in sccs.iter().enumerate() {
                if blocks.is_empty() {
                    return Err(format!("component {i} of {sccs:?} is empty"));
                }
                for &block in blocks {
                    if let Some(j) = scc_of.insert(block, i) {
                        return Err(format!(
                            "{block:?} appears in both component {j} and component {i} \
                             of {sccs:?}"
                        ));
                    }
                }
            }

            let reachable = reachability(func);

            // `TestFunction::fixup` is supposed to make every block reachable
            // from the entry block. If it didn't, that's a bug in the generator
            // rather than in the SCCs, so check it on its own.
            if reachable[&entry].len() != func.len_blocks() {
                return Err(format!(
                    "only {} of this function's {} blocks are reachable from {entry:?}; \
                     `TestFunction::fixup` should have made them all reachable",
                    reachable[&entry].len(),
                    func.len_blocks(),
                ));
            }

            // The components partition exactly the blocks that are reachable
            // from the entry block: no more and no less.
            let covered: BTreeSet<Block> = scc_of.keys().copied().collect();
            if covered != reachable[&entry] {
                return Err(format!(
                    "the components cover {covered:?} but {:?} are reachable from {entry:?}",
                    reachable[&entry],
                ));
            }

            // The defining property of strongly-connected components: two
            // blocks are members of the same component if and only if they are
            // mutually reachable.
            for (a, _) in func.blocks() {
                for (b, _) in func.blocks() {
                    let mutually_reachable =
                        reachable[&a].contains(&b) && reachable[&b].contains(&a);
                    let same_component = scc_of[&a] == scc_of[&b];
                    if mutually_reachable != same_component {
                        return Err(format!(
                            "{a:?} is in component {} and {b:?} is in component {}, but they \
                             are {}mutually reachable",
                            scc_of[&a],
                            scc_of[&b],
                            if mutually_reachable { "" } else { "not " },
                        ));
                    }
                }
            }

            // The components are found in reverse-topological order: for every
            // control-flow edge, the successor's component is never numbered
            // higher than the predecessor's.
            for (a, input_block) in func.blocks() {
                for b in input_block.successors() {
                    if scc_of[&b] > scc_of[&a] {
                        return Err(format!(
                            "the edge {a:?} --> {b:?} goes from component {} to the later \
                             component {}, so the components are not in reverse-topological \
                             order",
                            scc_of[&a], scc_of[&b],
                        ));
                    }
                }
            }

            // The entry block is always the root of its own component (its
            // lowlink can never be less than its index of zero) and its `Post`
            // event is always the last one, so its component is always found
            // last.
            if scc_of[&entry] != sccs.len() - 1 {
                return Err(format!(
                    "{entry:?} is in component {} but should be in the last component, {}",
                    scc_of[&entry],
                    sccs.len() - 1,
                ));
            }

            // Computing the components again gives the same answer.
            let sccs_again = components(func)?;
            if sccs != sccs_again {
                return Err(format!(
                    "computing the SCCs twice gave different answers: {sccs:?} vs {sccs_again:?}"
                ));
            }

            Ok(())
        })
    }
}
