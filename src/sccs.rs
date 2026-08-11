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
//! Derived from Wasmtime's implemenation.
//!
//! [Tarjan's algorithm]: https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm

use crate::{
    Entity, InputBlock, PrimaryMap,
    btree::{BTreeSet, BTreeSetArena},
    counts::Counts,
    dfs::{Dfs, DfsEvent},
    entity::{Block, EntityRepr, Scc, SccBlockIndex, SecondaryMap},
    error::IResult,
    input::InputFunction,
    output::OutputInner,
};
use alloc::vec::Vec;
use core::{cmp, marker::PhantomData, ops::Range};

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
            scc_stack,
            on_scc_stack,
            on_scc_stack_arena,
        } = self;
        components.reset();
        component_blocks.reset();
        indices.reset();
        lowlinks.reset();
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
            scc_stack,
            on_scc_stack,
            on_scc_stack_arena,
        } = self;
        components.is_reset()
            && component_blocks.is_reset()
            && indices.is_reset()
            && lowlinks.is_reset()
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
                        let start = self.component_blocks.next_key(output)?;
                        let mut done = false;
                        while let Some(b) = self.scc_stack.pop() {
                            let was_on_stack =
                                self.on_scc_stack.remove(&mut self.on_scc_stack_arena, &b);
                            debug_assert!(was_on_stack);
                            if b == block {
                                break;
                            }
                            self.component_blocks.push(output, b)?;
                        }
                        let end = self.component_blocks.next_key(output)?;
                        self.components.push(output, start..end)?;
                    }
                }
            }
        }

        counts.sccs += self.components.len();
        dfs.reset();
        Ok(())
    }
}
