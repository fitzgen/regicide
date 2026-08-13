use crate::{
    Block, Entity as _, EntityRepr, InputBlock as _, InputFunction, error::IResult,
    output::OutputInner,
};
use alloc::vec::Vec;

/// An iterative depth-first traversal.
///
/// TODO: allow some mechanism for skipping `DfsEvent` variants that a
/// particular traversal doesn't need, so we can avoid pushing/popping them from
/// the stack and processing these events that are ignored.
pub struct Dfs<E>
where
    E: EntityRepr,
{
    stack: Vec<DfsEvent<E>>,
}

impl<E> Dfs<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        Self { stack: Vec::new() }
    }

    /// Create a new DFS traversal, starting at the given roots.
    pub fn construct(
        &mut self,
        func: &impl InputFunction,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        let root = output.with_repr(func.entry_block())?;
        self.stack.push(DfsEvent::Pre(root));
        Ok(())
    }

    pub fn reset(&mut self) {
        let Self { stack } = self;
        stack.clear();
    }

    pub fn is_reset(&self) -> bool {
        self.stack.is_empty()
    }
}

/// An event during a DFS traversal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DfsEvent<E>
where
    E: EntityRepr,
{
    /// The first time seeing this block.
    Pre(Block<E>),

    /// After having just visited the given edge.
    AfterEdge(Block<E>, Block<E>),

    /// Finished visiting this block and all of its successors.
    Post(Block<E>),
}

impl<E> Dfs<E>
where
    E: EntityRepr,
{
    /// Pump the traversal, yielding the next `DfsEvent`.
    ///
    /// Returns `None` when the traversal is complete.
    pub fn next(
        &mut self,
        func: &impl InputFunction,
        output: &mut OutputInner<E>,
        seen: impl Fn(Block<E>) -> bool,
    ) -> IResult<Option<DfsEvent<E>>> {
        loop {
            let Some(event) = self.stack.pop() else {
                return Ok(None);
            };

            if let DfsEvent::Pre(block) = event {
                if seen(block) {
                    continue;
                }

                let input_block = func.block(block.with_repr32());
                let successors = input_block.successors();

                let (min, max) = successors.size_hint();
                let estimated_successors_len = max.unwrap_or_else(|| 2 * min);
                self.stack.reserve(
                    // We push an after-edge and pre event for each successor.
                    2 * estimated_successors_len
                        // And we push one post event for this block.
                        + 1,
                );

                self.stack.push(DfsEvent::Post(block));
                for succ in successors {
                    let succ = output.with_repr(succ)?;
                    self.stack.push(DfsEvent::AfterEdge(block, succ));
                    if !seen(succ) {
                        self.stack.push(DfsEvent::Pre(succ));
                    }
                }
            }

            return Ok(Some(event));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Entity as _;
    use crate::test::*;
    use mutatis::check::{Check, CheckResult};
    use std::collections::{BTreeSet, HashMap};

    /// Run a DFS to completion, treating every block in `seen` as
    /// already visited.
    ///
    /// Returns every event that was emitted, along with the final `seen` set.
    fn run_dfs(
        func: &TestFunction,
        mut seen: BTreeSet<Block>,
    ) -> (Vec<DfsEvent<u32>>, BTreeSet<Block>) {
        let mut output = OutputInner::<u32>::new();
        let mut dfs = Dfs::<u32>::new();
        dfs.construct(func, &mut output).unwrap();

        let mut events = Vec::new();
        while let Some(event) = dfs.next(func, &mut output, |b| seen.contains(&b)).unwrap() {
            if let DfsEvent::Pre(b) = event {
                seen.insert(b);
            }
            events.push(event);
        }
        (events, seen)
    }

    /// Independently (without going through `Dfs`) compute the set of blocks
    /// that would be freshly discovered starting from `start`, given that every
    /// block in `blocked` is already visited.
    fn reachable_avoiding(
        func: &TestFunction,
        start: Block,
        blocked: &BTreeSet<Block>,
    ) -> BTreeSet<Block> {
        let mut visited = blocked.clone();
        let mut discovered = BTreeSet::new();
        let mut worklist = alloc::vec![];

        if visited.insert(start) {
            discovered.insert(start);
            worklist.push(start);
        }

        while let Some(block) = worklist.pop() {
            for succ in func.block(block).successors() {
                if visited.insert(succ) {
                    discovered.insert(succ);
                    worklist.push(succ);
                }
            }
        }

        discovered
    }

    #[test]
    fn dfs_properties() -> CheckResult<TestFunction> {
        Check::new().iters(10_000).run(|func: &TestFunction| {
            let entry = func.entry_block();

            let (events, visited) = run_dfs(func, BTreeSet::new());

            // The DFS should visit exactly the blocks reachable from the entry
            // block.
            let reachable = reachable_avoiding(func, entry, &BTreeSet::new());
            if visited != reachable {
                return Err("DFS did not visit exactly the blocks reachable from the entry block");
            }

            // The traversal always begins by discovering the entry block.
            if events.first().copied() != Some(DfsEvent::Pre(entry)) {
                return Err("first DFS event was not `Pre(entry_block)`");
            }

            // Replay the events, checking that they form a well-nested DFS: every
            // block is discovered and finished at most once, `AfterEdge` only
            // fires while its source block is the innermost open block, and
            // edges only ever point at already-discovered blocks.
            let mut pre_seen = BTreeSet::new();
            let mut post_seen = BTreeSet::new();
            let mut shadow_stack = Vec::new();
            let mut after_edge_targets: HashMap<Block, Vec<Block>> = HashMap::new();
            for &event in &events {
                match event {
                    DfsEvent::Pre(b) => {
                        if !pre_seen.insert(b) {
                            return Err("a block was discovered (`Pre`) more than once");
                        }
                        shadow_stack.push(b);
                    }
                    DfsEvent::AfterEdge(b, s) => {
                        if shadow_stack.last() != Some(&b) {
                            return Err(
                                "`AfterEdge` fired while its block was not the innermost open block",
                            );
                        }
                        if !pre_seen.contains(&s) {
                            return Err("`AfterEdge` referenced a block that had not been discovered");
                        }
                        after_edge_targets.entry(b).or_default().push(s);
                    }
                    DfsEvent::Post(b) => {
                        if !post_seen.insert(b) {
                            return Err("a block was finished (`Post`) more than once");
                        }
                        if shadow_stack.pop() != Some(b) {
                            return Err("`Post` did not match the innermost open block");
                        }
                    }
                }
            }

            if !shadow_stack.is_empty() {
                return Err("the traversal finished with unclosed blocks");
            }
            if pre_seen != post_seen {
                return Err("not every discovered block was also finished");
            }

            // Every `AfterEdge` fired for a block must correspond exactly to
            // that block's successors.
            for &block in &pre_seen {
                let mut expected: Vec<Block> = func.block(block).successors().collect();
                expected.reverse();
                let actual = after_edge_targets.remove(&block).unwrap_or_default();
                if expected != actual {
                    return Err("`AfterEdge` targets did not match the block's successors");
                }
            }

            // Running the same traversal again from scratch is deterministic.
            let (events_again, _) = run_dfs(func, BTreeSet::new());
            if events != events_again {
                return Err("two DFS traversals of the same function produced different events");
            }

            // Mark every other discovered block as already "seen", and check
            // that the traversal skips exactly those blocks (and anything only
            // reachable through them), while still reaching everything else.
            let already_seen: BTreeSet<Block> = pre_seen
                .iter()
                .copied()
                .filter(|b| b.index() % 2 == 0)
                .collect();
            let (_, visited_with_seed) = run_dfs(func, already_seen.clone());
            let newly_discovered: BTreeSet<Block> =
                visited_with_seed.difference(&already_seen).copied().collect();
            let expected_discovered = reachable_avoiding(func, entry, &already_seen);
            if newly_discovered != expected_discovered {
                return Err("DFS did not respect externally pre-seeded `seen` blocks");
            }

            Ok(())
        })
    }
}
