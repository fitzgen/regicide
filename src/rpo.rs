use crate::{
    Block,
    dfs::{Dfs, DfsEvent},
    entity::{EntityRepr, EntitySet},
    error::IResult,
    input::InputFunction,
    output::OutputInner,
    timing::Timing,
};
use alloc::vec::Vec;

/// A reverse post-order traversal of a function's control-flow graph.
pub struct Rpo<E>
where
    E: EntityRepr,
{
    /// The blocks reachable from the entry block, in post-order.
    blocks: Vec<Block<E>>,

    /// Whether each block is reachable from the entry block, i.e. whether it
    /// appears in `blocks`.
    reachable: EntitySet<Block<E>>,
}

impl<E> Rpo<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        Rpo {
            blocks: Vec::new(),
            reachable: EntitySet::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self { blocks, reachable } = self;
        blocks.clear();
        reachable.reset();
    }

    pub fn is_reset(&self) -> bool {
        let Self { blocks, reachable } = self;
        blocks.is_empty() && reachable.is_reset()
    }

    /// Construct this `Rpo` in place for the given function.
    pub fn construct(
        &mut self,
        func: &impl InputFunction,
        dfs: &mut Dfs<E>,
        output: &mut OutputInner<E>,
    ) -> IResult<()> {
        let _timing = Timing::new("reverse post-order");

        debug_assert!(self.is_reset());
        self.blocks.reserve(func.len_blocks());

        dfs.construct(func, output)?;
        while let Some(event) = dfs.next(func, output, |block| self.reachable.contains(block))? {
            match event {
                DfsEvent::Pre(block) => {
                    self.reachable.insert(block);
                }
                DfsEvent::Post(block) => self.blocks.push(block),
                DfsEvent::AfterEdge(..) => {}
            }
        }

        Ok(())
    }

    /// Iterate over the reachable blocks in reverse post-order: a block always
    /// appears before any block that it dominates.
    ///
    /// Iterating in reverse therefore gives post-order, where a block always
    /// appears after every block it dominates.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = Block<E>> + DoubleEndedIterator + '_ {
        self.blocks.iter().copied().rev()
    }

    /// Is the given block reachable from the function's entry block?
    ///
    /// Unreachable blocks are not part of the traversal, and the rest of the
    /// allocator ignores them entirely.
    pub fn is_reachable(&self, block: Block<E>) -> bool {
        self.reachable.contains(block)
    }
}

impl<E> Default for Rpo<E>
where
    E: EntityRepr,
{
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{InputBlock as _, dominators::DominatorTree, test::*};
    use mutatis::check::{Check, CheckResult};
    use std::{
        collections::{BTreeSet, HashMap},
        format,
        string::String,
        vec,
    };

    fn rpo_of(func: &TestFunction) -> Rpo<u32> {
        let mut output = OutputInner::<u32>::new();
        let mut dfs = Dfs::<u32>::new();
        let mut rpo = Rpo::<u32>::new();
        rpo.construct(func, &mut dfs, &mut output).unwrap();
        rpo
    }

    #[test]
    fn rpo_properties() -> CheckResult<TestFunction> {
        Check::new()
            .min_iters(2_000)
            .min_duration(std::time::Duration::from_secs(2))
            .run(|func: &TestFunction| -> Result<(), String> {
                let rpo = rpo_of(func);
                let blocks: Vec<Block> = rpo.iter().collect();

                // Property 1: the traversal visits every block at most once.
                let mut seen = BTreeSet::new();
                for block in &blocks {
                    if !seen.insert(*block) {
                        return Err(format!(
                            "`Rpo::iter` visits {block:?} more than once: {blocks:?}"
                        ));
                    }
                }

                // Property 2: `iter` and `is_reachable` agree with each other.
                for (block, _) in func.blocks() {
                    if rpo.is_reachable(block) != seen.contains(&block) {
                        return Err(format!(
                            "`is_reachable({block:?})` is {} but `iter` visits {blocks:?}",
                            rpo.is_reachable(block),
                        ));
                    }
                }

                // Property 3: the reachable blocks are exactly the transitive
                // closure of the successor relation from the entry block,
                // computed here without any help from `Dfs`.
                let mut expected = BTreeSet::new();
                let mut stack = vec![func.entry_block()];
                while let Some(block) = stack.pop() {
                    if expected.insert(block) {
                        stack.extend(func.block(block).successors());
                    }
                }
                if seen != expected {
                    return Err(format!(
                        "`Rpo` says {seen:?} are reachable but the reachable blocks are \
                         {expected:?}"
                    ));
                }

                // Property 4: the entry block comes first.
                if blocks.first() != Some(&func.entry_block()) {
                    return Err(format!(
                        "`Rpo::iter` starts with {:?} but the entry block is {:?}",
                        blocks.first(),
                        func.entry_block(),
                    ));
                }

                // Property 5: a block always precedes every block that it
                // dominates. This is the property that the consumers of `Rpo`
                // actually rely on.
                let mut dominators = DominatorTree::new();
                dominators.compute(func);
                let position: HashMap<Block, usize> =
                    blocks.iter().enumerate().map(|(i, &b)| (b, i)).collect();
                for (&a, &i) in &position {
                    for (&b, &j) in &position {
                        if a != b && a.dominates(&dominators, b) && i > j {
                            return Err(format!(
                                "{a:?} dominates {b:?} but comes after it in {blocks:?}"
                            ));
                        }
                    }
                }

                // Property 6: iterating in reverse yields the same blocks in
                // the opposite order, so callers can get a post-order for
                // free.
                let mut backwards: Vec<Block> = rpo.iter().rev().collect();
                backwards.reverse();
                if backwards != blocks {
                    return Err(format!(
                        "`Rpo::iter` yields {blocks:?} forwards but {:?} backwards",
                        rpo.iter().rev().collect::<Vec<_>>(),
                    ));
                }
                if rpo.iter().len() != blocks.len() {
                    return Err(format!(
                        "`Rpo::iter().len()` is {} but it yields {} blocks",
                        rpo.iter().len(),
                        blocks.len(),
                    ));
                }

                Ok(())
            })
    }
}
