use crate::{
    Block, Entity as _, EntityRepr, InputBlock as _, InputFunction, error::IResult,
    output::OutputInner,
};
use alloc::vec::Vec;

/// An iterative depth-first traversal.
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
