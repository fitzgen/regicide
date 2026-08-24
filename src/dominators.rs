//! Dominator trees.
//!
//! Derived from Cranelift's implementation in
//! `wasmtime/cranelift/codegen/src/dominator_tree.rs`.
//!
//! Dominators are computed with the Semi-NCA algorithm, described in
//!
//! * *Linear-Time Algorithms for Dominators and Related Problems.* Loukas
//!   Georgiadis, Princeton University, November 2005.

use crate::{Block, InputBlock as _, InputFunction, entity::SecondaryMap};
use alloc::{vec, vec::Vec};
use core::{
    cmp, mem,
    ops::{Index, IndexMut},
};

/// The DFS preorder number of unvisited blocks, and of the spanning tree's
/// virtual root.
const NOT_VISITED: u32 = 0;

/// A spanning tree node, used while computing the dominator tree.
#[derive(Clone, Debug, Default, Hash)]
struct SpanningTreeNode {
    /// This node's block in the function's CFG.
    block: Option<Block>,

    /// This node's ancestor in the spanning tree.
    ///
    /// Gets invalidated during semi-dominator computation.
    ancestor: u32,

    /// The smallest semi value discovered on any semi-dominator path that went
    /// through this node up till the moment.
    ///
    /// Gets updated in the course of semi-dominator computation.
    label: u32,

    /// The semidominator value for this node.
    semi: u32,

    /// The immediate dominator value for this node.
    ///
    /// Initialized to this node's ancestor in the spanning tree.
    idom: u32,
}

/// A spanning tree of the CFG, in preorder.
///
/// Node 0 is a virtual root and does not have a corresponding block. It isn't
/// strictly required, since a function's CFG always has a single root, but it
/// helps avoid additional checks.
#[derive(Clone, Debug, Hash)]
struct SpanningTree {
    nodes: Vec<SpanningTreeNode>,
}

impl SpanningTree {
    fn new() -> Self {
        Self {
            nodes: vec![
                // Include the virtual root.
                SpanningTreeNode::default(),
            ],
        }
    }

    fn len(&self) -> usize {
        self.nodes.len()
    }

    fn reserve(&mut self, capacity: usize) {
        self.nodes.reserve(capacity);
    }

    fn clear(&mut self) {
        // Keep the virtual root.
        self.nodes.truncate(1);
    }

    /// Push a new node, returning its preorder number.
    fn push(&mut self, ancestor: u32, block: Block) -> u32 {
        // The virtual root should already be included.
        debug_assert!(!self.nodes.is_empty());

        let pre_number = u32::try_from(self.nodes.len()).unwrap();

        self.nodes.push(SpanningTreeNode {
            block: Some(block),
            ancestor,
            label: pre_number,
            semi: pre_number,
            idom: ancestor,
        });

        pre_number
    }
}

impl Index<u32> for SpanningTree {
    type Output = SpanningTreeNode;

    fn index(&self, idx: u32) -> &Self::Output {
        &self.nodes[usize::try_from(idx).unwrap()]
    }
}

impl IndexMut<u32> for SpanningTree {
    fn index_mut(&mut self, idx: u32) -> &mut Self::Output {
        &mut self.nodes[usize::try_from(idx).unwrap()]
    }
}

/// A traversal event, used to compute both the preorder spanning tree and the
/// postorder block list.
enum TraversalEvent {
    Enter(u32, Block),
    Exit(Block),
}

/// A dominator tree node. We keep one of these per block.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
struct DomNode {
    /// The immediate dominator of this block, `None` for the entry block and
    /// for unreachable blocks.
    idom: Option<Block>,

    /// The CFG preorder traversal number, zero for unreachable blocks.
    pre_number: u32,

    /// The first child of this node in the dominator tree.
    child: Option<Block>,

    /// The next sibling of this node in the dominator tree. This linked list is
    /// ordered according to the CFG reverse postorder (i.e. decreasing CFG
    /// postorder number).
    sibling: Option<Block>,

    /// This node's number in a preorder traversal of the dominator tree.
    /// Unreachable blocks have number 0, and the entry block has number 1.
    dom_pre_number: u32,

    /// The maximum `dom_pre_number` in the dominator tree's subtree that is
    /// rooted at this node. This is always `>= dom_pre_number`.
    dom_pre_max: u32,
}

/// The dominator tree for a function.
#[derive(Clone, Debug, Hash)]
pub struct DominatorTree {
    /// The DFS spanning tree.
    stree: SpanningTree,

    /// The CFG's blocks, in postorder.
    postorder: Vec<Block>,

    /// The dominator tree's nodes.
    nodes: SecondaryMap<Block, DomNode>,

    valid: bool,
}

impl Default for DominatorTree {
    fn default() -> Self {
        Self::new()
    }
}

/// Methods for querying the dominator tree.
impl DominatorTree {
    /// Get the CFG postorder of blocks that was used to compute this dominator
    /// tree.
    #[allow(dead_code, reason = "will probably need it")]
    pub fn cfg_postorder(&self) -> &[Block] {
        debug_assert!(self.is_valid());
        &self.postorder
    }
}

/// Dominator tree queries about a block.
impl Block {
    /// Is this block reachable from the entry block?
    pub(crate) fn is_reachable(self, dominators: &DominatorTree) -> bool {
        debug_assert!(dominators.is_valid());
        dominators.nodes[self].pre_number != NOT_VISITED
    }

    /// Get the immediate dominator of this block.
    ///
    /// `a` is said to *dominate* `b` if all control-flow paths from the
    /// function entry to `b` must go through `a`. The *immediate dominator* is
    /// the dominator that is closest to this block; all of this block's other
    /// dominators also dominate its immediate dominator.
    ///
    /// Returns `None` if this is the entry block, which has no dominator other
    /// than itself, or if this block is not reachable from the entry block.
    pub(crate) fn idom(self, dominators: &DominatorTree) -> Option<Block> {
        debug_assert!(dominators.is_valid());
        dominators.nodes[self].idom
    }

    /// Does this block dominate `other`?
    ///
    /// That is, must every control-flow path from the function entry to `other`
    /// go through this block? A block is considered to dominate itself.
    ///
    /// This is `O(1)`: it checks whether this block's dominator tree preorder
    /// interval contains `other`'s.
    ///
    /// Dominance is ill-defined for blocks that are not reachable from the
    /// entry block.
    pub(crate) fn dominates(self, dominators: &DominatorTree, other: Block) -> bool {
        debug_assert!(dominators.is_valid());
        let a = &dominators.nodes[self];
        let b = &dominators.nodes[other];
        a.dom_pre_number <= b.dom_pre_number && a.dom_pre_max >= b.dom_pre_max
    }

    /// Get an iterator over the direct children of this block in the dominator
    /// tree.
    ///
    /// These are the blocks whose immediate dominator is this block, ordered by
    /// decreasing CFG postorder number.
    #[allow(dead_code, reason = "will probably need it")]
    pub(crate) fn dom_children(self, dominators: &DominatorTree) -> ChildIter<'_> {
        debug_assert!(dominators.is_valid());
        ChildIter {
            dominators,
            next: dominators.nodes[self].child,
        }
    }
}

/// Methods for constructing the dominator tree.
impl DominatorTree {
    /// Create a new, empty dominator tree.
    ///
    /// Use `DominatorTree::compute` to compute the dominator tree for a
    /// function.
    pub fn new() -> Self {
        Self {
            stree: SpanningTree::new(),
            postorder: Vec::new(),
            nodes: SecondaryMap::new(DomNode::default()),
            valid: false,
        }
    }

    /// Reset this dominator tree and recompute a CFG postorder and dominator
    /// tree for `func`.
    pub fn compute(&mut self, func: &impl InputFunction) {
        self.clear();
        self.compute_spanning_tree(func);
        self.compute_domtree(func);
        self.compute_domtree_preorder();
        self.valid = true;
    }

    /// Clear this dominator tree, leaving it in a state where
    /// `DominatorTree::is_valid` returns `false`.
    pub fn clear(&mut self) {
        let Self {
            stree,
            postorder,
            nodes,
            valid,
        } = self;
        stree.clear();
        postorder.clear();
        nodes.reset();
        *valid = false;
    }

    /// Is this dominator tree in a valid state?
    pub fn is_valid(&self) -> bool {
        self.valid
    }

    /// Build the spanning tree and compute a postorder of the control-flow
    /// graph.
    fn compute_spanning_tree(&mut self, func: &impl InputFunction) {
        self.stree.reserve(func.len_blocks());
        self.postorder.reserve(func.len_blocks());

        let mut worklist = vec![TraversalEvent::Enter(0, func.entry_block())];

        while let Some(event) = worklist.pop() {
            match event {
                TraversalEvent::Enter(parent, block) => {
                    if self.nodes[block].pre_number != NOT_VISITED {
                        continue;
                    }

                    worklist.push(TraversalEvent::Exit(block));

                    let pre_number = self.stree.push(parent, block);
                    self.nodes[block].pre_number = pre_number;

                    // Note that Cranelift visits successors in reverse here, but
                    // only as a heuristic to make the cached postorder nicer for
                    // its other consumers; it has no effect on the dominators
                    // that we compute. `TestBlockSuccessorsIter` is not a
                    // `DoubleEndedIterator`, so we simply don't.
                    for succ in func.block(block).successors() {
                        // A simple optimization: push fewer items to the stack.
                        if self.nodes[succ].pre_number == NOT_VISITED {
                            worklist.push(TraversalEvent::Enter(pre_number, succ));
                        }
                    }
                }
                TraversalEvent::Exit(block) => self.postorder.push(block),
            }
        }
    }

    fn compute_domtree(&mut self, func: &impl InputFunction) {
        let mut eval_worklist = Vec::new();

        // Compute the semidominators.
        for w in (1..u32::try_from(self.stree.len()).unwrap()).rev() {
            let block = self.stree[w]
                .block
                .expect("the virtual root must have been excluded");
            let mut semi = self.stree[w].ancestor;

            let last_linked = w + 1;

            for pred in func.block(block).predecessors() {
                // Skip unreachable blocks.
                let pred_pre_number = self.nodes[pred].pre_number;
                if pred_pre_number == NOT_VISITED {
                    continue;
                }

                let semi_candidate = eval(
                    &mut self.stree,
                    &mut eval_worklist,
                    pred_pre_number,
                    last_linked,
                );
                semi = cmp::min(semi, semi_candidate);
            }

            let w_node = &mut self.stree[w];
            w_node.label = semi;
            w_node.semi = semi;
        }

        // Compute the immediate dominators.
        for v in 1..u32::try_from(self.stree.len()).unwrap() {
            let semi = self.stree[v].semi;
            let block = self.stree[v]
                .block
                .expect("the virtual root must have been excluded");
            let mut idom = self.stree[v].idom;

            while idom > semi {
                idom = self.stree[idom].idom;
            }

            self.stree[v].idom = idom;

            self.nodes[block].idom = self.stree[idom].block;
        }
    }

    /// Compute the dominator tree's preorder information, populating the
    /// child/sibling links and the preorder numbers that give us `O(1)`
    /// dominance checks.
    fn compute_domtree_preorder(&mut self) {
        // Populate the child and sibling links.
        //
        // By following the CFG postorder and pushing to the front of the lists,
        // we make sure that sibling lists are ordered according to the CFG
        // reverse postorder (i.e. decreasing CFG postorder number).
        let mut worklist = Vec::new();
        for &block in &self.postorder {
            match self.nodes[block].idom {
                Some(idom) => {
                    let sib = mem::replace(&mut self.nodes[idom].child, Some(block));
                    self.nodes[block].sibling = sib;
                }
                // The only block without an immediate dominator is the root of
                // the dominator tree, i.e. the entry block.
                None => worklist.push(block),
            }
        }

        // Assign preorder numbers from a DFS of the dominator tree.
        //
        // Entering a node pushes its sibling and then its child, so the child is
        // popped first and the child's whole subtree lands on the stack above the
        // sibling. Each subtree therefore gets a contiguous range of numbers.
        let mut n = 0;
        while let Some(block) = worklist.pop() {
            n += 1;
            let node = &mut self.nodes[block];
            node.dom_pre_number = n;
            node.dom_pre_max = n;
            let (child, sibling) = (node.child, node.sibling);
            if let Some(sibling) = sibling {
                worklist.push(sibling);
            }
            if let Some(child) = child {
                worklist.push(child);
            }
        }

        // Propagate the `dom_pre_max` numbers up the tree.
        //
        // The CFG postorder is topologically ordered with respect to dominance,
        // so a block always comes after all of its dominator tree children.
        for &block in &self.postorder {
            if let Some(idom) = self.nodes[block].idom {
                let pre_max = cmp::max(self.nodes[block].dom_pre_max, self.nodes[idom].dom_pre_max);
                self.nodes[idom].dom_pre_max = pre_max;
            }
        }
    }
}

/// The eval-link procedure from the paper.
///
/// For a predecessor `v` of node `w`, returns `v` if `v < w`, and otherwise the
/// minimum of `sdom(u)`, where `u > w` and `u` is on a semi-dominator path for
/// `w` in the CFG.
///
/// Uses path compression to bring the complexity down to `O(m * log(n))`.
fn eval(stree: &mut SpanningTree, worklist: &mut Vec<u32>, v: u32, last_linked: u32) -> u32 {
    if stree[v].ancestor < last_linked {
        return stree[v].label;
    }

    // Follow the semi-dominator path.
    debug_assert!(worklist.is_empty());
    let mut root = v;
    loop {
        worklist.push(root);
        root = stree[root].ancestor;

        if stree[root].ancestor < last_linked {
            break;
        }
    }

    let mut prev = root;
    let root = stree[prev].ancestor;

    // Perform path compression. Point all ancestors at the root and propagate
    // the minimal `sdom(u)` value from ancestors to children.
    while let Some(curr) = worklist.pop() {
        if stree[prev].label < stree[curr].label {
            stree[curr].label = stree[prev].label;
        }

        stree[curr].ancestor = root;
        prev = curr;
    }

    stree[v].label
}

/// An iterator that enumerates the direct children of a block in the dominator
/// tree.
pub struct ChildIter<'a> {
    dominators: &'a DominatorTree,
    next: Option<Block>,
}

impl Iterator for ChildIter<'_> {
    type Item = Block;

    fn next(&mut self) -> Option<Block> {
        let n = self.next;
        if let Some(block) = n {
            self.next = self.dominators.nodes[block].sibling;
        }
        n
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test::TestFunction;
    use mutatis::check::{Check, CheckResult};
    use std::{
        collections::{BTreeSet, HashMap},
        format,
        string::{String, ToString},
    };

    /// Compute the set of blocks reachable from the entry block without ever
    /// entering `avoid`.
    ///
    /// This is a plain worklist over `successors()`, using neither
    /// `DominatorTree` nor `crate::dfs::Dfs`, so that it is an independent
    /// oracle rather than a restatement of the code under test.
    fn reachable_avoiding(func: &TestFunction, avoid: Option<Block>) -> BTreeSet<Block> {
        let mut visited = BTreeSet::new();

        let entry = func.entry_block();
        if Some(entry) == avoid {
            return visited;
        }
        visited.insert(entry);

        let mut worklist = vec![entry];
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

    /// For each block `a`, compute the set of blocks that `a` dominates.
    ///
    /// `a` dominates `b` when every control-flow path from the entry block to
    /// `b` goes through `a`, which is exactly when `b` becomes unreachable once
    /// `a` is removed from the CFG.
    ///
    /// Note that this makes dominance reflexive, since removing `a` from the
    /// graph makes `a` itself unreachable too.
    fn dominance_oracle(func: &TestFunction) -> HashMap<Block, BTreeSet<Block>> {
        let reachable = reachable_avoiding(func, None);
        func.blocks()
            .map(|(a, _)| {
                let without_a = reachable_avoiding(func, Some(a));
                let dominated = reachable.difference(&without_a).copied().collect();
                (a, dominated)
            })
            .collect()
    }

    #[test]
    fn dominator_tree_properties() -> CheckResult<TestFunction> {
        Check::new().iters(10_000).run(|func: &TestFunction| -> Result<(), String> {
            let entry = func.entry_block();
            let dominators = func.dominators();
            let blocks: Vec<Block> = func.blocks().map(|(b, _)| b).collect();

            // `TestFunction::fixup` is supposed to make every block reachable
            // from the entry block. If it didn't, that's a bug in the generator
            // rather than in the dominator tree, so check it on its own.
            let reachable = reachable_avoiding(func, None);
            if reachable.len() != blocks.len() {
                return Err(format!(
                    "only {} of this function's {} blocks are reachable from {entry:?}; \
                     `TestFunction::fixup` should have made them all reachable",
                    reachable.len(),
                    blocks.len(),
                ));
            }
            for b in &blocks {
                if !b.is_reachable(dominators) {
                    return Err(format!("`is_reachable({b:?})` is false"));
                }
            }

            let oracle = dominance_oracle(func);

            // `dominates` must agree with the definition of dominance for every
            // ordered pair of blocks. We go through the `InputBlock` trait method
            // rather than `DominatorTree` directly, since that is what the
            // register allocator will use.
            for a in &blocks {
                let input_block = func.block(*a);
                for b in &blocks {
                    let actual = input_block.dominates(*b);
                    let expected = oracle[a].contains(b);
                    if actual != expected {
                        return Err(format!(
                            "`{a:?}.dominates({b:?})` is {actual}, but {a:?} does {}dominate \
                             {b:?}",
                            if expected { "" } else { "not " },
                        ));
                    }
                }
            }

            // The entry block is the only block without an immediate dominator.
            for b in &blocks {
                let idom = func.block(*b).immediate_dominator();
                if (*b == entry) != idom.is_none() {
                    return Err(format!(
                        "`{b:?}.immediate_dominator()` is {idom:?}, but {b:?} is {}the entry \
                         block",
                        if *b == entry { "" } else { "not " },
                    ));
                }
            }

            // Walking up the immediate dominators from a block must enumerate
            // exactly that block's dominators, and must terminate at the entry
            // block.
            for b in &blocks {
                let expected: BTreeSet<Block> = blocks
                    .iter()
                    .copied()
                    .filter(|a| oracle[a].contains(b))
                    .collect();

                let mut chain = BTreeSet::new();
                let mut curr = Some(*b);
                while let Some(c) = curr {
                    if !chain.insert(c) {
                        return Err(format!(
                            "the immediate dominator chain of {b:?} revisits {c:?}, so it is not \
                             a tree"
                        ));
                    }
                    curr = func.block(c).immediate_dominator();
                }

                if !chain.contains(&entry) {
                    return Err(format!(
                        "the immediate dominator chain of {b:?} is {chain:?}, which does not \
                         reach {entry:?}"
                    ));
                }
                if chain != expected {
                    return Err(format!(
                        "the immediate dominator chain of {b:?} is {chain:?} but its dominators \
                         are {expected:?}"
                    ));
                }
            }

            // `children` must be exactly the inverse of `immediate_dominator`:
            // every block but the entry block is the child of exactly one block.
            let mut children = BTreeSet::new();
            for d in &blocks {
                for c in d.dom_children(dominators) {
                    if !children.insert(c) {
                        return Err(format!(
                            "{c:?} is a dominator tree child of more than one block"
                        ));
                    }
                    let idom = func.block(c).immediate_dominator();
                    if idom != Some(*d) {
                        return Err(format!(
                            "{c:?} is a dominator tree child of {d:?} but its immediate \
                             dominator is {idom:?}"
                        ));
                    }
                }
            }
            let expected_children: BTreeSet<Block> =
                blocks.iter().copied().filter(|b| *b != entry).collect();
            if children != expected_children {
                return Err(format!(
                    "the dominator tree's children are {children:?}, but every block except \
                     {entry:?} should be a child of some block"
                ));
            }

            // The cached CFG postorder must contain every reachable block exactly
            // once, and must end at the entry block.
            let postorder = dominators.cfg_postorder();
            let postorder_set: BTreeSet<Block> = postorder.iter().copied().collect();
            if postorder_set.len() != postorder.len() {
                return Err(format!("the CFG postorder {postorder:?} repeats a block"));
            }
            if postorder_set != reachable {
                return Err(format!(
                    "the CFG postorder {postorder:?} does not contain exactly the blocks \
                     reachable from {entry:?}"
                ));
            }
            if postorder.last() != Some(&entry) {
                return Err(format!(
                    "the CFG postorder {postorder:?} does not end at {entry:?}"
                ));
            }

            // Recomputing the dominator tree gives the same answer.
            let mut again = DominatorTree::new();
            again.compute(func);
            if again.postorder != dominators.postorder {
                return Err("recomputing gave a different CFG postorder".to_string());
            }
            for b in &blocks {
                if again.nodes[*b] != dominators.nodes[*b] {
                    return Err(format!(
                        "recomputing gave a different dominator tree node for {b:?}: {:?} \
                         versus {:?}",
                        again.nodes[*b], dominators.nodes[*b],
                    ));
                }
            }

            Ok(())
        })
    }
}
