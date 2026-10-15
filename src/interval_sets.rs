//! Sets of disjoint intervals, merged in time proportional to how often they
//! interleave. Each is a treap keyed by start and threaded with `next` links,
//! whose shape depends only on its members.

use crate::entity::{Entity, SecondaryMap};
use alloc::vec::Vec;
use core::fmt::Debug;

/// Steps along `next` before searching from the root.
///
/// One step, not none: the descent costs `O(log n)` fuel per boundary where a
/// step costs 1, and `check_disjoint` pays that per boundary, so dropping the
/// walk entirely made a finely interleaved refusal cost ~8x more fuel. That is
/// what a region's budget is charged, and at `RegionFuel::FLOOR` it decides
/// whether a merge happens at all. Beyond one step the walk stops paying for
/// itself; see the sweep in `reports/compilation-speedup-007/`.
const MAX_STEPS: u32 = 1;

/// Keeps debug cross-checks from going quadratic.
const DEBUG_WALK_LIMIT: usize = 256;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Refused {
    Overlap,

    /// The sets may still be disjoint.
    OutOfFuel,
}

/// A limit on tree nodes visited.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Fuel {
    limit: u64,
    spent: u64,
}

impl Fuel {
    pub fn new(limit: u64) -> Self {
        Fuel { limit, spent: 0 }
    }

    /// A limit for merging the sets of `n` intervals that only a pathological
    /// input exhausts: O(n log^2 n).
    pub fn safety_net(n: usize) -> u64 {
        let n = n as u64;
        let log_n = u64::from(n.max(1).ilog2()) + 1;
        64 * n * log_n * log_n + 1024
    }

    /// Includes a successful union's own work, so may exceed the limit.
    pub fn spent(&self) -> u64 {
        self.spent
    }

    #[inline]
    fn burn(&mut self) -> Result<(), Refused> {
        if self.spent >= self.limit {
            return Err(Refused::OutOfFuel);
        }
        self.spent += 1;
        Ok(())
    }
}

/// Arena storage for `IntervalSet<K>`s whose intervals span ranges of `P`
/// points.
pub(crate) struct IntervalSetArena<K, P>
where
    K: Entity,
{
    nodes: SecondaryMap<K, Option<Node<K, P>>>,

    /// Scratch: `(end of one run, start of the next)` from the last check.
    boundaries: Vec<(K, K)>,
}

/// A disjoint-interval set of `K`s.
///
/// A set's intervals are half-open, non-empty, and disjoint, so their ends sort
/// like their starts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct IntervalSet<K> {
    root: K,
    first: K,
    last: K,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Node<K, P> {
    start: P,
    end: P,
    left: Option<K>,
    right: Option<K>,
    next: Option<K>,
}

/// Where a top-down split or join attaches its next node.
#[derive(Clone, Copy)]
enum Hole<K> {
    Root,
    Left(K),
    Right(K),
}

/// splitmix64, because FxHash preserves the arithmetic progressions span
/// indices form and degenerates the treap.
#[inline]
fn priority<K: Entity>(k: K) -> u64 {
    let mut z = k.index() as u64;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

impl<K, P> IntervalSetArena<K, P>
where
    K: Entity,
    P: Copy + Ord + Debug,
{
    pub const fn new() -> Self {
        IntervalSetArena {
            nodes: SecondaryMap::new(None),
            boundaries: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self { nodes, boundaries } = self;
        nodes.reset();
        boundaries.clear();
    }

    pub fn is_reset(&self) -> bool {
        let Self { nodes, boundaries } = self;
        nodes.is_reset() && boundaries.is_empty()
    }

    #[inline]
    fn node(&self, k: K) -> &Node<K, P> {
        self.nodes
            .get(k)
            .and_then(Option::as_ref)
            .expect("only elements of some set are ever visited")
    }

    #[inline]
    fn node_mut(&mut self, k: K) -> &mut Node<K, P> {
        self.nodes
            .get_mut(k)
            .and_then(Option::as_mut)
            .expect("only elements of some set are ever visited")
    }

    #[inline]
    fn start(&self, k: K) -> P {
        self.node(k).start
    }

    #[inline]
    fn end(&self, k: K) -> P {
        self.node(k).end
    }

    /// The last element of `root`'s set ending by `key`, at or after `from`.
    fn last_ending_by(&self, from: K, root: K, key: P, fuel: &mut Fuel) -> Result<K, Refused> {
        debug_assert!(self.end(from) <= key);

        // A close interleaving needs only the one step.
        let mut p = from;
        for _ in 0..MAX_STEPS {
            fuel.burn()?;
            match self.node(p).next {
                Some(next) if self.end(next) <= key => p = next,
                _ => return Ok(p),
            }
        }

        // Ends sort like starts, so search by end.
        let mut node = Some(root);
        while let Some(n) = node {
            fuel.burn()?;
            if self.end(n) <= key {
                p = n;
                node = self.node(n).right;
            } else {
                node = self.node(n).left;
            }
        }
        Ok(p)
    }

    #[inline]
    fn fill(&mut self, root: &mut Option<K>, hole: Hole<K>, child: Option<K>) {
        match hole {
            Hole::Root => *root = child,
            Hole::Left(parent) => self.node_mut(parent).left = child,
            Hole::Right(parent) => self.node_mut(parent).right = child,
        }
    }

    /// Split `tree` into the elements starting before `key` and the rest.
    fn split(&mut self, tree: Option<K>, key: P, visits: &mut u64) -> (Option<K>, Option<K>) {
        let (mut lo, mut hi) = (None, None);
        let (mut lo_hole, mut hi_hole) = (Hole::Root, Hole::Root);
        let mut tree = tree;
        while let Some(n) = tree {
            *visits += 1;
            if self.start(n) < key {
                self.fill(&mut lo, lo_hole, Some(n));
                lo_hole = Hole::Right(n);
                tree = self.node(n).right;
            } else {
                self.fill(&mut hi, hi_hole, Some(n));
                hi_hole = Hole::Left(n);
                tree = self.node(n).left;
            }
        }
        self.fill(&mut lo, lo_hole, None);
        self.fill(&mut hi, hi_hole, None);
        (lo, hi)
    }

    /// Join two trees, `lo` entirely before `hi`.
    fn join(&mut self, lo: Option<K>, hi: Option<K>, visits: &mut u64) -> Option<K> {
        let mut root = None;
        let mut hole = Hole::Root;
        let (mut lo, mut hi) = (lo, hi);
        loop {
            *visits += 1;
            match (lo, hi) {
                (Some(l), Some(h)) => {
                    debug_assert!(self.start(l) < self.start(h));
                    if priority(l) > priority(h) {
                        self.fill(&mut root, hole, Some(l));
                        hole = Hole::Right(l);
                        lo = self.node(l).right;
                    } else {
                        self.fill(&mut root, hole, Some(h));
                        hole = Hole::Left(h);
                        hi = self.node(h).left;
                    }
                }
                (rest, None) | (None, rest) => {
                    self.fill(&mut root, hole, rest);
                    return root;
                }
            }
        }
    }

    fn self_or_descendant(&self, k: K, child: impl Fn(&Node<K, P>) -> Option<K>) -> K {
        let mut k = k;
        while let Some(c) = child(self.node(k)) {
            k = c;
        }
        k
    }
}

impl<K> IntervalSet<K>
where
    K: Entity,
{
    /// Make `k` a set of its own, covering `[start, end)`.
    pub fn singleton<P>(arena: &mut IntervalSetArena<K, P>, k: K, start: P, end: P) -> Self
    where
        P: Copy + Ord + Debug,
    {
        debug_assert!(start < end);
        arena.nodes[k] = Some(Node {
            start,
            end,
            left: None,
            right: None,
            next: None,
        });
        IntervalSet {
            root: k,
            first: k,
            last: k,
        }
    }

    /// The set's elements in ascending order.
    pub fn iter<P>(self, arena: &IntervalSetArena<K, P>) -> impl Iterator<Item = K> + '_
    where
        P: Copy + Ord + Debug,
    {
        core::iter::successors(Some(self.first), move |&k| arena.node(k).next)
    }

    /// Merge `self` and `other` if disjoint.
    ///
    /// A successful union invalidates `self` and `other`. On `Err`, both are
    /// unchanged.
    pub fn try_union<P>(
        self,
        arena: &mut IntervalSetArena<K, P>,
        other: Self,
        fuel: &mut Fuel,
    ) -> Result<Self, Refused>
    where
        P: Copy + Ord + Debug,
    {
        debug_assert_ne!(self.root, other.root);

        let self_first = match self.check_disjoint(arena, other, fuel) {
            Ok(self_first) => self_first,
            Err(refused) => {
                arena.boundaries.clear();
                debug_assert!(
                    refused == Refused::OutOfFuel
                        || self.overlap_by_walking(arena, other, DEBUG_WALK_LIMIT) != Some(false),
                    "refused as overlapping, but the sets are disjoint",
                );
                return Err(refused);
            }
        };

        debug_assert_ne!(
            self.overlap_by_walking(arena, other, DEBUG_WALK_LIMIT),
            Some(true)
        );

        let set = match other.first == other.last {
            true => {
                let mut visits = 0;
                let set = self.insert_one(arena, other, &mut visits);
                fuel.spent += visits;
                arena.boundaries.clear();
                set
            }
            false => self.union(arena, other, self_first, fuel),
        };

        #[cfg(debug_assertions)]
        set.assert_valid(arena, DEBUG_WALK_LIMIT);

        Ok(set)
    }

    /// Record run boundaries if `self` and `other` are disjoint. Returns
    /// whether `self` comes first.
    fn check_disjoint<P>(
        self,
        arena: &mut IntervalSetArena<K, P>,
        other: Self,
        fuel: &mut Fuel,
    ) -> Result<bool, Refused>
    where
        P: Copy + Ord + Debug,
    {
        debug_assert!(arena.boundaries.is_empty());

        if arena.end(self.last) <= arena.start(other.first) {
            arena.boundaries.push((self.last, other.first));
            return Ok(true);
        }
        if arena.end(other.last) <= arena.start(self.first) {
            arena.boundaries.push((other.last, self.first));
            return Ok(false);
        }

        // `(element, root)` pairs; `x` starts first.
        let (mut x, mut y) = ((self.first, self.root), (other.first, other.root));
        let mut x_is_self = true;
        let mut self_first = true;
        loop {
            fuel.burn()?;
            if arena.start(y.0) < arena.start(x.0) {
                core::mem::swap(&mut x, &mut y);
                x_is_self = !x_is_self;
            }
            let y_start = arena.start(y.0);
            if arena.end(x.0) > y_start {
                return Err(Refused::Overlap);
            }

            // `x`'s set is sorted, so everything up to `p` precedes `y`.
            let p = arena.last_ending_by(x.0, x.1, y_start, fuel)?;
            if arena.boundaries.is_empty() {
                self_first = x_is_self;
            }
            debug_assert!(arena.end(p) <= y_start);
            arena.boundaries.push((p, y.0));

            match arena.node(p).next {
                // The rest of `y`'s set follows.
                None => return Ok(self_first),
                Some(next) => x.0 = next,
            }
        }
    }

    /// Insert the single node `other` into `self`.
    ///
    /// Over half of all unions add one interval, where the general merge
    /// splits the tree apart and joins it back; this descends once and
    /// splits only the subtree the new node displaces.
    ///
    /// Exactly one `boundaries` pair mentions `other`, and the node follows
    /// that pair's `p` in the `next` chain unless it is `p`, in which case it
    /// precedes the whole set.
    fn insert_one<P>(
        self,
        arena: &mut IntervalSetArena<K, P>,
        other: Self,
        visits: &mut u64,
    ) -> Self
    where
        P: Copy + Ord + Debug,
    {
        debug_assert_eq!(other.first, other.last);
        let node = other.root;

        // Splice into the `next` chain the tree is kept alongside.
        let first = match arena
            .boundaries
            .iter()
            .find(|&&(p, q)| p == node || q == node)
        {
            // `node` precedes the whole set.
            Some(&(p, q)) if p == node => {
                arena.node_mut(node).next = Some(q);
                node
            }
            Some(&(p, _)) => {
                arena.node_mut(node).next = arena.node(p).next;
                arena.node_mut(p).next = Some(node);
                self.first
            }
            None => unreachable!("a boundary always mentions the inserted node"),
        };

        // Descend while the nodes outrank `node`, then split the subtree it
        // displaces around its key.
        let key = arena.start(node);
        let pri = priority(node);
        let mut root = None;
        let mut hole = Hole::Root;
        let mut tree = Some(self.root);
        while let Some(n) = tree {
            if priority(n) < pri {
                break;
            }
            *visits += 1;
            let left = key < arena.start(n);
            arena.fill(&mut root, hole, Some(n));
            hole = match left {
                true => Hole::Left(n),
                false => Hole::Right(n),
            };
            tree = match left {
                true => arena.node(n).left,
                false => arena.node(n).right,
            };
        }
        let (lo, hi) = arena.split(tree, key, visits);
        arena.node_mut(node).left = lo;
        arena.node_mut(node).right = hi;
        arena.fill(&mut root, hole, Some(node));

        let set = IntervalSet {
            root: root.expect("the tree is never empty"),
            first,
            last: match key > arena.start(self.last) {
                true => node,
                false => self.last,
            },
        };
        debug_assert_eq!(arena.self_or_descendant(set.root, |n| n.left), set.first);
        debug_assert_eq!(arena.self_or_descendant(set.root, |n| n.right), set.last);
        set
    }

    /// Merge `self` and `other` along the run boundaries recorded by
    /// `check_disjoint`.
    fn union<P>(
        self,
        arena: &mut IntervalSetArena<K, P>,
        other: Self,
        self_first: bool,
        fuel: &mut Fuel,
    ) -> Self
    where
        P: Copy + Ord + Debug,
    {
        let boundaries = core::mem::take(&mut arena.boundaries);
        debug_assert!(!boundaries.is_empty());

        // Runs alternate sets, starting with `sets[0]`.
        let sets = if self_first {
            [self, other]
        } else {
            [other, self]
        };
        let mut rest = [Some(sets[0].root), Some(sets[1].root)];
        let mut merged = None;
        let mut visits = 0;
        for (i, &(_, next_own_run)) in boundaries.iter().enumerate().skip(1) {
            let own = (i - 1) % 2;
            let (run, after) = arena.split(rest[own], arena.start(next_own_run), &mut visits);
            rest[own] = after;
            merged = arena.join(merged, run, &mut visits);
        }
        let k = boundaries.len();
        merged = arena.join(merged, rest[(k - 1) % 2], &mut visits);
        merged = arena.join(merged, rest[k % 2], &mut visits);

        for &(p, q) in &boundaries {
            debug_assert!(arena.end(p) <= arena.start(q));
            arena.node_mut(p).next = Some(q);
        }

        fuel.spent += visits;
        arena.boundaries = boundaries;
        arena.boundaries.clear();

        let last = core::cmp::max_by_key(self.last, other.last, |&k| arena.start(k));
        let set = IntervalSet {
            root: merged.expect("merging two non-empty sets"),
            first: sets[0].first,
            last,
        };
        debug_assert_eq!(arena.self_or_descendant(set.root, |n| n.left), set.first);
        debug_assert_eq!(arena.self_or_descendant(set.root, |n| n.right), set.last);
        set
    }

    /// A naive cross-check of `check`. `None` past `limit` steps.
    fn overlap_by_walking<P>(
        self,
        arena: &IntervalSetArena<K, P>,
        other: Self,
        limit: usize,
    ) -> Option<bool>
    where
        P: Copy + Ord + Debug,
    {
        let (mut x, mut y) = (Some(self.first), Some(other.first));
        let mut steps = 0;
        while let (Some(sx), Some(sy)) = (x, y) {
            steps += 1;
            if steps > limit {
                return None;
            }
            if arena.start(sx) < arena.end(sy) && arena.start(sy) < arena.end(sx) {
                return Some(true);
            }
            if arena.end(sx) <= arena.start(sy) {
                x = arena.node(sx).next;
            } else {
                y = arena.node(sy).next;
            }
        }
        Some(false)
    }

    /// Skipped for sets of more than `limit` elements.
    #[cfg(any(test, debug_assertions))]
    fn assert_valid<P>(self, arena: &IntervalSetArena<K, P>, limit: usize)
    where
        P: Copy + Ord + Debug,
    {
        // No recursion: trees can be deep.
        let mut in_order = Vec::new();
        let mut stack = Vec::new();
        let mut node = Some(self.root);
        loop {
            while let Some(n) = node {
                stack.push(n);
                node = arena.node(n).left;
            }
            let Some(n) = stack.pop() else { break };
            in_order.push(n);
            if in_order.len() > limit {
                return;
            }
            node = arena.node(n).right;
        }

        assert_eq!(in_order.first(), Some(&self.first));
        assert_eq!(in_order.last(), Some(&self.last));
        for &k in &in_order {
            let n = arena.node(k);
            assert!(n.start < n.end, "{k:?} is empty");
            for child in [n.left, n.right].into_iter().flatten() {
                assert!(
                    priority(k) > priority(child),
                    "{k:?} is above {child:?} but has a lower priority",
                );
            }
        }
        for pair in in_order.windows(2) {
            let (p, q) = (pair[0], pair[1]);
            assert!(
                arena.end(p) <= arena.start(q),
                "{p:?} and {q:?} are out of order or overlap",
            );
            assert_eq!(arena.node(p).next, Some(q));
        }
        assert_eq!(arena.node(self.last).next, None);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::entity::Val;
    use mutatis::{
        Mutate,
        check::{Check, CheckResult},
        mutators as m,
    };
    use std::{format, string::String, vec, vec::Vec};

    type V = Val<u32>;
    type Arena = IntervalSetArena<V, u32>;

    fn v(i: usize) -> V {
        V::try_new(i).unwrap()
    }

    /// The treap `elems` defines, built straight from the definition.
    fn canonical(elems: &[V], children: &mut Vec<(V, Option<V>, Option<V>)>) -> Option<V> {
        let (i, &root) = elems
            .iter()
            .enumerate()
            .max_by_key(|&(_, &k)| priority(k))?;
        let left = canonical(&elems[..i], children);
        let right = canonical(&elems[i + 1..], children);
        children.push((root, left, right));
        Some(root)
    }

    fn depths(arena: &Arena, set: IntervalSet<V>) -> Vec<usize> {
        let mut depths = vec![];
        let mut stack = vec![(set.root, 1)];
        while let Some((k, depth)) = stack.pop() {
            depths.push(depth);
            let n = arena.node(k);
            stack.extend(n.left.map(|c| (c, depth + 1)));
            stack.extend(n.right.map(|c| (c, depth + 1)));
        }
        depths
    }

    #[test]
    fn reset_clears_scratch_from_an_abandoned_run() {
        let mut arena = Arena::new();
        IntervalSet::singleton(&mut arena, v(0), 0, 1);
        arena.boundaries.push((v(0), v(1)));
        assert!(!arena.is_reset());

        arena.reset();
        assert!(arena.is_reset());
    }

    #[test]
    fn a_set_inside_one_gap_of_another_merges_in_few_steps() {
        let mut arena = Arena::new();
        let n = 1_000;

        let mut outer = IntervalSet::singleton(&mut arena, v(0), 0, 1);
        let far = IntervalSet::singleton(&mut arena, v(1), 10_000, 10_001);
        outer = outer
            .try_union(&mut arena, far, &mut Fuel::new(u64::MAX))
            .unwrap();

        let mut inner = IntervalSet::singleton(&mut arena, v(2), 10, 11);
        for i in 1..n {
            let k = v(2 + i);
            let start = u32::try_from(10 + 2 * i).unwrap();
            let one = IntervalSet::singleton(&mut arena, k, start, start + 1);
            inner = inner
                .try_union(&mut arena, one, &mut Fuel::new(u64::MAX))
                .unwrap();
        }

        let mut fuel = Fuel::new(u64::MAX);
        let merged = outer.try_union(&mut arena, inner, &mut fuel).unwrap();
        assert!(fuel.spent() < 200, "spent {}", fuel.spent());
        assert_eq!(merged.iter(&arena).count(), n + 2);
        merged.assert_valid(&arena, usize::MAX);
    }

    #[test]
    fn a_long_interleaving_runs_out_of_fuel() {
        let mut arena = Arena::new();
        let n = 512;
        let mut sets: [Option<IntervalSet<V>>; 2] = [None, None];
        for i in 0..2 * n {
            let start = u32::try_from(2 * i).unwrap();
            let one = IntervalSet::singleton(&mut arena, v(i), start, start + 1);
            let set = &mut sets[i % 2];
            *set = Some(match *set {
                None => one,
                Some(set) => set
                    .try_union(&mut arena, one, &mut Fuel::new(u64::MAX))
                    .unwrap(),
            });
        }
        // One overlap, at the far end.
        let [a, b] = sets.map(Option::unwrap);
        let one = IntervalSet::singleton(&mut arena, v(2 * n), 10_000, 10_010);
        let a = a
            .try_union(&mut arena, one, &mut Fuel::new(u64::MAX))
            .unwrap();
        let one = IntervalSet::singleton(&mut arena, v(2 * n + 1), 10_005, 10_020);
        let b = b
            .try_union(&mut arena, one, &mut Fuel::new(u64::MAX))
            .unwrap();

        let snapshot =
            |arena: &Arena| -> Vec<_> { (0..2 * n + 2).map(|i| arena.nodes[v(i)]).collect() };
        let before = snapshot(&arena);
        let mut fuel = Fuel::new(100);
        assert_eq!(
            a.try_union(&mut arena, b, &mut fuel),
            Err(Refused::OutOfFuel)
        );
        assert_eq!(fuel.spent(), 100);
        let after = snapshot(&arena);
        assert_eq!(before, after);

        let mut fuel = Fuel::new(u64::MAX);
        assert_eq!(a.try_union(&mut arena, b, &mut fuel), Err(Refused::Overlap));
    }

    #[test]
    fn arithmetic_progressions_build_shallow_trees() {
        let n: usize = 2_048;
        let log_n = f64::from(n.ilog2());
        for stride in [1, 2, 4, 8, 22, 23, 64, 257] {
            let mut arena = Arena::new();
            let mut set = IntervalSet::singleton(&mut arena, v(0), 0, 1);
            for i in 1..n {
                let start = u32::try_from(i).unwrap();
                let one = IntervalSet::singleton(&mut arena, v(i * stride), start, start + 1);
                set = set
                    .try_union(&mut arena, one, &mut Fuel::new(u64::MAX))
                    .unwrap();
            }
            set.assert_valid(&arena, usize::MAX);

            let depths = depths(&arena, set);
            assert_eq!(depths.len(), n);
            let max = *depths.iter().max().unwrap() as f64;
            let mean = depths.iter().sum::<usize>() as f64 / n as f64;
            assert!(
                mean <= 2.0 * log_n && max <= 4.0 * log_n,
                "stride {stride}: mean depth {mean}, max depth {max}, log2(n) {log_n}",
            );
        }
    }

    #[test]
    fn unions_match_a_model() -> CheckResult<(Vec<(u8, u8)>, Vec<(u8, u8, u8)>)> {
        let mutator = m::default::<(Vec<(u8, u8)>, Vec<(u8, u8, u8)>)>().map(|_ctx, input| {
            let (intervals, unions) = input;
            intervals.truncate(64);
            unions.truncate(128);
            Ok(())
        });
        Check::new().run_with(
            mutator,
            [(Vec::new(), Vec::new())],
            |(intervals, unions): &(Vec<(u8, u8)>, Vec<(u8, u8, u8)>)| -> Result<(), String> {
                if intervals.is_empty() {
                    return Ok(());
                }
                let len = intervals.len();

                // Spread out, so many are disjoint.
                let bounds: Vec<(u32, u32)> = intervals
                    .iter()
                    .map(|&(start, len)| {
                        let start = u32::from(start) * 4;
                        (start, start + 1 + u32::from(len % 8))
                    })
                    .collect();

                let mut arena = Arena::new();
                let mut handles: Vec<IntervalSet<V>> = bounds
                    .iter()
                    .enumerate()
                    .map(|(i, &(start, end))| IntervalSet::singleton(&mut arena, v(i), start, end))
                    .collect();
                // Model sets, named by smallest member.
                let mut owner: Vec<usize> = (0..len).collect();
                let mut members: Vec<Vec<usize>> = (0..len).map(|i| vec![i]).collect();

                for &(a, b, fuel) in unions {
                    let (sa, sb) = (owner[usize::from(a) % len], owner[usize::from(b) % len]);
                    if sa == sb {
                        continue;
                    }

                    let overlaps = members[sa].iter().any(|&x| {
                        members[sb].iter().any(|&y| {
                            let ((xs, xe), (ys, ye)) = (bounds[x], bounds[y]);
                            xs < ye && ys < xe
                        })
                    });

                    // Small fuel, or none at all.
                    let limit = if fuel < 128 {
                        u64::from(fuel)
                    } else {
                        u64::MAX
                    };
                    let before: Vec<_> = (0..len).map(|i| arena.nodes[v(i)]).collect();
                    let result =
                        handles[sa].try_union(&mut arena, handles[sb], &mut Fuel::new(limit));

                    let merged = match result {
                        Err(Refused::OutOfFuel) if limit != u64::MAX => None,
                        Err(Refused::Overlap) if overlaps => None,
                        Ok(merged) if !overlaps => Some(merged),
                        other => {
                            return Err(format!(
                                "{:?} and {:?} {} overlap, but merging them gave {other:?}",
                                members[sa],
                                members[sb],
                                if overlaps { "do" } else { "do not" },
                            ));
                        }
                    };
                    let Some(merged) = merged else {
                        let after: Vec<_> = (0..len).map(|i| arena.nodes[v(i)]).collect();
                        if before != after {
                            return Err("a refused union changed a set".into());
                        }
                        continue;
                    };

                    let (keep, gone) = (sa.min(sb), sa.max(sb));
                    let moved = core::mem::take(&mut members[gone]);
                    for &x in &moved {
                        owner[x] = keep;
                    }
                    members[keep].extend(moved);
                    members[keep].sort_by_key(|&x| bounds[x].0);
                    handles[keep] = merged;

                    merged.assert_valid(&arena, usize::MAX);
                    let elems: Vec<V> = members[keep].iter().map(|&x| v(x)).collect();
                    if merged.iter(&arena).ne(elems.iter().copied()) {
                        return Err(format!(
                            "merged to {:?}, expected {elems:?}",
                            merged.iter(&arena).collect::<Vec<_>>(),
                        ));
                    }

                    let mut children = vec![];
                    let root = canonical(&elems, &mut children);
                    if root != Some(merged.root) {
                        return Err(format!("rooted at {:?}, not {root:?}", merged.root));
                    }
                    for (k, left, right) in children {
                        let n = arena.node(k);
                        if (n.left, n.right) != (left, right) {
                            return Err(format!(
                                "{k:?} has children {:?}, not {:?}",
                                (n.left, n.right),
                                (left, right),
                            ));
                        }
                    }
                }
                Ok(())
            },
        )
    }
}
