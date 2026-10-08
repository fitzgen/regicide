use alloc::vec::Vec;
use core::{borrow::Borrow, cmp::Ordering};

/// A set kept as a sorted, deduplicated vector.
///
/// Whole-set unions merge in one pass, and `union_with_unsorted` builds a set
/// with one sort, but `insert` and `remove` shift the tail: liveness's
/// per-operand updates pay that, which is cheaper than a B-tree on these sets'
/// sizes.
#[derive(Clone, Debug)]
pub struct SortedVec<T> {
    inner: Vec<T>,
}

impl<T> SortedVec<T> {
    pub const fn new() -> Self {
        Self { inner: Vec::new() }
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    #[allow(dead_code, reason = "will probably need it")]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn clear(&mut self) {
        self.inner.clear();
    }

    fn search<Q>(&self, value: &Q) -> Result<usize, usize>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.inner.binary_search_by(|x| x.borrow().cmp(value))
    }

    /// Iterate over this set's elements in ascending order.
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.inner.iter()
    }

    /// Add every element of `other` to this set, returning whether that added
    /// anything that was not already here.
    pub fn union_with(&mut self, other: &Self) -> bool
    where
        T: Clone + Ord,
    {
        if self.inner.is_empty() {
            self.inner.extend_from_slice(&other.inner);
            return !other.inner.is_empty();
        }
        let ours = &self.inner;
        let theirs = &other.inner;

        // Count what is new first, so the merge can run back to front in place.
        let (mut i, mut j, mut new) = (0, 0, 0);
        while j < theirs.len() {
            if i == ours.len() {
                new += theirs.len() - j;
                break;
            }
            match ours[i].cmp(&theirs[j]) {
                Ordering::Less => i += 1,
                Ordering::Equal => (i, j) = (i + 1, j + 1),
                Ordering::Greater => (new, j) = (new + 1, j + 1),
            }
        }
        if new == 0 {
            return false;
        }

        let (mut i, mut j) = (ours.len(), theirs.len());
        let mut k = i + new;
        self.inner.resize(k, theirs[0].clone());
        while j > 0 {
            k -= 1;
            if i > 0 && self.inner[i - 1] > theirs[j - 1] {
                self.inner[k] = self.inner[i - 1].clone();
                i -= 1;
            } else {
                if i > 0 && self.inner[i - 1] == theirs[j - 1] {
                    i -= 1;
                }
                self.inner[k] = theirs[j - 1].clone();
                j -= 1;
            }
        }
        debug_assert_eq!(k, i);
        debug_assert!(self.inner.windows(2).all(|w| w[0] < w[1]));
        true
    }

    /// Add every element of `values`, in any order and with duplicates, and
    /// leave `values` empty. Returns whether that added anything that was not
    /// already here.
    ///
    /// One sort and one merge, where inserting one at a time would shift the
    /// tail for each.
    pub fn union_with_unsorted(&mut self, values: &mut Vec<T>) -> bool
    where
        T: Clone + Ord,
    {
        values.sort_unstable();
        values.dedup();
        let sorted = Self {
            inner: core::mem::take(values),
        };
        let changed = self.union_with(&sorted);
        *values = sorted.inner;
        values.clear();
        changed
    }

    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q> + Ord,
        Q: Ord,
        Q: ?Sized,
    {
        self.search(value).is_ok()
    }

    #[allow(dead_code, reason = "will probably need it")]
    pub fn get<Q>(&self, value: &Q) -> Option<&T>
    where
        T: Borrow<Q> + Ord,
        Q: Ord,
        Q: ?Sized,
    {
        self.search(value).ok().map(|i| &self.inner[i])
    }

    pub fn insert(&mut self, value: T) -> bool
    where
        T: Ord,
    {
        match self.search(&value) {
            Ok(_) => false,
            Err(i) => {
                self.inner.insert(i, value);
                true
            }
        }
    }

    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        match self.search(value) {
            Ok(i) => {
                self.inner.remove(i);
                true
            }
            Err(_) => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mutatis::{
        Mutate,
        check::{Check, CheckResult},
        mutators as m,
    };
    use std::{collections::BTreeSet as Oracle, string::String, vec, vec::Vec};

    /// Every operation agrees with `std`'s `BTreeSet`, on small values so that
    /// inserts, removes, and unions collide often.
    #[test]
    fn agrees_with_std() -> CheckResult<Vec<(u8, u8)>> {
        let mutator = m::default::<Vec<(u8, u8)>>().map(|_ctx, ops| {
            ops.truncate(64);
            Ok(())
        });
        Check::new().run_with(mutator, [Vec::new()], |ops| -> Result<(), String> {
            let mut sets = [SortedVec::new(), SortedVec::new()];
            let mut oracles = [Oracle::new(), Oracle::new()];
            for &(op, value) in ops {
                let value = value % 16;
                let s = usize::from(op & 1);
                match op / 2 % 5 {
                    0 => assert_eq!(sets[s].insert(value), oracles[s].insert(value)),
                    1 => assert_eq!(sets[s].remove(&value), oracles[s].remove(&value)),
                    2 => {
                        let [a, b] = &mut sets;
                        let (into, from) = if s == 0 { (a, &*b) } else { (b, &*a) };
                        let before = oracles[s].len();
                        let other = oracles[1 - s].clone();
                        oracles[s].extend(other);
                        assert_eq!(into.union_with(from), oracles[s].len() != before);
                    }
                    3 => {
                        // A few values from `value` up, out of order and with
                        // a repeat.
                        let mut values = vec![value, (value + 3) % 16, value, (value + 1) % 16];
                        let before = oracles[s].len();
                        oracles[s].extend(values.iter().copied());
                        assert_eq!(
                            sets[s].union_with_unsorted(&mut values),
                            oracles[s].len() != before
                        );
                        assert!(values.is_empty());
                    }
                    _ => {
                        sets[s].clear();
                        oracles[s].clear();
                    }
                }
                for (set, oracle) in sets.iter().zip(&oracles) {
                    assert!(set.iter().eq(oracle.iter()));
                    assert_eq!(set.contains(&value), oracle.contains(&value));
                }
            }
            Ok(())
        })
    }
}
