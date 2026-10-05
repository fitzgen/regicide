//! Fixed-capacity sets of entities.

use super::Entity;
use core::{
    cmp::Ordering,
    fmt::Debug,
    hash::{Hash, Hasher},
    marker::PhantomData,
};

type Word = u64;
const BITS: usize = Word::BITS as usize;

/// How many `Word`s a `FixedEntitySet` needs in order to hold `capacity`
/// entities.
pub const fn words_for(capacity: usize) -> usize {
    capacity.div_ceil(BITS)
}

/// Split an entity's index into the word that holds its bit and the bit within
/// that word.
#[inline]
#[allow(
    clippy::cast_possible_truncation,
    reason = "the remainder is less than `BITS`"
)]
fn word_and_bit(index: usize) -> (usize, u32) {
    (index / BITS, (index % BITS) as u32)
}

/// A set of entities of type `K`, holding up to `WORDS * 64` of them.
///
/// The parameter is a word count rather than a bit count because an array length
/// on stable Rust may be a const generic parameter but not an expression over
/// one. Use [`words_for`] to name it in terms of a capacity.
pub struct FixedEntitySet<K, const WORDS: usize> {
    words: [Word; WORDS],
    _phantom: PhantomData<fn() -> K>,
}

impl<K, const WORDS: usize> FixedEntitySet<K, WORDS> {
    /// How many entities this set can hold.
    pub const CAPACITY: usize = WORDS * BITS;

    /// Create a new, empty set.
    #[inline]
    pub const fn new() -> Self {
        Self {
            words: [0; WORDS],
            _phantom: PhantomData,
        }
    }

    /// Remove every entity from this set.
    #[inline]
    pub fn reset(&mut self) {
        let Self { words, _phantom } = self;
        words.fill(0);
    }

    /// Is this set empty?
    #[inline]
    pub fn is_reset(&self) -> bool {
        self.is_empty()
    }

    /// Is this set empty?
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// How many entities are in this set?
    #[inline]
    pub fn len(&self) -> usize {
        self.words
            .iter()
            .map(|w| usize::try_from(w.count_ones()).unwrap())
            .sum()
    }

    /// Is every entity in `self` also in `superset`?
    #[inline]
    pub fn is_subset_of(&self, superset: &Self) -> bool {
        self.words
            .iter()
            .zip(superset.words.iter())
            .all(|(l, r)| *l & *r == *l)
    }

    /// Create the set of entities that are in `self`, in `rhs`, or in both.
    #[inline]
    pub fn union(&self, rhs: &Self) -> Self {
        self.combine(rhs, |l, r| l | r)
    }

    /// Add every entity of `rhs` to `self`, returning whether that added
    /// anything `self` did not already have.
    #[inline]
    pub fn union_with(&mut self, rhs: &Self) -> bool {
        let mut grew = false;
        for i in 0..WORDS {
            let before = self.words[i];
            let after = before | rhs.words[i];
            grew |= after != before;
            self.words[i] = after;
        }
        grew
    }

    /// Replace this set's contents with `other`'s.
    #[inline]
    pub fn copy_from(&mut self, other: &Self) {
        self.words.copy_from_slice(&other.words);
    }

    /// Create the set of entities that are in both `self` and `rhs`.
    #[inline]
    pub fn intersection(&self, rhs: &Self) -> Self {
        self.combine(rhs, |l, r| l & r)
    }

    /// Create the set of entities that are in `self` but not in `rhs`.
    #[inline]
    pub fn difference(&self, rhs: &Self) -> Self {
        self.combine(rhs, |l, r| l & !r)
    }

    #[inline]
    fn combine(&self, rhs: &Self, f: impl Fn(Word, Word) -> Word) -> Self {
        let mut result = Self::new();
        for i in 0..WORDS {
            let word = f(self.words[i], rhs.words[i]);
            result.words[i] = word;
        }
        result
    }
}

impl<K, const WORDS: usize> FixedEntitySet<K, WORDS>
where
    K: Entity,
{
    /// Is `k` in this set?
    ///
    /// # Panics
    ///
    /// Panics if `k`'s index is not less than [`Self::CAPACITY`].
    pub fn contains(&self, k: K) -> bool {
        let (word, bit) = self.word_and_bit(k);
        self.words[word] & (1 << bit) != 0
    }

    /// Add `k` to this set, returning whether it was newly added.
    ///
    /// # Panics
    ///
    /// Panics if `k`'s index is not less than [`Self::CAPACITY`].
    pub fn insert(&mut self, k: K) -> bool {
        let (word, bit) = self.word_and_bit(k);
        let was_present = self.words[word] & (1 << bit) != 0;
        self.words[word] |= 1 << bit;
        !was_present
    }

    /// Remove `k` from this set, returning whether it was present.
    ///
    /// # Panics
    ///
    /// Panics if `k`'s index is not less than [`Self::CAPACITY`].
    pub fn remove(&mut self, k: K) -> bool {
        let (word, bit) = self.word_and_bit(k);
        let was_present = self.words[word] & (1 << bit) != 0;
        self.words[word] &= !(1 << bit);
        was_present
    }

    /// Iterate over the entities in this set, in ascending order.
    pub fn iter(&self) -> Iter<'_, K> {
        Iter {
            words: self.words.iter().enumerate(),
            word: 0,
            base: 0,
            _phantom: PhantomData,
        }
    }

    #[inline]
    fn word_and_bit(&self, k: K) -> (usize, u32) {
        assert!(
            k.index() < Self::CAPACITY,
            "entity index is beyond this set's capacity",
        );
        word_and_bit(k.index())
    }
}

// Manual impls so that we don't require `K: Clone` or `K: Copy`.
impl<K, const WORDS: usize> Copy for FixedEntitySet<K, WORDS> {}

impl<K, const WORDS: usize> Clone for FixedEntitySet<K, WORDS> {
    fn clone(&self) -> Self {
        Self {
            words: self.words,
            _phantom: PhantomData,
        }
    }
}

impl<K, const WORDS: usize> PartialEq for FixedEntitySet<K, WORDS> {
    fn eq(&self, other: &Self) -> bool {
        self.words == other.words
    }
}

impl<K, const WORDS: usize> Eq for FixedEntitySet<K, WORDS> {}

impl<K, const WORDS: usize> PartialOrd for FixedEntitySet<K, WORDS> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// The order is not meaningful -- it is neither the subset order nor the order
/// of the entities in the sets -- but it is total, which is all a map key
/// needs.
impl<K, const WORDS: usize> Ord for FixedEntitySet<K, WORDS> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.words.cmp(&other.words)
    }
}

impl<K, const WORDS: usize> Hash for FixedEntitySet<K, WORDS> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.words.hash(state);
    }
}

impl<K, const WORDS: usize> Debug for FixedEntitySet<K, WORDS>
where
    K: Debug + Entity,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("FixedEntitySet ")?;
        f.debug_set().entries(self.iter()).finish()
    }
}

/// A set serializes as an ascending array of its members' indices.
#[cfg(feature = "serialize")]
impl<K, const WORDS: usize> serde::Serialize for FixedEntitySet<K, WORDS>
where
    K: crate::entity::Entity + serde::Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.collect_seq(self.iter())
    }
}

/// An iterator over the entities in a [`FixedEntitySet`].
pub struct Iter<'a, K> {
    words: core::iter::Enumerate<core::slice::Iter<'a, Word>>,

    /// The bits of the word we are part way through, with the ones we have
    /// already yielded cleared.
    word: Word,

    /// The index of the first entity that `self.word` covers.
    base: usize,

    _phantom: PhantomData<fn() -> K>,
}

// Manual impl so that we don't require `K: Clone`.
impl<K> Clone for Iter<'_, K> {
    fn clone(&self) -> Self {
        Iter {
            words: self.words.clone(),
            word: self.word,
            base: self.base,
            _phantom: PhantomData,
        }
    }
}

impl<K> Iterator for Iter<'_, K>
where
    K: Entity,
{
    type Item = K;

    fn next(&mut self) -> Option<K> {
        loop {
            if self.word != 0 {
                let bit = self.word.trailing_zeros() as usize;
                // Clear the lowest set bit, so that the next call moves on.
                self.word &= self.word - 1;
                // Every entity in here was put in via a `K`, so its index fits.
                return Some(K::try_new(self.base + bit).unwrap());
            }

            let (i, &word) = self.words.next()?;
            self.word = word;
            self.base = i * BITS;
        }
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
    use std::{
        collections::BTreeSet,
        format,
        string::{String, ToString},
        vec,
        vec::Vec,
    };

    type TestSet = FixedEntitySet<Val, { words_for(128) }>;

    #[allow(
        clippy::cast_possible_truncation,
        reason = "the test set's capacity is 128"
    )]
    const CAPACITY: u32 = TestSet::CAPACITY as u32;

    #[derive(Clone, Debug, Mutate)]
    enum Op {
        Insert { index: u32 },
        Remove { index: u32 },
        Reset,
    }

    impl Default for Op {
        fn default() -> Self {
            Op::Insert { index: 0 }
        }
    }

    /// Check that `set` and `oracle` describe the same set.
    fn check_agree(set: &TestSet, oracle: &BTreeSet<Val>) -> Result<(), String> {
        if set.len() != oracle.len() {
            return Err(format!(
                "the set has {} entities but should have {}",
                set.len(),
                oracle.len(),
            ));
        }
        if set.is_empty() != oracle.is_empty() || set.is_reset() != oracle.is_empty() {
            return Err(format!(
                "`is_empty` is {} and `is_reset` is {}, but the set has {} entities",
                set.is_empty(),
                set.is_reset(),
                oracle.len(),
            ));
        }

        // `BTreeSet` also iterates in ascending order, so this pins down both the
        // contents and the order.
        let actual: Vec<Val> = set.iter().collect();
        let expected: Vec<Val> = oracle.iter().copied().collect();
        if actual != expected {
            return Err(format!(
                "the set holds {actual:?} but should hold {expected:?}"
            ));
        }

        Ok(())
    }

    #[test]
    fn fixed_entity_set_properties() -> CheckResult<Vec<Op>> {
        let mutator = m::default::<Vec<Op>>()
            .or(m::from_fn(
                |ctx: &mut mutatis::Context, ops: &mut Vec<Op>| {
                    let Some(i) = ctx.rng().gen_index(ops.len()) else {
                        ops.push(Op::Insert { index: 0 });
                        ops.push(Op::Insert { index: 127 });
                        ops.push(Op::Remove { index: 0 });
                        ops.push(Op::Remove { index: 127 });
                        ops.push(Op::Reset);
                        return Ok(());
                    };

                    let src_index = match ops[i] {
                        Op::Insert { index } | Op::Remove { index } => index,
                        Op::Reset => return Ok(()),
                    };

                    match ctx.rng().gen_u8() % 3 {
                        0 => ops.push(Op::Insert { index: src_index }),
                        1 => ops.push(Op::Remove { index: src_index }),
                        2 => {
                            let j = ctx.rng().gen_index(ops.len()).unwrap();
                            if i == j {
                                ops.push(if ctx.rng().gen_bool() {
                                    Op::Insert { index: src_index }
                                } else {
                                    Op::Remove { index: src_index }
                                });
                            } else {
                                match &mut ops[j] {
                                    Op::Insert { index } | Op::Remove { index } => {
                                        *index = src_index
                                    }
                                    Op::Reset => {}
                                }
                            }
                        }
                        _ => unreachable!(),
                    }

                    Ok(())
                },
            ))
            .map(|_ctx, ops| {
                ops.truncate(50);
                for op in ops.iter_mut() {
                    match op {
                        Op::Insert { index } | Op::Remove { index } => *index %= CAPACITY,
                        Op::Reset => {}
                    }
                }
                Ok(())
            });

        Check::new()
            .min_iters(1_000)
            .min_duration(std::time::Duration::from_secs(1))
            .run_with(
                mutator,
                [
                    vec![],
                    vec![Op::Insert { index: 0 }, Op::Remove { index: 0 }],
                    vec![Op::Insert { index: 63 }, Op::Remove { index: 63 }],
                    vec![Op::Insert { index: 64 }, Op::Remove { index: 64 }],
                    vec![Op::Insert { index: 127 }, Op::Remove { index: 127 }],
                ],
                |ops: &Vec<Op>| -> Result<(), String> {
                    let mut set = TestSet::new();
                    let mut oracle = BTreeSet::<Val>::new();

                    if !set.is_reset() {
                        return Err("a new set is not reset".to_string());
                    }
                    check_agree(&set, &oracle)?;

                    for op in ops {
                        match *op {
                            Op::Insert { index } => {
                                let val = Val::try_new(index as usize).unwrap();
                                let actual = set.insert(val);
                                let expected = oracle.insert(val);
                                if actual != expected {
                                    return Err(format!(
                                        "inserting {val:?} returned {actual} but should have \
                                     returned {expected}",
                                    ));
                                }
                            }
                            Op::Remove { index } => {
                                let val = Val::try_new(index as usize).unwrap();
                                let actual = set.remove(val);
                                let expected = oracle.remove(&val);
                                if actual != expected {
                                    return Err(format!(
                                        "removing {val:?} returned {actual} but should have \
                                     returned {expected}",
                                    ));
                                }
                            }
                            Op::Reset => {
                                set.reset();
                                oracle.clear();
                            }
                        }

                        check_agree(&set, &oracle)?;
                    }

                    for index in 0..CAPACITY {
                        let val = Val::try_new(index as usize).unwrap();
                        if set.contains(val) != oracle.contains(&val) {
                            return Err(format!(
                                "`contains({val:?})` is {} but should be {}",
                                set.contains(val),
                                oracle.contains(&val),
                            ));
                        }
                    }

                    Ok(())
                },
            )
    }

    /// Two sets to combine, plus how much of the first to reuse as a set that is
    /// a subset of it by construction.
    #[derive(Clone, Debug, Default, Mutate)]
    struct SetPair {
        lhs: Vec<u32>,
        rhs: Vec<u32>,
        lhs_prefix: u32,
    }

    /// Build both a set and its oracle out of `indices`.
    fn build(indices: &[u32]) -> (TestSet, BTreeSet<Val>) {
        let mut set = TestSet::new();
        let mut oracle = BTreeSet::new();
        for &index in indices {
            let val = Val::try_new(index as usize).unwrap();
            set.insert(val);
            oracle.insert(val);
        }
        (set, oracle)
    }

    #[test]
    fn fixed_entity_set_algebra() -> CheckResult<SetPair> {
        let mutator = m::default::<SetPair>().map(|_ctx, pair| {
            pair.lhs.truncate(50);
            pair.rhs.truncate(50);
            for index in pair.lhs.iter_mut().chain(pair.rhs.iter_mut()) {
                *index %= CAPACITY;
            }
            Ok(())
        });

        Check::new()
            .min_iters(1_000)
            .min_duration(std::time::Duration::from_secs(1))
            .run_with(
                mutator,
                [SetPair::default()],
                |pair: &SetPair| -> Result<(), String> {
                    let (a, oracle_a) = build(&pair.lhs);
                    let (b, oracle_b) = build(&pair.rhs);

                    let union = a.union(&b);
                    let expected: BTreeSet<Val> = oracle_a.union(&oracle_b).copied().collect();
                    check_agree(&union, &expected)?;

                    let intersection = a.intersection(&b);
                    let expected: BTreeSet<Val> =
                        oracle_a.intersection(&oracle_b).copied().collect();
                    check_agree(&intersection, &expected)?;

                    let difference = a.difference(&b);
                    let expected: BTreeSet<Val> = oracle_a.difference(&oracle_b).copied().collect();
                    check_agree(&difference, &expected)?;

                    for (x, oracle_x, y, oracle_y) in [
                        (&a, &oracle_a, &b, &oracle_b),
                        (&b, &oracle_b, &a, &oracle_a),
                    ] {
                        let actual = x.is_subset_of(y);
                        let expected = oracle_x.is_subset(oracle_y);
                        if actual != expected {
                            return Err(format!(
                                "`{x:?}.is_subset_of({y:?})` is {actual} but should be {expected}",
                            ));
                        }
                    }

                    // Test a set that is a subset of `a` by construction, because
                    // the `is_subset_of` check above is unlikely to exercise the
                    // `true`-returning case for random inputs.
                    let prefix = &pair.lhs[..(pair.lhs_prefix as usize).min(pair.lhs.len())];
                    let (c, oracle_c) = build(prefix);
                    let actual = c.is_subset_of(&a);
                    let expected = oracle_c.is_subset(&oracle_a);
                    if actual != expected {
                        return Err(format!(
                            "`{c:?}.is_subset_of({a:?})` is {actual} but should be {expected}",
                        ));
                    }

                    Ok(())
                },
            )
    }

    /// Build a set and a `BTreeSet` holding the entities at `indices`.
    fn set_of(indices: &[u32]) -> (TestSet, BTreeSet<Val>) {
        let mut set = TestSet::new();
        let mut oracle = BTreeSet::<Val>::new();
        for &index in indices {
            let val = Val::try_new((index % CAPACITY) as usize).unwrap();
            set.insert(val);
            oracle.insert(val);
        }
        (set, oracle)
    }

    #[test]
    fn union_with_and_copy_from_properties() -> CheckResult<(Vec<u32>, Vec<u32>)> {
        Check::new()
            .min_iters(1_000)
            .min_duration(std::time::Duration::from_secs(1))
            .run(|(lhs, rhs): &(Vec<u32>, Vec<u32>)| -> Result<(), String> {
                let (mut set, mut oracle) = set_of(lhs);
                let (other, other_oracle) = set_of(rhs);

                // The dataflow fixpoints key their worklists on this.
                let expected_grew = !other_oracle.is_subset(&oracle);
                let grew = set.union_with(&other);
                if grew != expected_grew {
                    return Err(format!(
                        "`union_with` returned {grew} but should have returned \
                             {expected_grew}",
                    ));
                }
                oracle.extend(other_oracle.iter().copied());
                check_agree(&set, &oracle)?;

                // It agrees with the by-value `union`.
                let (fresh, _) = set_of(lhs);
                if set.iter().collect::<Vec<_>>() != fresh.union(&other).iter().collect::<Vec<_>>()
                {
                    return Err("`union_with` and `union` disagree".to_string());
                }

                // Unioning the same thing in again cannot grow it.
                if set.union_with(&other) {
                    return Err("a repeated `union_with` reported growth".to_string());
                }
                check_agree(&set, &oracle)?;

                // `copy_from` clears whatever the union added.
                set.copy_from(&other);
                check_agree(&set, &other_oracle)?;

                Ok(())
            })
    }

    #[test]
    #[should_panic = "beyond this set's capacity"]
    fn insert_beyond_capacity_panics() {
        let mut set = TestSet::new();
        set.insert(Val::try_new(TestSet::CAPACITY).unwrap());
    }
}
