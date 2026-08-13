use super::Entity;
use alloc::vec::Vec;
use core::{fmt::Debug, marker::PhantomData};

type Word = u64;
const BITS: usize = Word::BITS as usize;

#[inline]
fn word_and_bit(index: usize) -> (usize, u32) {
    (index / BITS, (index % BITS) as u32)
}

/// A set of entities of type `K`.
pub(crate) struct EntitySet<K> {
    words: Vec<Word>,
    len: usize,
    _phantom: PhantomData<fn() -> K>,
}

impl<K> EntitySet<K> {
    /// Create a new, empty set.
    pub const fn new() -> Self {
        Self {
            words: Vec::new(),
            len: 0,
            _phantom: PhantomData,
        }
    }

    pub fn reset(&mut self) {
        let Self {
            words,
            len,
            _phantom,
        } = self;
        words.fill(0);
        *len = 0;
    }

    pub fn is_reset(&self) -> bool {
        self.is_empty()
    }

    /// Is this set empty?
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// How many entities are in this set?
    pub fn len(&self) -> usize {
        self.len
    }
}

impl<K> EntitySet<K>
where
    K: Entity,
{
    /// Is `k` in this set?
    pub fn contains(&self, k: K) -> bool {
        let (word, bit) = word_and_bit(k.index());
        // An entity whose word we never grew into cannot have been inserted, so
        // this is `false` rather than out of bounds.
        match self.words.get(word) {
            Some(word) => word & (1 << bit) != 0,
            None => false,
        }
    }

    /// Add `k` to this set, returning whether it was newly added.
    pub fn insert(&mut self, k: K) -> bool {
        let (word, bit) = word_and_bit(k.index());
        if word >= self.words.len() {
            // `Vec` already grows geometrically, so this is amortized constant
            // time even when inserting ascending entities one at a time.
            self.words.resize(word + 1, 0);
        }
        let was_present = self.words[word] & (1 << bit) != 0;
        self.words[word] |= 1 << bit;
        self.len += (!was_present) as usize;
        !was_present
    }

    /// Remove `k` from this set, returning whether it was present.
    pub fn remove(&mut self, k: K) -> bool {
        let (word, bit) = word_and_bit(k.index());
        // No need to grow: a bit that has no word cannot be set.
        match self.words.get_mut(word) {
            Some(w) => {
                let was_present = *w & (1 << bit) != 0;
                *w &= !(1 << bit);
                self.len -= was_present as usize;
                was_present
            }
            None => false,
        }
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
}

impl<K> Debug for EntitySet<K>
where
    K: Debug + Entity,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("EntitySet ")?;
        f.debug_set().entries(self.iter()).finish()
    }
}

/// An iterator over the entities in an [`EntitySet`].
pub(crate) struct Iter<'a, K> {
    words: core::iter::Enumerate<core::slice::Iter<'a, Word>>,

    /// The bits of the word we are part way through, with the ones we have
    /// already yielded cleared.
    word: Word,

    /// The index of the first entity that `self.word` covers.
    base: usize,

    _phantom: PhantomData<fn() -> K>,
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
        vec::Vec,
    };

    /// The entity indices that a generated operation may name.
    ///
    /// Sixteen words, which is enough to cover the word boundaries at 63/64 and
    /// 127/128, growing into a high index from empty, and growing again after a
    /// `reset`, without making each iteration expensive.
    const MAX_INDEX: u32 = 16 * BITS as u32;

    /// One entity index past every word that an operation can touch, so that
    /// probing up to here reaches past the end of the set's storage.
    const PROBE_LIMIT: u32 = MAX_INDEX + BITS as u32;

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
    fn check_agree(set: &EntitySet<Val>, oracle: &BTreeSet<Val>) -> Result<(), String> {
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
    fn entity_set_properties() -> CheckResult<Vec<Op>> {
        let mutator = m::default::<Vec<Op>>().map(|_ctx, ops| {
            ops.truncate(50);
            for op in ops.iter_mut() {
                match op {
                    Op::Insert { index } | Op::Remove { index } => *index %= MAX_INDEX,
                    Op::Reset => {}
                }
            }
            Ok(())
        });

        Check::new().iters(10_000).run_with(
            mutator,
            [
                alloc::vec![Op::Insert { index: 0 }, Op::Remove { index: 0 }],
                alloc::vec![Op::Insert { index: 63 }, Op::Remove { index: 63 }],
                alloc::vec![Op::Insert { index: 64 }, Op::Remove { index: 64 }],
                alloc::vec![Op::Insert { index: 150 }, Op::Remove { index: 150 }],
            ],
            |ops: &Vec<Op>| -> Result<(), String> {
                let mut set = EntitySet::<Val>::new();
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

                // Finally, ask about every entity the operations could have
                // named and then some, which reaches past the end of the set's
                // storage. Iteration alone would not catch a bit set outside the
                // range it walks, or a `contains` reading the wrong word.
                for index in 0..PROBE_LIMIT {
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
}
