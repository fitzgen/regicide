use super::Entity;
use crate::{
    error::{IResult, InternalError},
    output::OutputInner,
};
use alloc::vec::Vec;
use core::{
    fmt::Debug,
    marker::PhantomData,
    ops::{Index, IndexMut},
};

#[derive(Clone, Hash)]
#[cfg_attr(any(test, fuzz), derive(mutatis::Mutate))]
pub struct PrimaryMap<K, V> {
    elems: Vec<V>,
    _phantom: PhantomData<K>,
}

impl<K, V> Default for PrimaryMap<K, V> {
    fn default() -> Self {
        Self {
            elems: Vec::default(),
            _phantom: PhantomData,
        }
    }
}

impl<K, V> Debug for PrimaryMap<K, V>
where
    K: Debug + Entity,
    V: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("PrimaryMap ")?;
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V> PrimaryMap<K, V>
where
    K: Entity,
{
    /// Creates a new, empty [`PrimaryMap`].
    pub const fn new() -> Self {
        Self {
            elems: Vec::new(),
            _phantom: PhantomData,
        }
    }

    /// Resets the map to an empty state.
    pub fn reset(&mut self) {
        let Self { elems, _phantom } = self;
        elems.clear();
    }

    /// Returns `true` if the map is in a reset (empty) state.
    pub fn is_reset(&self) -> bool {
        let Self { elems, _phantom } = self;
        elems.is_empty()
    }

    /// Reserve space for at least `additional` more elements.
    pub fn reserve(&mut self, additional: usize) {
        self.elems.reserve(additional);
    }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        self.elems.len()
    }

    /// Returns `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.elems.is_empty()
    }

    /// Allocates the next key without inserting a value.
    pub(crate) fn next_key(&self, output: &mut OutputInner<K::Repr>) -> IResult<K> {
        let index = self.elems.len();
        match K::try_new(index) {
            Some(k) => Ok(k),
            None => output.error(InternalError::EntityReprTooSmall),
        }
    }

    /// Appends a value to the map, returning its entity key.
    pub(crate) fn push(&mut self, output: &mut OutputInner<K::Repr>, value: V) -> IResult<K> {
        let key = self.next_key(output)?;
        self.elems.push(value);
        Ok(key)
    }

    pub(crate) fn next_key_unwrap(&self) -> K {
        K::try_new(self.elems.len()).unwrap()
    }

    pub(crate) fn push_unwrap(&mut self, value: V) -> K {
        let key = self.next_key_unwrap();
        self.elems.push(value);
        key
    }

    /// Returns an iterator over the key-value pairs in the map.
    pub fn iter(&self) -> PrimaryMapIter<'_, K, V> {
        PrimaryMapIter {
            inner: self.elems.iter().enumerate(),
            _phantom: PhantomData,
        }
    }

    /// Returns a mutable iterator over the key-value pairs in the map.
    pub fn iter_mut(&mut self) -> PrimaryMapIterMut<'_, K, V> {
        PrimaryMapIterMut {
            inner: self.elems.iter_mut().enumerate(),
            _phantom: PhantomData,
        }
    }

    /// Returns an owning iterator of the key-value pairs in the map.
    pub fn into_iter(self) -> PrimaryMapIntoIter<K, V> {
        PrimaryMapIntoIter {
            inner: self.elems.into_iter().enumerate(),
            _phantom: PhantomData,
        }
    }

    /// Returns an iterator over the keys in the map.
    pub fn keys(&self) -> PrimaryMapKeys<K> {
        PrimaryMapKeys {
            pos: 0,
            len: self.elems.len(),
            _phantom: PhantomData,
        }
    }

    /// Returns an iterator over the values in the map.
    pub fn values(&self) -> core::slice::Iter<'_, V> {
        self.elems.iter()
    }

    /// Returns a mutable iterator over the values in the map.
    pub fn values_mut(&mut self) -> core::slice::IterMut<'_, V> {
        self.elems.iter_mut()
    }
}

/// An iterator over key-value pairs in a `PrimaryMap`.
pub struct PrimaryMapIter<'a, K, V> {
    inner: core::iter::Enumerate<core::slice::Iter<'a, V>>,
    _phantom: PhantomData<K>,
}

impl<'a, K, V> Iterator for PrimaryMapIter<'a, K, V>
where
    K: Entity,
{
    type Item = (K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let (idx, val) = self.inner.next()?;
        let key = K::try_new(idx).unwrap();
        Some((key, val))
    }
}

/// A mutable iterator over key-value pairs in a `PrimaryMap`.
pub struct PrimaryMapIterMut<'a, K, V> {
    inner: core::iter::Enumerate<core::slice::IterMut<'a, V>>,
    _phantom: PhantomData<K>,
}

impl<'a, K, V> Iterator for PrimaryMapIterMut<'a, K, V>
where
    K: Entity,
{
    type Item = (K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let (idx, val) = self.inner.next()?;
        let key = K::try_new(idx).unwrap();
        Some((key, val))
    }
}

/// A mutable iterator over key-value pairs in a `PrimaryMap`.
pub struct PrimaryMapIntoIter<K, V> {
    inner: core::iter::Enumerate<alloc::vec::IntoIter<V>>,
    _phantom: PhantomData<K>,
}

impl<K, V> Iterator for PrimaryMapIntoIter<K, V>
where
    K: Entity,
{
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let (idx, val) = self.inner.next()?;
        let key = K::try_new(idx).unwrap();
        Some((key, val))
    }
}

/// An iterator over the keys of a [`PrimaryMap`].
#[derive(Clone, Debug)]
pub struct PrimaryMapKeys<K> {
    pos: usize,
    len: usize,
    _phantom: PhantomData<fn() -> K>,
}

impl<K> Iterator for PrimaryMapKeys<K>
where
    K: Entity,
{
    type Item = K;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.len {
            let key = K::try_new(self.pos).unwrap();
            self.pos += 1;
            Some(key)
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.len - self.pos;
        (remaining, Some(remaining))
    }
}

impl<'a, K> ExactSizeIterator for PrimaryMapKeys<K> where K: Entity {}

impl<'a, K> DoubleEndedIterator for PrimaryMapKeys<K>
where
    K: Entity,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.pos < self.len {
            self.len -= 1;
            let key = K::try_new(self.len).unwrap();
            Some(key)
        } else {
            None
        }
    }
}

impl<K, V> Index<K> for PrimaryMap<K, V>
where
    K: Entity,
{
    type Output = V;

    fn index(&self, key: K) -> &Self::Output {
        let index = key.index();
        &self.elems[index]
    }
}

impl<K, V> IndexMut<K> for PrimaryMap<K, V>
where
    K: Entity,
{
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        let index = key.index();
        &mut self.elems[index]
    }
}

#[derive(Clone, Hash)]
pub(crate) struct SecondaryMap<K, V> {
    inner: PrimaryMap<K, V>,
    default_value: V,
}

impl<K, V> Debug for SecondaryMap<K, V>
where
    K: Entity + Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SecondaryMap")
            .field("inner", &self.inner)
            .field("default_value", &self.default_value)
            .finish()
    }
}

impl<K, V> SecondaryMap<K, V>
where
    K: Entity,
{
    pub const fn new(default_value: V) -> Self {
        Self {
            inner: PrimaryMap::new(),
            default_value,
        }
    }

    pub fn reset(&mut self) {
        let Self {
            inner,
            default_value: _,
        } = self;
        inner.reset();
    }

    pub fn is_reset(&self) -> bool {
        self.inner.is_reset()
    }

    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional);
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn get(&self, key: K) -> Option<&V> {
        let index = key.index();
        self.inner.elems.get(index)
    }

    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        let index = key.index();
        self.inner.elems.get_mut(index)
    }

    pub fn iter(&self) -> PrimaryMapIter<'_, K, V> {
        self.inner.iter()
    }

    pub fn into_iter(self) -> PrimaryMapIntoIter<K, V> {
        self.inner.into_iter()
    }
}

impl<K, V> Index<K> for SecondaryMap<K, V>
where
    K: Entity,
{
    type Output = V;

    fn index(&self, key: K) -> &Self::Output {
        if let Some(value) = self.get(key) {
            value
        } else {
            &self.default_value
        }
    }
}

impl<K, V> IndexMut<K> for SecondaryMap<K, V>
where
    K: Entity,
    V: Clone,
{
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        let index = key.index();
        while self.inner.elems.len() <= index {
            self.inner.elems.push(self.default_value.clone());
        }
        &mut self.inner[key]
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
    use std::{string::String, vec::Vec};

    #[test]
    fn primary_map_properties() -> CheckResult<Vec<u32>> {
        let mutator = m::default::<Vec<u32>>().map(|_ctx, vec| {
            vec.truncate(100);
            Ok(())
        });
        Check::new().run_with(
            mutator,
            [Vec::new()],
            |values: &Vec<u32>| -> Result<(), String> {
                let mut map = PrimaryMap::<Val, u32>::new();
                assert!(map.is_empty());
                assert_eq!(map.len(), 0);
                assert!(map.is_reset());

                for &v in values {
                    map.elems.push(v);
                }

                assert_eq!(map.len(), values.len());
                assert_eq!(map.is_empty(), values.is_empty());
                assert_eq!(map.is_reset(), values.is_empty());

                // Check keys, values, and indexing for `PrimaryMap`.
                let keys: Vec<Val> = map.keys().collect();
                assert_eq!(keys.len(), values.len());
                assert_eq!(map.keys().len(), values.len());

                for (i, &expected_val) in values.iter().enumerate() {
                    let key = Val::try_new(i).expect("valid key");
                    assert_eq!(keys[i], key);
                    assert_eq!(map[key], expected_val);
                }

                // Check `iter()` and `values()` iterators for `PrimaryMap`.
                let iter_items: Vec<(Val, &u32)> = map.iter().collect();
                assert_eq!(iter_items.len(), values.len());
                for (i, (key, val)) in iter_items.into_iter().enumerate() {
                    assert_eq!(key, Val::try_new(i).unwrap());
                    assert_eq!(*val, values[i]);
                }

                let collected_vals: Vec<&u32> = map.values().collect();
                assert_eq!(collected_vals.len(), values.len());
                for (i, val) in collected_vals.into_iter().enumerate() {
                    assert_eq!(*val, values[i]);
                }

                // Check `DoubleEndedIterator` implementation for `PrimaryMapKeys`.
                let rev_keys: Vec<Val> = map.keys().rev().collect();
                assert_eq!(rev_keys.len(), values.len());
                for (i, &key) in rev_keys.iter().enumerate() {
                    let expected_index = values.len() - 1 - i;
                    assert_eq!(key, Val::try_new(expected_index).unwrap());
                }

                // Test `reset()` method on `PrimaryMap`.
                map.reset();
                assert!(map.is_empty());
                assert_eq!(map.len(), 0);
                assert!(map.is_reset());

                Ok(())
            },
        )
    }

    #[test]
    fn primary_map_mutation_properties() -> CheckResult<(Vec<u32>, Vec<u32>)> {
        let mutator = m::default::<(Vec<u32>, Vec<u32>)>().map(|_ctx, (v1, v2)| {
            v1.truncate(50);
            v2.resize(v1.len(), 42);
            Ok(())
        });
        Check::new().run_with(
            mutator,
            [(Vec::new(), Vec::new())],
            |(initial, updates): &(Vec<u32>, Vec<u32>)| -> Result<(), String> {
                let mut map = PrimaryMap::<Val, u32>::new();
                for &v in initial {
                    map.elems.push(v);
                }

                // Mutate values via `IndexMut`.
                for (i, &new_val) in updates.iter().enumerate() {
                    let key = Val::try_new(i).unwrap();
                    map[key] = new_val;
                }

                // Verify updated values via `Index` and `values()`.
                for (i, &new_val) in updates.iter().enumerate() {
                    let key = Val::try_new(i).unwrap();
                    assert_eq!(map[key], new_val);
                }

                let current_vals: Vec<&u32> = map.values().collect();
                for (i, val) in current_vals.into_iter().enumerate() {
                    assert_eq!(*val, updates[i]);
                }

                // Mutate values via `values_mut()`.
                for val in map.values_mut() {
                    *val = val.wrapping_add(1);
                }

                for (i, &orig_new_val) in updates.iter().enumerate() {
                    let key = Val::try_new(i).unwrap();
                    assert_eq!(map[key], orig_new_val.wrapping_add(1));
                }

                Ok(())
            },
        )
    }

    #[test]
    fn secondary_map_properties() -> CheckResult<(u32, Vec<(u8, u32)>)> {
        let mutator = m::default::<(u32, Vec<(u8, u32)>)>().map(|_ctx, (_default_val, pairs)| {
            pairs.truncate(100);
            Ok(())
        });
        Check::new().run_with(
            mutator,
            [(0, Vec::new())],
            |(default_val, pairs): &(u32, Vec<(u8, u32)>)| -> Result<(), String> {
                let default_val = *default_val;
                let mut map = SecondaryMap::<Val, u32>::new(default_val);
                assert!(map.is_reset());

                // Before any mutation, all keys return `None` for `get` and
                // `default_val` for `Index`.
                for key_idx in 0..50 {
                    let key = Val::try_new(key_idx).unwrap();
                    assert_eq!(map.get(key), None);
                    assert_eq!(map[key], default_val);
                }

                // Track expected values in a `HashMap`.
                let mut expected = std::collections::HashMap::new();
                let mut max_idx: Option<usize> = None;

                for &(idx, val) in pairs {
                    let idx = idx as usize;
                    let key = Val::try_new(idx).unwrap();
                    map[key] = val;
                    expected.insert(idx, val);
                    max_idx = Some(max_idx.map_or(idx, |m| m.max(idx)));
                }

                // Check modified keys and implicit default-filled keys up to
                // `max_idx`.
                if let Some(max) = max_idx {
                    assert!(!map.is_reset());
                    for i in 0..=max {
                        let key = Val::try_new(i).unwrap();
                        let expected_val = expected.get(&i).copied().unwrap_or(default_val);
                        assert_eq!(map[key], expected_val);
                        assert_eq!(map.get(key), Some(&expected_val));
                    }
                }

                // Check keys beyond `max_idx`.
                let beyond_idx = max_idx.map_or(0, |m| m + 1);
                for i in beyond_idx..beyond_idx + 20 {
                    let key = Val::try_new(i).unwrap();
                    assert_eq!(map.get(key), None);
                    assert_eq!(map[key], default_val);
                }

                // Test `get_mut` method for mutation.
                for (&idx, &exp_val) in &expected {
                    let key = Val::try_new(idx).unwrap();
                    if let Some(mut_ref) = map.get_mut(key) {
                        *mut_ref = mut_ref.wrapping_add(10);
                    }
                    assert_eq!(map[key], exp_val.wrapping_add(10));
                }

                // Test `reset()` method on `SecondaryMap`.
                map.reset();
                assert!(map.is_reset());
                for key_idx in 0..50 {
                    let key = Val::try_new(key_idx).unwrap();
                    assert_eq!(map.get(key), None);
                    assert_eq!(map[key], default_val);
                }

                Ok(())
            },
        )
    }
}
