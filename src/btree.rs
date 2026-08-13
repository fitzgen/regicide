use core::{borrow::Borrow, marker::PhantomData};

type Inner<T> = alloc::collections::BTreeSet<T>;

pub struct BTreeSetArena<E, T> {
    _phantom: PhantomData<fn(E) -> T>,
}

impl<E, T> BTreeSetArena<E, T> {
    pub const fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }

    pub fn reset(&mut self) {
        let Self { _phantom } = self;
    }

    pub fn is_reset(&self) -> bool {
        true
    }
}

pub struct BTreeSet<E, T> {
    // TODO: replace with arena-based btree
    inner: Inner<T>,
    _phantom: PhantomData<fn(BTreeSetArena<E, T>)>,
}

// Written out rather than derived, so that it does not demand `E: Clone` from
// what is only ever a marker.
impl<E, T> Clone for BTreeSet<E, T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            _phantom: PhantomData,
        }
    }
}

impl<E, T> BTreeSet<E, T> {
    pub const fn new() -> Self {
        Self {
            inner: Inner::new(),
            _phantom: PhantomData,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn clear(&mut self, arena: &mut BTreeSetArena<E, T>) {
        let _ = arena;
        self.inner.clear();
    }

    /// Iterate over this set's elements in ascending order.
    pub fn iter(&self, arena: &BTreeSetArena<E, T>) -> impl Iterator<Item = &T> {
        let _ = arena;
        self.inner.iter()
    }

    /// Add every element of `other` to this set, returning whether that added
    /// anything that was not already here.
    pub fn union_with(&mut self, arena: &mut BTreeSetArena<E, T>, other: &Self) -> bool
    where
        T: Clone + Ord,
    {
        let _ = arena;
        let mut changed = false;
        for value in other.inner.iter() {
            changed |= self.inner.insert(value.clone());
        }
        changed
    }

    pub fn contains<Q>(&self, arena: &BTreeSetArena<E, T>, value: &Q) -> bool
    where
        T: Borrow<Q> + Ord,
        Q: Ord,
        Q: ?Sized,
    {
        let _ = arena;
        self.inner.contains(value)
    }

    pub fn get<Q>(&self, arena: &BTreeSetArena<E, T>, value: &Q) -> Option<&T>
    where
        T: Borrow<Q> + Ord,
        Q: Ord,
        Q: ?Sized,
    {
        let _ = arena;
        self.inner.get(value)
    }

    pub fn insert(&mut self, arena: &mut BTreeSetArena<E, T>, value: T) -> bool
    where
        T: Ord,
    {
        let _ = arena;
        self.inner.insert(value)
    }

    pub fn remove<Q: ?Sized>(&mut self, arena: &mut BTreeSetArena<E, T>, value: &Q) -> bool
    where
        T: Borrow<Q> + Ord,
        Q: Ord,
    {
        let _ = arena;
        self.inner.remove(value)
    }
}
