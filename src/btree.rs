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
