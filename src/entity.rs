use core::{
    fmt::Debug,
    marker::PhantomData,
    num::NonZero,
    ops::{Index, IndexMut, Sub},
};

use alloc::vec::Vec;

use crate::{
    error::{IResult, InternalError},
    output::OutputInner,
};

mod sealed {
    use super::*;

    pub trait One {
        fn one() -> Self;
    }

    pub trait CheckedAdd: Sized {
        fn checked_add(self, rhs: Self) -> Option<Self>;
    }

    pub trait NonZeroIntInner:
        One + CheckedAdd + Sub<Output = Self> + TryFrom<usize> + TryInto<usize>
    {
    }

    pub trait NonZeroInt: sealed::NonZeroIntInner {
        type NonZero: Sized + Copy + Debug + PartialEq + Eq + PartialOrd + Ord;

        const MAX: Self::NonZero;

        fn new(inner: Self) -> Option<Self::NonZero>;

        fn get(non_zero: Self::NonZero) -> Self;
    }

    macro_rules! define_non_zero_ints {
        ( $( $t:ty ),* ) => {
            $(
                impl One for $t {
                    #[inline]
                    fn one() -> Self {
                        1
                    }
                }

                impl CheckedAdd for $t {
                    #[inline]
                    fn checked_add(self, rhs: Self) -> Option<Self> {
                        <$t>::checked_add(self, rhs)
                    }
                }

                impl NonZeroIntInner for $t {}

                impl NonZeroInt for $t {
                    type NonZero = NonZero<Self>;

                    const MAX: Self::NonZero = Self::NonZero::new(<$t>::MAX).unwrap();

                    #[inline]
                    fn new(inner: Self) -> Option<Self::NonZero> {
                        Self::NonZero::new(inner)
                    }

                    #[inline]
                    fn get(non_zero: Self::NonZero) -> Self {
                        non_zero.get()
                    }
                }
            )*
        };
    }

    define_non_zero_ints! {
        u8, u16, u32
    }
}

/// TODO FITZGEN
pub trait EntityRepr:
    sealed::NonZeroInt + Copy + Debug + PartialEq + Eq + PartialOrd + Ord
{
}

impl EntityRepr for u8 {}
impl EntityRepr for u16 {}
impl EntityRepr for u32 {}

/// TODO FITZGEN
pub trait Entity: Sized + Copy + Debug + PartialEq + Eq + PartialOrd + Ord {
    /// TODO FITZGEN
    type Repr: EntityRepr;

    /// TODO FITZGEN
    const MAX: Self;

    /// TODO FITZGEN
    fn try_new(index: usize) -> Option<Self>;

    /// TODO FITZGEN
    fn index(self) -> usize;
}

macro_rules! define_entities {
    ( $(
        $( #[$attr:meta] )*
        $vis:vis struct $name:ident ;
    )* ) => {
        $(
            $( #[$attr] )*
            $vis struct $name<T = u32> ( T::NonZero )
            where
                T: EntityRepr;

            impl<T: EntityRepr> Entity for $name<T> {
                type Repr = T;

                const MAX: Self = $name(T::MAX);

                #[inline]
                fn try_new(index: usize) -> Option<Self> {
                    let inner = T::try_from(index.checked_add(1)?).ok()?;
                    let non_zero = T::new(inner)?;
                    Some(Self(non_zero))
                }

                #[inline]
                fn index(self) -> usize {
                    let index = T::get(self.0) - T::one();
                    <T as TryInto<usize>>::try_into(index).map_err(|_| ()).unwrap()
                }
            }
        )*
    };
}

define_entities! {
    /// TODO FITZGEN
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Val;

    /// TODO FITZGEN
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Inst;

    /// TODO FITZGEN
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Block;

    /// TODO FITZGEN
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Scc;

    /// TODO FITZGEN
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Region;

    /// TODO FITZGEN
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Reg;

    /// TODO FITZGEN
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct SpillSlot;

    /// TODO FITZGEN
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct LiveRange;

    /// TODO FITZGEN
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Bundle;

    /// TODO FITZGEN
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Allocation;
}

/// TODO FITZGEN
pub(crate) struct PrimaryMap<K, V> {
    elems: Vec<V>,
    _phantom: PhantomData<K>,
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
    pub const fn new() -> Self {
        Self {
            elems: Vec::new(),
            _phantom: PhantomData,
        }
    }

    pub fn reset(&mut self) {
        let Self { elems, _phantom } = self;
        elems.clear();
    }

    pub fn is_reset(&self) -> bool {
        let Self { elems, _phantom } = self;
        elems.is_empty()
    }

    pub fn next_key(&self, output: &mut OutputInner<K::Repr>) -> IResult<K> {
        let index = self.elems.len();
        match K::try_new(index) {
            Some(k) => Ok(k),
            None => output.error(InternalError::EntityReprTooSmall),
        }
    }

    pub fn push(&mut self, output: &mut OutputInner<K::Repr>, value: V) -> IResult<K> {
        let key = self.next_key(output)?;
        self.elems.push(value);
        Ok(key)
    }

    pub fn iter(&self) -> PrimaryMapIter<'_, K, V> {
        PrimaryMapIter {
            inner: self.elems.iter().enumerate(),
            _phantom: PhantomData,
        }
    }
}

/// TODO FITZGEN
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

    pub fn get(&self, key: K) -> Option<&V> {
        let index = key.index();
        self.inner.elems.get(index)
    }

    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        let index = key.index();
        self.inner.elems.get_mut(index)
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
