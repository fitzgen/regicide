use core::{fmt::Debug, hash::Hash, num::NonZero, ops::Sub};

mod map;
mod set;

pub use map::*;
pub use set::*;

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
        type NonZero: Sized + Copy + Debug + PartialEq + Eq + PartialOrd + Ord + Hash;

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
    sealed::NonZeroInt + Copy + Debug + PartialEq + Eq + PartialOrd + Ord + Hash
{
}

impl EntityRepr for u8 {}
impl EntityRepr for u16 {}
impl EntityRepr for u32 {}

/// TODO FITZGEN
pub trait Entity: Sized + Copy + Debug + PartialEq + Eq + PartialOrd + Ord + Hash {
    /// TODO FITZGEN
    type Repr: EntityRepr;

    /// TODO FITZGEN
    const MAX: Self;

    /// TODO FITZGEN
    fn try_new(index: usize) -> Option<Self>;

    /// TODO FITZGEN
    fn index(self) -> usize;

    #[doc(hidden)]
    type Family<E>: Entity
    where
        E: EntityRepr;

    #[doc(hidden)]
    fn with_repr32(self) -> Self::Family<u32> {
        self.with_repr::<u32>().unwrap()
    }

    #[doc(hidden)]
    fn with_repr<E>(self) -> Option<Self::Family<E>>
    where
        E: EntityRepr,
    {
        let index = self.index();
        <Self::Family<E> as Entity>::try_new(index)
    }
}

macro_rules! define_entities {
    ( $(
        $( #[$attr:meta] )*
        $vis:vis struct $name:ident = $fmt:expr;
    )* ) => {
        $(
            $( #[$attr] )*
            $vis struct $name<T = u32> ( T::NonZero )
            where
                T: EntityRepr;

            impl<T: EntityRepr> Default for $name<T> {
                fn default() -> Self {
                    Self::MAX
                }
            }

            impl<T: EntityRepr> core::fmt::Debug for $name<T> {
                fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    write!(f, "{}{}", $fmt, self.index())
                }
            }

            impl<T: EntityRepr> Entity for $name<T> {
                type Repr = T;

                type Family<E> = $name<E>
                where
                    E: EntityRepr;

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
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Val = "v";

    /// TODO FITZGEN
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Inst = "inst";

    /// TODO FITZGEN
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Block = "block";

    /// TODO FITZGEN
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Scc = "scc";

    /// TODO FITZGEN
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct SccBlockIndex = "scc_block_index";

    /// TODO FITZGEN
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Region = "region";

    /// TODO FITZGEN
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct RegionBlocksStorageIndex = "region_blocks_storage_index";

    /// TODO FITZGEN
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct RegionChildrenStorageIndex = "region_children_storage_index";

    /// TODO FITZGEN
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Reg = "r";

    /// TODO FITZGEN
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct SpillSlot = "spill_slot";

    /// TODO FITZGEN
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct LiveRange = "live_range";

    /// TODO FITZGEN
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Bundle = "bundle";
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct EntityRange<K: Entity> {
    pub start: K,
    pub end: K,
}

impl<K> Default for EntityRange<K>
where
    K: Entity,
{
    fn default() -> Self {
        Self::empty()
    }
}

impl<K> EntityRange<K>
where
    K: Entity,
{
    pub const fn empty() -> Self {
        Self {
            start: K::MAX,
            end: K::MAX,
        }
    }

    /// Is this range empty?
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// How many entities does this range cover?
    pub fn len(&self) -> usize {
        self.end.index() - self.start.index()
    }

    /// The `usize` indices that this range covers.
    ///
    /// Empty ranges give `0..0`, regardless of their actual `start` and `end`.
    pub fn indices(&self) -> core::ops::Range<usize> {
        if self.is_empty() {
            0..0
        } else {
            self.start.index()..self.end.index()
        }
    }
}
