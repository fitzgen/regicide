use core::{fmt::Debug, hash::Hash, marker::PhantomData, num::NonZero, ops::Sub};

mod fixed_set;
mod map;
mod set;

pub use fixed_set::*;
pub use map::*;
pub use sealed::{NonZeroInt, WideInt};
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

    /// An unsigned integer used as the packed backing store for a bit-packed
    /// entity-derived value, such as a program point.
    ///
    /// Only exposes conversion to and from `usize`: everything bit-packed into
    /// one of these is built out of entity indices, which are already `usize`.
    pub trait WideInt: Sized + Copy + Debug + PartialEq + Eq + PartialOrd + Ord + Hash {
        /// How many bits wide this integer is.
        const BITS: u32;

        /// Convert from a `usize`, or `None` if it does not fit.
        fn try_from_usize(x: usize) -> Option<Self>;

        /// Convert from a `usize`.
        fn from_usize(x: usize) -> Self;

        /// Convert to a `usize`.
        fn to_usize(self) -> usize;
    }

    macro_rules! define_wide_ints {
        ( $( $t:ty ),* ) => {
            $(
                impl WideInt for $t {
                    const BITS: u32 = <$t>::BITS;

                    #[inline]
                    fn try_from_usize(x: usize) -> Option<Self> {
                        <$t>::try_from(x).ok()
                    }

                    #[inline]
                    #[allow(
                        clippy::cast_possible_truncation,
                        reason = "narrowing is intentional here; the `debug_assert!` catches it in \
                                  debug builds"
                    )]
                    fn from_usize(x: usize) -> Self {
                        debug_assert!(Self::try_from_usize(x).is_some());
                        x as $t
                    }

                    #[inline]
                    fn to_usize(self) -> usize {
                        <Self as TryInto<usize>>::try_into(self)
                            .map_err(|_| ())
                            .unwrap()
                    }
                }
            )*
        };
    }

    define_wide_ints! {
        u16, u32
    }
}

/// The underlying representation of an [`Entity`].
///
/// This is a sealed trait and cannot be implemented outside of this crate.
pub trait EntityRepr:
    sealed::NonZeroInt + Copy + Debug + PartialEq + Eq + PartialOrd + Ord + Hash
{
    /// An unsigned integer twice as wide as `Self`, maxing out at `u32`.
    #[doc(hidden)]
    type Wide: sealed::WideInt;
}

impl EntityRepr for u8 {
    type Wide = u16;
}

impl EntityRepr for u16 {
    type Wide = u32;
}

impl EntityRepr for u32 {
    type Wide = u32;
}

/// TODO FITZGEN
pub trait Entity: Sized + Copy + Debug + PartialEq + Eq + PartialOrd + Ord + Hash {
    /// TODO FITZGEN
    type Repr: EntityRepr;

    /// TODO FITZGEN
    fn try_new(index: usize) -> Option<Self>;

    /// TODO FITZGEN
    fn index(self) -> usize;

    /// TODO FITZGEN
    fn from_bits(bits: <Self::Repr as sealed::NonZeroInt>::NonZero) -> Self;

    /// TODO FITZGEN
    fn to_bits(self) -> <Self::Repr as sealed::NonZeroInt>::NonZero;

    #[doc(hidden)]
    const MAX_REPRESENTABLE: Self;

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
                T: crate::entity::EntityRepr;

            impl<T: crate::entity::EntityRepr> Default for $name<T> {
                fn default() -> Self {
                    use crate::entity::Entity;
                    Self::MAX_REPRESENTABLE
                }
            }

            impl<T: crate::entity::EntityRepr> core::fmt::Debug for $name<T> {
                fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    use crate::entity::Entity;
                    write!(f, "{}{}", $fmt, self.index())
                }
            }

            impl<T: crate::entity::EntityRepr> crate::entity::Entity for $name<T> {
                type Repr = T;

                type Family<E> = $name<E>
                where
                    E: crate::entity::EntityRepr;

                const MAX_REPRESENTABLE: Self = $name(T::MAX);

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

                #[inline]
                fn from_bits(bits: <Self::Repr as crate::entity::NonZeroInt>::NonZero) -> Self {
                    Self(bits)
                }

                #[inline]
                fn to_bits(self) -> <Self::Repr as crate::entity::NonZeroInt>::NonZero {
                    self.0
                }
            }
        )*
    };
}

/// Like `define_entities` but for fixed-size entities that are not
/// parameterized on `E: EntityRepr`.
macro_rules! define_fixed_size_entities {
    ( $(
        $( #[$attr:meta] )*
        $vis:vis struct $name:ident : $repr:ty = $fmt:expr;
    )* ) => {
        $(
            $( #[$attr] )*
            $vis struct $name ( core::num::NonZero<$repr> );

            const _: () = assert!(
                $name::MAX <= <$repr>::MAX as usize,
                concat!(
                    stringify!($name),
                    " must have a representation wide enough for every index below its MAX",
                ),
            );

            impl Default for $name {
                fn default() -> Self {
                    use crate::entity::Entity;
                    Self::MAX_REPRESENTABLE
                }
            }

            impl core::fmt::Debug for $name {
                fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    use crate::entity::Entity;
                    write!(f, "{}{}", $fmt, self.index())
                }
            }

            impl crate::entity::Entity for $name {
                type Repr = $repr;

                type Family<E> = Self
                where
                    E: crate::entity::EntityRepr;

                const MAX_REPRESENTABLE: Self =
                    $name(match core::num::NonZero::<$repr>::new(<$repr>::MAX) {
                        Some(x) => x,
                        None => unreachable!(),
                    });

                #[inline]
                fn try_new(index: usize) -> Option<Self> {
                    let inner = <$repr>::try_from(index.checked_add(1)?).ok()?;
                    let non_zero = core::num::NonZero::<$repr>::new(inner)?;
                    Some(Self(non_zero))
                }

                #[inline]
                fn index(self) -> usize {
                    usize::try_from(self.0.get() - 1).unwrap()
                }

                #[inline]
                fn from_bits(bits: <Self::Repr as crate::entity::NonZeroInt>::NonZero) -> Self {
                    Self(bits)
                }

                #[inline]
                fn to_bits(self) -> <Self::Repr as crate::entity::NonZeroInt>::NonZero {
                    self.0
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
    pub struct SpillSlot = "spill_slot";
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
            start: K::MAX_REPRESENTABLE,
            end: K::MAX_REPRESENTABLE,
        }
    }

    /// Is this range empty?
    pub fn is_empty(&self) -> bool {
        self.start == self.end
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

impl<K> IntoIterator for EntityRange<K>
where
    K: Entity,
{
    type Item = K;

    type IntoIter = EntityRangeIter<K>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        EntityRangeIter {
            indices: self.indices(),
            _phantom: PhantomData,
        }
    }
}

/// An iterator over a range of `K` entities.
#[derive(Clone, Debug)]
pub struct EntityRangeIter<K> {
    indices: core::ops::Range<usize>,
    _phantom: PhantomData<K>,
}

impl<K> Iterator for EntityRangeIter<K>
where
    K: Entity,
{
    type Item = K;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.indices.next().map(|i| K::try_new(i).unwrap())
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.indices.size_hint()
    }
}

impl<K> DoubleEndedIterator for EntityRangeIter<K>
where
    K: Entity,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.indices.next_back().map(|i| K::try_new(i).unwrap())
    }
}

impl<K> ExactSizeIterator for EntityRangeIter<K>
where
    K: Entity,
{
    #[inline]
    fn len(&self) -> usize {
        self.indices.len()
    }
}

#[cfg(test)]
mod tests {
    use crate::{RegClass, RegUnit, entity::Entity};
    use core::mem;

    /// The point of a fixed-repr entity is that it does not pay for indices it
    /// can never hold.
    #[test]
    fn fixed_entities_are_as_small_as_they_claim() {
        assert_eq!(mem::size_of::<RegClass>(), 1);
        assert_eq!(mem::size_of::<RegUnit>(), 2);

        // Being a `NonZero` inside is what makes the niche available, which is
        // what keeps `Machine`'s intersection table one byte per entry.
        assert_eq!(mem::size_of::<Option<RegClass>>(), 1);
        assert_eq!(mem::size_of::<Option<RegUnit>>(), 2);
    }

    /// Indices are one-based inside and zero-based outside, at both ends of the
    /// range, and the entity refuses an index it cannot represent.
    #[test]
    fn fixed_entities_round_trip() {
        for i in [
            0,
            1,
            2,
            RegClass::MAX_INCLUDING_DERIVED - 1,
            RegClass::MAX_REPRESENTABLE.index(),
        ] {
            assert_eq!(RegClass::try_new(i).unwrap().index(), i);
        }

        assert!(RegClass::try_new(RegClass::MAX_REPRESENTABLE.index() + 1).is_none());
        assert!(RegClass::try_new(usize::MAX).is_none());

        // `Family<E> = Self` for a fixed entity, so the repr conversions that
        // `run` performs on the generic entities are the identity here.
        let class = RegClass::try_new(7).unwrap();
        assert_eq!(class.with_repr::<u8>(), Some(class));
        assert_eq!(class.with_repr::<u16>(), Some(class));
        assert_eq!(class.with_repr::<u32>(), Some(class));
    }
}
