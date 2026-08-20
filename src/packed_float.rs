//! A lossy, order-preserving packing of positive `f32`s into fewer bits.

use core::{fmt::Debug, hash::Hash};

pub use sealed::Storage;
mod sealed {
    use super::*;

    pub trait Storage: Sized + Copy + Debug + PartialEq + Eq + PartialOrd + Ord + Hash {
        /// How many bits wide this integer is.
        const BITS: u32;
    }
}

/// A positive `f32`, truncated to its most significant `BITS` bits and stored in
/// a `T`.
///
/// An `f32` is `[sign: 1, exponent: 8, mantissa: 23]`. The sign is always clear
/// for the quantities packed this way, so dropping it leaves 31 bits, of which
/// we keep the top `BITS` and truncate the rest. At `BITS = 16` that is the same
/// shape as a `bfloat16`, except with an extra bit of mantissa in place of the
/// sign.
///
/// Truncation only ever rounds *towards zero*, so an unpacked value is never
/// larger than the value it was packed from. Because the exponent sits
/// immediately below the discarded sign, the packed bits of two values compare
/// in the same order as the values themselves; that is what the derived `Ord`
/// below relies on, and it is the main reason to keep the high bits rather than
/// round to nearest.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PackedPositiveFloat<T, const BITS: u32>
where
    T: Storage,
{
    bits: T,
}

impl<T, const BITS: u32> PackedPositiveFloat<T, BITS>
where
    T: Storage,
{
    const SHIFT: u32 = (f32::MANTISSA_DIGITS - 1) + u8::BITS - BITS;
    const MASK_AS_U32: u32 = u32::MAX >> (u32::BITS - BITS);

    /// Every constructor mentions this, so an out-of-range `BITS` is a compile
    /// error rather than a shift that quietly misbehaves.
    const VALID_BITS: () = {
        assert!(
            BITS >= 1 && BITS <= 31,
            "an `f32` has 31 bits below its sign, and a packed value must \
             occupy at least one of them",
        );
        assert!(
            BITS <= T::BITS,
            "the storage must be at least as wide as the packed field",
        );
    };
}

macro_rules! define_storages {
    ( $( $t:ty ),* ) => {
        $(
            impl Storage for $t {
                const BITS: u32 = <$t>::BITS;
            }

            impl<const BITS: u32> core::fmt::Debug for PackedPositiveFloat<$t, BITS> {
                fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    core::fmt::Debug::fmt(&self.as_f32(), f)
                }
            }

            #[allow(dead_code, reason = "macro-generated")]
            impl<const BITS: u32> PackedPositiveFloat<$t, BITS> {
                #[allow(trivial_numeric_casts, reason = "macro-generated")]
                pub const MASK: $t = Self::MASK_AS_U32 as $t;

                /// Pack `value`.
                ///
                /// Infinity survives, since the exponent is kept whole. `NaN`
                /// also survives as *some* `NaN`, since the exponent is all ones
                /// either way, but which one is not preserved.
                #[inline]
                pub const fn new(value: f32) -> Self {
                    let () = Self::VALID_BITS;
                    debug_assert!(
                        value.is_sign_positive(),
                        "the sign bit is not stored, so it must be clear",
                    );

                    let bits = (value.to_bits() >> Self::SHIFT) & Self::MASK_AS_U32;

                    #[allow(trivial_numeric_casts, reason = "macro-generated")]
                    let bits = bits as $t;

                    PackedPositiveFloat { bits }
                }

                #[inline]
                pub const fn from_bits(bits: $t) -> Self {
                    let () = Self::VALID_BITS;
                    debug_assert!(
                        bits & !Self::MASK == 0,
                        "bits above the packed field must be clear",
                    );
                    PackedPositiveFloat { bits }
                }

                /// Unpack this value, with the truncated low mantissa bits
                /// restored as zeroes.
                #[inline]
                pub const fn as_f32(self) -> f32 {
                    #[allow(trivial_numeric_casts, reason = "macro-generated")]
                    let bits = self.bits as u32;
                    f32::from_bits(bits << Self::SHIFT)
                }

                /// This value's packed bits, which occupy only the low `BITS` of
                /// the result.
                ///
                /// These compare in the same order as the values they encode, so
                /// they may stand in for the value wherever only the ordering
                /// matters, including as one field of a wider bitfield.
                #[inline]
                pub const fn bits(self) -> $t {
                    self.bits
                }
            }
        )*
    };
}

define_storages! {
    u16, u32
}

#[cfg(test)]
mod tests {
    use super::*;

    type Packed = PackedPositiveFloat<u16, 16>;

    #[test]
    fn round_trips_approximately() {
        for value in [0.0f32, 1e-20, 0.5, 1.0, 3.25, 123.456, 1e20] {
            let unpacked = Packed::new(value).as_f32();
            // Truncating the low mantissa bits only ever rounds towards zero,
            // and 16 bits keeps 8 bits of mantissa.
            assert!(unpacked <= value, "{unpacked} <= {value}");
            assert!(
                unpacked >= value * (1.0 - 1.0 / 256.0),
                "{unpacked} >= {value} * (1 - 1/256)"
            );
        }

        // Infinity survives, since the exponent is kept whole.
        assert_eq!(Packed::new(f32::INFINITY).as_f32(), f32::INFINITY);
    }

    /// Check the properties that must hold at *every* width, for one storage and
    /// width pair.
    ///
    /// A macro rather than a generic function because the conversions are
    /// `const fn`s in one inherent `impl` per storage type, which a function
    /// generic over the storage cannot call, for the same reason they cannot be
    /// trait methods in the first place.
    macro_rules! check_at_width {
        ( $( ($t:ty, $bits:expr) ),* $(,)? ) => {
            $({
                type P = PackedPositiveFloat<$t, $bits>;

                // Keeping `BITS` bits below the sign leaves exactly the sign bit
                // above them, and the mask covers exactly those bits.
                assert_eq!(P::SHIFT + $bits + 1, u32::BITS, "at {} bits", $bits);
                assert_eq!(P::MASK.count_ones(), $bits, "at {} bits", $bits);

                let mut previous = None;
                for value in [0.0f32, 1e-20, 0.5, 1.0, 2.0, 1000.0, 1e20, f32::INFINITY] {
                    let packed = P::new(value);

                    // Packed bits compare in the same order as the values they
                    // encode, which is what everything holding one relies on.
                    if let Some(previous) = previous {
                        assert!(
                            packed > previous,
                            "{packed:?} > {previous:?} for {value} at {} bits",
                            $bits,
                        );
                    }
                    previous = Some(packed);

                    // Unpacking only ever rounds towards zero.
                    assert!(packed.as_f32() <= value, "{packed:?} <= {value}");

                    // The bits stay inside the field -- in particular, a storage
                    // wider than its field must not smuggle the sign bit in --
                    // and survive a trip out to a bitfield and back.
                    assert_eq!(packed.bits() & !P::MASK, 0, "at {} bits", $bits);
                    assert_eq!(P::from_bits(packed.bits()), packed, "at {} bits", $bits);
                }
            })*
        };
    }

    #[test]
    fn packing_properties_hold_at_every_width() {
        check_at_width! {
            // The narrowest width that still keeps the whole exponent, and the
            // widest width there is.
            (u16, 9),
            (u32, 31),
            // The two widths the crate actually uses.
            (u16, 16),
            (u32, 29),
            // A storage wider than the field it holds.
            (u32, 16),
        }
    }

    /// A packing is no wider than the storage it asks for, which is the whole
    /// point of the storage being a parameter: some of these live in per-value
    /// and per-operand arrays.
    #[test]
    fn a_packing_is_as_wide_as_its_storage() {
        assert_eq!(size_of::<PackedPositiveFloat<u16, 9>>(), 2);
        assert_eq!(size_of::<PackedPositiveFloat<u16, 16>>(), 2);
        assert_eq!(size_of::<PackedPositiveFloat<u32, 29>>(), 4);
    }
}
