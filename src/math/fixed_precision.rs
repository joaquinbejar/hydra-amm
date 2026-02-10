//! Fixed-point implementation of the [`Precision`] trait.
//!
//! This module is only available when the `fixed-point` Cargo feature is
//! enabled.  It provides [`FixedPointArithmetic`], a newtype over
//! [`I80F48`](fixed::types::I80F48) that implements [`Precision`] using
//! deterministic fixed-point arithmetic from the [`fixed`] crate.
//!
//! # Precision characteristics
//!
//! | Aspect | Value |
//! |--------|-------|
//! | Integer bits | 80 (signed) |
//! | Fractional bits | 48 |
//! | Precision | 2^−48 ≈ 3.55 × 10⁻¹⁵ |
//! | Range | ±2^79 |
//! | Determinism | 100 % bit-for-bit |
//!
//! # When to use
//!
//! Use `FixedPointArithmetic` for on-chain deployments (Solana BPF, WASM)
//! where determinism and auditability are critical.

use core::fmt;

use fixed::types::I80F48;

use crate::domain::Rounding;
use crate::error::AmmError;

use super::Precision;

/// `I80F48`-backed precision type for on-chain computation.
///
/// All checked arithmetic methods return [`Err`] on overflow, underflow,
/// or division by zero.  Conversions are infallible but may saturate or
/// truncate for values outside the representable range.
///
/// # Examples
///
/// ```
/// use fixed::types::I80F48;
/// use hydra_amm::math::{FixedPointArithmetic, Precision};
///
/// let a = FixedPointArithmetic::new(I80F48::from_num(10));
/// let b = FixedPointArithmetic::new(I80F48::from_num(3));
/// let sum = a.checked_add(&b);
/// assert!(sum.is_ok());
/// ```
///
/// [`I80F48`]: fixed::types::I80F48
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FixedPointArithmetic(I80F48);

impl FixedPointArithmetic {
    /// Creates a new `FixedPointArithmetic` from a raw [`I80F48`].
    #[inline]
    #[must_use]
    pub const fn new(value: I80F48) -> Self {
        Self(value)
    }

    /// Returns the underlying [`I80F48`] value.
    #[inline]
    #[must_use]
    pub const fn get(&self) -> I80F48 {
        self.0
    }
}

impl From<I80F48> for FixedPointArithmetic {
    #[inline]
    fn from(value: I80F48) -> Self {
        Self(value)
    }
}

impl fmt::Display for FixedPointArithmetic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Precision for FixedPointArithmetic {
    #[inline]
    fn zero() -> Self {
        Self(I80F48::ZERO)
    }

    #[inline]
    fn one() -> Self {
        Self(I80F48::ONE)
    }

    // -- Conversions --------------------------------------------------------

    /// Converts `u128` to `I80F48` by first truncating to `u64`.
    ///
    /// `I80F48` has 80 integer bits (signed), so all `u64` values fit.
    /// Values above `u64::MAX` are truncated to the lower 64 bits.
    #[inline]
    fn from_u128(value: u128) -> Self {
        #[allow(clippy::cast_possible_truncation)]
        let truncated = value as u64;
        Self(I80F48::from_num(truncated))
    }

    /// Extracts the integer part as `u128`.
    ///
    /// Negative values are clamped to `0`.  The fractional part is
    /// discarded (truncated toward zero).
    #[inline]
    fn to_u128(&self) -> u128 {
        if self.0 < I80F48::ZERO {
            return 0;
        }
        // I80F48 integer range fits in u128
        self.0.to_num::<u128>()
    }

    /// Converts `f64` to `I80F48` using saturating conversion.
    ///
    /// Values outside the `I80F48` representable range are clamped to
    /// `I80F48::MIN` or `I80F48::MAX`.
    #[inline]
    fn from_f64(value: f64) -> Self {
        Self(I80F48::saturating_from_num(value))
    }

    /// Converts `I80F48` to `f64`.
    ///
    /// Precision may be lost because `f64` has fewer significant bits
    /// than `I80F48` for large integer values.
    #[inline]
    fn to_f64_lossy(&self) -> f64 {
        self.0.to_num::<f64>()
    }

    // -- Checked arithmetic -------------------------------------------------

    fn checked_add(&self, other: &Self) -> Result<Self, AmmError> {
        self.0
            .checked_add(other.0)
            .map(Self)
            .ok_or(AmmError::Overflow("fixed-point addition overflow"))
    }

    fn checked_sub(&self, other: &Self) -> Result<Self, AmmError> {
        self.0
            .checked_sub(other.0)
            .map(Self)
            .ok_or(AmmError::Underflow("fixed-point subtraction underflow"))
    }

    fn checked_mul(&self, other: &Self) -> Result<Self, AmmError> {
        self.0
            .checked_mul(other.0)
            .map(Self)
            .ok_or(AmmError::Overflow("fixed-point multiplication overflow"))
    }

    /// Divides with explicit rounding direction.
    ///
    /// - [`Rounding::Down`] — truncates toward zero (default `I80F48`
    ///   behaviour).
    /// - [`Rounding::Up`] — adds one ULP (unit in the last place) when
    ///   truncation discards a non-zero remainder.
    fn checked_div(&self, other: &Self, rounding: Rounding) -> Result<Self, AmmError> {
        if other.0 == I80F48::ZERO {
            return Err(AmmError::DivisionByZero);
        }

        let quotient = self
            .0
            .checked_div(other.0)
            .ok_or(AmmError::Overflow("fixed-point division overflow"))?;

        match rounding {
            Rounding::Down => Ok(Self(quotient)),
            Rounding::Up => {
                // Detect remainder: if quotient * other != self, round up
                let product = quotient
                    .checked_mul(other.0)
                    .ok_or(AmmError::Overflow("fixed-point division rounding overflow"))?;
                if product != self.0 {
                    let ulp = I80F48::from_bits(1);
                    let adjusted = quotient
                        .checked_add(ulp)
                        .ok_or(AmmError::Overflow("fixed-point division rounding overflow"))?;
                    Ok(Self(adjusted))
                } else {
                    Ok(Self(quotient))
                }
            }
        }
    }

    // -- Comparison helpers -------------------------------------------------

    #[inline]
    fn min(&self, other: &Self) -> Self {
        if self.0 <= other.0 { *self } else { *other }
    }

    #[inline]
    fn max(&self, other: &Self) -> Self {
        if self.0 >= other.0 { *self } else { *other }
    }

    #[inline]
    fn abs(&self) -> Self {
        Self(self.0.abs())
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0 == I80F48::ZERO
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;

    type FP = FixedPointArithmetic;

    fn fp(v: i64) -> FP {
        FP::new(I80F48::from_num(v))
    }

    fn fp_f(v: f64) -> FP {
        FP::new(I80F48::from_num(v))
    }

    // -- Identity -----------------------------------------------------------

    #[test]
    fn zero_is_zero() {
        assert!(FP::zero().is_zero());
        assert_eq!(FP::zero().to_u128(), 0);
    }

    #[test]
    fn one_is_one() {
        assert!(!FP::one().is_zero());
        assert_eq!(FP::one().to_u128(), 1);
    }

    // -- Conversions --------------------------------------------------------

    #[test]
    fn from_u128_small() {
        let v = FP::from_u128(42);
        assert_eq!(v.to_u128(), 42);
    }

    #[test]
    fn from_u128_large_truncates() {
        // u128::MAX is truncated to u64::MAX then converted
        let v = FP::from_u128(u128::MAX);
        assert_eq!(v.to_u128(), u64::MAX as u128);
    }

    #[test]
    fn to_u128_truncates_fractional() {
        let v = fp_f(3.9);
        assert_eq!(v.to_u128(), 3);
    }

    #[test]
    fn to_u128_negative_clamps() {
        let v = fp(-5);
        assert_eq!(v.to_u128(), 0);
    }

    #[test]
    fn from_f64_roundtrip() {
        let v = FP::from_f64(core::f64::consts::PI);
        let back = v.to_f64_lossy();
        assert!((back - core::f64::consts::PI).abs() < 1e-10);
    }

    #[test]
    fn from_f64_saturates_large() {
        let v = FP::from_f64(f64::MAX);
        // Should not panic — saturates to I80F48::MAX
        assert!(v.to_f64_lossy() > 0.0);
    }

    // -- Checked add --------------------------------------------------------

    #[test]
    fn checked_add_normal() {
        let Ok(r) = fp(10).checked_add(&fp(20)) else {
            panic!("expected Ok");
        };
        assert_eq!(r.to_u128(), 30);
    }

    #[test]
    fn checked_add_overflow() {
        let big = FP::new(I80F48::MAX);
        assert!(big.checked_add(&FP::one()).is_err());
    }

    // -- Checked sub --------------------------------------------------------

    #[test]
    fn checked_sub_normal() {
        let Ok(r) = fp(20).checked_sub(&fp(7)) else {
            panic!("expected Ok");
        };
        assert_eq!(r.to_u128(), 13);
    }

    #[test]
    fn checked_sub_negative_result() {
        let Ok(r) = fp(3).checked_sub(&fp(5)) else {
            panic!("expected Ok");
        };
        assert!((r.to_f64_lossy() - (-2.0)).abs() < f64::EPSILON);
    }

    #[test]
    fn checked_sub_underflow() {
        let min = FP::new(I80F48::MIN);
        assert!(min.checked_sub(&FP::one()).is_err());
    }

    // -- Checked mul --------------------------------------------------------

    #[test]
    fn checked_mul_normal() {
        let Ok(r) = fp(6).checked_mul(&fp(7)) else {
            panic!("expected Ok");
        };
        assert_eq!(r.to_u128(), 42);
    }

    #[test]
    fn checked_mul_zero() {
        let Ok(r) = FP::zero().checked_mul(&fp(1_000_000)) else {
            panic!("expected Ok");
        };
        assert!(r.is_zero());
    }

    #[test]
    fn checked_mul_overflow() {
        let big = FP::new(I80F48::MAX);
        assert!(big.checked_mul(&fp(2)).is_err());
    }

    // -- Checked div --------------------------------------------------------

    #[test]
    fn checked_div_exact() {
        let Ok(r) = fp(10).checked_div(&fp(2), Rounding::Down) else {
            panic!("expected Ok");
        };
        assert_eq!(r.to_u128(), 5);
    }

    #[test]
    fn checked_div_round_down() {
        let Ok(r) = fp(10).checked_div(&fp(3), Rounding::Down) else {
            panic!("expected Ok");
        };
        // 10 / 3 = 3.333..., truncated
        assert_eq!(r.to_u128(), 3);
        assert!(r.to_f64_lossy() < 10.0 / 3.0 + 1e-14);
    }

    #[test]
    fn checked_div_round_up_with_remainder() {
        let Ok(r) = fp(10).checked_div(&fp(3), Rounding::Up) else {
            panic!("expected Ok");
        };
        // Should be strictly greater than the Down result
        let Ok(r_down) = fp(10).checked_div(&fp(3), Rounding::Down) else {
            panic!("expected Ok");
        };
        assert!(r > r_down);
    }

    #[test]
    fn checked_div_round_up_exact_no_adjustment() {
        let Ok(r_down) = fp(10).checked_div(&fp(2), Rounding::Down) else {
            panic!("expected Ok");
        };
        let Ok(r_up) = fp(10).checked_div(&fp(2), Rounding::Up) else {
            panic!("expected Ok");
        };
        // Exact division — Up and Down should be equal
        assert_eq!(r_down, r_up);
    }

    #[test]
    fn checked_div_by_zero() {
        assert!(fp(1).checked_div(&FP::zero(), Rounding::Down).is_err());
    }

    // -- Min / Max / Abs ----------------------------------------------------

    #[test]
    fn min_returns_smaller() {
        assert_eq!(Precision::min(&fp(1), &fp(2)), fp(1));
    }

    #[test]
    fn max_returns_larger() {
        assert_eq!(Precision::max(&fp(1), &fp(2)), fp(2));
    }

    #[test]
    fn abs_positive() {
        assert_eq!(fp(3).abs(), fp(3));
    }

    #[test]
    fn abs_negative() {
        assert_eq!(fp(-3).abs(), fp(3));
    }

    #[test]
    fn abs_zero() {
        assert!(FP::zero().abs().is_zero());
    }

    // -- is_zero ------------------------------------------------------------

    #[test]
    fn is_zero_true() {
        assert!(FP::zero().is_zero());
        assert!(fp(0).is_zero());
    }

    #[test]
    fn is_zero_false() {
        assert!(!fp(1).is_zero());
    }

    // -- Display / From / Copy ----------------------------------------------

    #[test]
    fn display() {
        let s = format!("{}", fp(42));
        assert!(s.contains("42"));
    }

    #[test]
    fn from_i80f48_trait() {
        let v: FixedPointArithmetic = I80F48::from_num(7).into();
        assert_eq!(v.to_u128(), 7);
    }

    #[test]
    fn copy_semantics() {
        let a = fp(99);
        let b = a;
        assert_eq!(a, b);
    }

    // -- Ordering -----------------------------------------------------------

    #[test]
    fn ordering() {
        assert!(fp(1) < fp(2));
        assert!(fp(2) > fp(1));
    }

    // -- Additional edge cases ----------------------------------------------

    #[test]
    fn checked_div_zero_numerator() {
        let Ok(r) = FP::zero().checked_div(&fp(10), Rounding::Down) else {
            panic!("expected Ok");
        };
        assert!(r.is_zero());
    }

    #[test]
    fn checked_div_zero_numerator_round_up() {
        let Ok(r) = FP::zero().checked_div(&fp(10), Rounding::Up) else {
            panic!("expected Ok");
        };
        assert!(r.is_zero());
    }

    #[test]
    fn from_u128_roundtrip_small() {
        let v = FP::from_u128(1_000_000);
        assert_eq!(v.to_u128(), 1_000_000);
    }

    #[test]
    fn checked_add_negative_values() {
        let Ok(r) = fp(-3).checked_add(&fp(-2)) else {
            panic!("expected Ok");
        };
        assert!((r.to_f64_lossy() - (-5.0)).abs() < f64::EPSILON);
    }

    #[test]
    fn checked_mul_negative_times_positive() {
        let Ok(r) = fp(-3).checked_mul(&fp(2)) else {
            panic!("expected Ok");
        };
        assert!((r.to_f64_lossy() - (-6.0)).abs() < f64::EPSILON);
    }

    #[test]
    fn checked_div_negative_by_positive() {
        let Ok(r) = fp(-6).checked_div(&fp(2), Rounding::Down) else {
            panic!("expected Ok");
        };
        assert!((r.to_f64_lossy() - (-3.0)).abs() < f64::EPSILON);
    }

    #[test]
    fn min_with_equal() {
        assert_eq!(Precision::min(&fp(5), &fp(5)), fp(5));
    }

    #[test]
    fn max_with_equal() {
        assert_eq!(Precision::max(&fp(5), &fp(5)), fp(5));
    }

    #[test]
    fn min_with_negative() {
        assert_eq!(Precision::min(&fp(-3), &fp(3)), fp(-3));
    }

    #[test]
    fn max_with_negative() {
        assert_eq!(Precision::max(&fp(-3), &fp(3)), fp(3));
    }
}
