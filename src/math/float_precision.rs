//! Floating-point implementation of the [`Precision`] trait.
//!
//! This module is only available when the `float` Cargo feature is enabled.
//! It provides [`FloatArithmetic`], a newtype over `f64` that implements
//! [`Precision`] using IEEE 754 double-precision arithmetic.
//!
//! # Precision characteristics
//!
//! | Aspect | Value |
//! |--------|-------|
//! | Significant digits | ~15–17 |
//! | Range | ±2^1024 |
//! | Determinism | Subject to IEEE 754 rounding |
//!
//! # When to use
//!
//! Use `FloatArithmetic` for off-chain simulation, bots, and analytics
//! where iteration speed matters more than bit-for-bit determinism.

use core::fmt;

use crate::domain::Rounding;
use crate::error::AmmError;

use super::Precision;

/// IEEE 754 `f64`-backed precision type for off-chain computation.
///
/// All checked arithmetic methods return [`Err`] when the result is
/// non-finite (`NaN` or `±∞`).  Conversion helpers are infallible but
/// may lose precision for very large integer values.
///
/// # Examples
///
/// ```
/// use hydra_amm::math::{FloatArithmetic, Precision};
///
/// let a = FloatArithmetic::new(10.0);
/// let b = FloatArithmetic::new(3.0);
/// let sum = a.checked_add(&b);
/// assert!(sum.is_ok());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct FloatArithmetic(f64);

impl FloatArithmetic {
    /// Creates a new `FloatArithmetic` from a raw `f64`.
    #[inline]
    #[must_use]
    pub fn new(value: f64) -> Self {
        Self(value)
    }

    /// Returns the underlying `f64` value.
    #[inline]
    #[must_use]
    pub const fn get(&self) -> f64 {
        self.0
    }
}

impl From<f64> for FloatArithmetic {
    #[inline]
    fn from(value: f64) -> Self {
        Self(value)
    }
}

impl fmt::Display for FloatArithmetic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Precision for FloatArithmetic {
    #[inline]
    fn zero() -> Self {
        Self(0.0)
    }

    #[inline]
    fn one() -> Self {
        Self(1.0)
    }

    // -- Conversions --------------------------------------------------------

    /// Converts `u128` to `f64`.
    ///
    /// Values above 2^53 lose precision because `f64` has only 53 bits of
    /// mantissa.
    #[inline]
    fn from_u128(value: u128) -> Self {
        #[allow(clippy::cast_precision_loss)]
        Self(value as f64)
    }

    /// Truncates toward zero and returns as `u128`.
    ///
    /// Negative values produce `0`.  Values above `u128::MAX` saturate to
    /// `u128::MAX`.  `NaN` produces `0`.
    #[inline]
    fn to_u128(&self) -> u128 {
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let v = self.0 as u128;
        v
    }

    #[inline]
    fn from_f64(value: f64) -> Self {
        Self(value)
    }

    #[inline]
    fn to_f64_lossy(&self) -> f64 {
        self.0
    }

    // -- Checked arithmetic -------------------------------------------------

    fn checked_add(&self, other: &Self) -> Result<Self, AmmError> {
        let result = self.0 + other.0;
        if result.is_finite() {
            Ok(Self(result))
        } else {
            Err(AmmError::Overflow("float addition overflow"))
        }
    }

    fn checked_sub(&self, other: &Self) -> Result<Self, AmmError> {
        let result = self.0 - other.0;
        if result.is_finite() {
            Ok(Self(result))
        } else {
            Err(AmmError::Underflow("float subtraction underflow"))
        }
    }

    fn checked_mul(&self, other: &Self) -> Result<Self, AmmError> {
        let result = self.0 * other.0;
        if result.is_finite() {
            Ok(Self(result))
        } else {
            Err(AmmError::Overflow("float multiplication overflow"))
        }
    }

    /// Divides using IEEE 754 semantics.
    ///
    /// The `_rounding` parameter is accepted for API consistency but has no
    /// effect — `f64` division always uses IEEE 754 round-to-nearest-even.
    /// For explicit floor/ceil rounding use the higher-level `div_round`
    /// helper instead.
    fn checked_div(&self, other: &Self, _rounding: Rounding) -> Result<Self, AmmError> {
        if other.0 == 0.0 {
            return Err(AmmError::DivisionByZero);
        }
        let result = self.0 / other.0;
        if result.is_finite() {
            Ok(Self(result))
        } else {
            Err(AmmError::Overflow("float division overflow"))
        }
    }

    // -- Comparison helpers -------------------------------------------------

    #[inline]
    fn min(&self, other: &Self) -> Self {
        Self(self.0.min(other.0))
    }

    #[inline]
    fn max(&self, other: &Self) -> Self {
        Self(self.0.max(other.0))
    }

    #[inline]
    fn abs(&self) -> Self {
        Self(self.0.abs())
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0 == 0.0
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;

    type F = FloatArithmetic;

    // -- Identity -----------------------------------------------------------

    #[test]
    fn zero_is_zero() {
        assert!(F::zero().is_zero());
        assert!((F::zero().get()).abs() < f64::EPSILON);
    }

    #[test]
    fn one_is_one() {
        assert!(!F::one().is_zero());
        assert!((F::one().get() - 1.0).abs() < f64::EPSILON);
    }

    // -- Conversions --------------------------------------------------------

    #[test]
    fn from_u128_small() {
        let v = F::from_u128(42);
        assert!((v.get() - 42.0).abs() < f64::EPSILON);
    }

    #[test]
    fn from_u128_large() {
        // Precision loss is expected for very large values
        let v = F::from_u128(u128::MAX);
        assert!(v.get() > 0.0);
    }

    #[test]
    fn to_u128_truncates() {
        let v = F::new(3.9);
        assert_eq!(v.to_u128(), 3);
    }

    #[test]
    fn to_u128_negative_clamps() {
        let v = F::new(-5.0);
        assert_eq!(v.to_u128(), 0);
    }

    #[test]
    fn from_f64_roundtrip() {
        let v = F::from_f64(core::f64::consts::PI);
        assert!((v.to_f64_lossy() - core::f64::consts::PI).abs() < f64::EPSILON);
    }

    // -- Checked add --------------------------------------------------------

    #[test]
    fn checked_add_normal() {
        let Ok(r) = F::new(1.5).checked_add(&F::new(2.5)) else {
            panic!("expected Ok");
        };
        assert!((r.get() - 4.0).abs() < f64::EPSILON);
    }

    #[test]
    fn checked_add_overflow() {
        let result = F::new(f64::MAX).checked_add(&F::new(f64::MAX));
        assert!(result.is_err());
    }

    // -- Checked sub --------------------------------------------------------

    #[test]
    fn checked_sub_normal() {
        let Ok(r) = F::new(5.0).checked_sub(&F::new(3.0)) else {
            panic!("expected Ok");
        };
        assert!((r.get() - 2.0).abs() < f64::EPSILON);
    }

    #[test]
    fn checked_sub_negative_result() {
        let Ok(r) = F::new(3.0).checked_sub(&F::new(5.0)) else {
            panic!("expected Ok");
        };
        assert!((r.get() - (-2.0)).abs() < f64::EPSILON);
    }

    #[test]
    fn checked_sub_overflow() {
        let result = F::new(-f64::MAX).checked_sub(&F::new(f64::MAX));
        assert!(result.is_err());
    }

    // -- Checked mul --------------------------------------------------------

    #[test]
    fn checked_mul_normal() {
        let Ok(r) = F::new(3.0).checked_mul(&F::new(4.0)) else {
            panic!("expected Ok");
        };
        assert!((r.get() - 12.0).abs() < f64::EPSILON);
    }

    #[test]
    fn checked_mul_zero() {
        let Ok(r) = F::new(0.0).checked_mul(&F::new(1e300)) else {
            panic!("expected Ok");
        };
        assert!(r.is_zero());
    }

    #[test]
    fn checked_mul_overflow() {
        let result = F::new(f64::MAX).checked_mul(&F::new(2.0));
        assert!(result.is_err());
    }

    // -- Checked div --------------------------------------------------------

    #[test]
    fn checked_div_normal() {
        let Ok(r) = F::new(10.0).checked_div(&F::new(4.0), Rounding::Down) else {
            panic!("expected Ok");
        };
        assert!((r.get() - 2.5).abs() < f64::EPSILON);
    }

    #[test]
    fn checked_div_by_zero() {
        let result = F::new(1.0).checked_div(&F::zero(), Rounding::Down);
        assert!(result.is_err());
    }

    #[test]
    fn checked_div_rounding_param_accepted() {
        // Both rounding directions produce the same IEEE 754 result for f64
        let Ok(r_down) = F::new(10.0).checked_div(&F::new(3.0), Rounding::Down) else {
            panic!("expected Ok");
        };
        let Ok(r_up) = F::new(10.0).checked_div(&F::new(3.0), Rounding::Up) else {
            panic!("expected Ok");
        };
        assert_eq!(r_down, r_up);
    }

    // -- Min / Max / Abs ----------------------------------------------------

    #[test]
    fn min_returns_smaller() {
        assert_eq!(F::new(1.0).min(&F::new(2.0)), F::new(1.0));
    }

    #[test]
    fn max_returns_larger() {
        assert_eq!(F::new(1.0).max(&F::new(2.0)), F::new(2.0));
    }

    #[test]
    fn abs_positive() {
        assert_eq!(F::new(3.0).abs(), F::new(3.0));
    }

    #[test]
    fn abs_negative() {
        assert_eq!(F::new(-3.0).abs(), F::new(3.0));
    }

    #[test]
    fn abs_zero() {
        assert!(F::new(0.0).abs().is_zero());
    }

    // -- is_zero ------------------------------------------------------------

    #[test]
    fn is_zero_true() {
        assert!(F::zero().is_zero());
        assert!(F::new(0.0).is_zero());
    }

    #[test]
    fn is_zero_false() {
        assert!(!F::new(1e-300).is_zero());
    }

    // -- Display / From / Copy ----------------------------------------------

    #[test]
    fn display() {
        assert_eq!(format!("{}", F::new(1.5)), "1.5");
    }

    #[test]
    fn from_f64_trait() {
        let v: FloatArithmetic = core::f64::consts::PI.into();
        assert!((v.get() - core::f64::consts::PI).abs() < f64::EPSILON);
    }

    #[test]
    fn copy_semantics() {
        let a = F::new(42.0);
        let b = a;
        assert_eq!(a, b);
    }

    // -- Ordering -----------------------------------------------------------

    #[test]
    fn ordering() {
        assert!(F::new(1.0) < F::new(2.0));
        assert!(F::new(2.0) > F::new(1.0));
    }

    // -- NaN handling -------------------------------------------------------

    #[test]
    fn to_u128_nan_gives_zero() {
        let v = F::new(f64::NAN);
        assert_eq!(v.to_u128(), 0);
    }

    #[test]
    fn to_u128_infinity_saturates() {
        let v = F::new(f64::INFINITY);
        // Rust saturating cast: f64::INFINITY as u128 = u128::MAX
        assert!(v.to_u128() > 0);
    }

    #[test]
    fn from_u128_roundtrip_small() {
        let v = F::from_u128(1_000_000);
        assert_eq!(v.to_u128(), 1_000_000);
    }

    #[test]
    fn checked_add_negative_values() {
        let Ok(r) = F::new(-3.0).checked_add(&F::new(-2.0)) else {
            panic!("expected Ok");
        };
        assert!((r.get() - (-5.0)).abs() < f64::EPSILON);
    }

    #[test]
    fn checked_mul_negative_times_positive() {
        let Ok(r) = F::new(-3.0).checked_mul(&F::new(2.0)) else {
            panic!("expected Ok");
        };
        assert!((r.get() - (-6.0)).abs() < f64::EPSILON);
    }

    #[test]
    fn checked_div_negative_by_positive() {
        let Ok(r) = F::new(-6.0).checked_div(&F::new(2.0), Rounding::Down) else {
            panic!("expected Ok");
        };
        assert!((r.get() - (-3.0)).abs() < f64::EPSILON);
    }

    #[test]
    fn is_zero_negative_zero() {
        assert!(F::new(-0.0).is_zero());
    }

    #[test]
    fn min_with_equal() {
        assert_eq!(F::new(5.0).min(&F::new(5.0)), F::new(5.0));
    }

    #[test]
    fn max_with_equal() {
        assert_eq!(F::new(5.0).max(&F::new(5.0)), F::new(5.0));
    }
}
