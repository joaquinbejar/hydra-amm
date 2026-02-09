//! Precision trait for feature-gated numeric backends.
//!
//! The [`Precision`] trait abstracts over numeric types so that pool
//! implementations can be generic over the arithmetic backend.  At compile
//! time exactly one backend is selected via Cargo feature flags, giving
//! zero runtime branching overhead.
//!
//! See the crate-level feature table for available backends:
//!
//! | Feature | Backend | Type |
//! |---------|---------|------|
//! | `float` | IEEE 754 `f64` | `FloatArithmetic` |
//! | `fixed-point` | `I80F48` (80-bit int, 48-bit frac) | `FixedPointArithmetic` |

use crate::domain::Rounding;
use crate::error::AmmError;

/// Abstraction over numeric types used in AMM calculations.
///
/// All pool implementations are generic over `P: Precision` so that the
/// same algorithm can run with either fixed-point or floating-point
/// arithmetic depending on compile-time feature selection.
///
/// # Contract
///
/// - All checked arithmetic methods return [`Err`] on overflow, underflow,
///   or division by zero — they **never** panic.
/// - Conversion helpers (`from_u128`, `from_f64`) are infallible but may
///   lose precision for values outside the representable range (documented
///   per implementation).
/// - `zero()` and `one()` return the additive and multiplicative identities.
pub trait Precision: Clone + Copy + core::fmt::Debug + PartialEq + PartialOrd {
    // -- Identity constants -------------------------------------------------

    /// Returns the additive identity (zero).
    #[must_use]
    fn zero() -> Self;

    /// Returns the multiplicative identity (one).
    #[must_use]
    fn one() -> Self;

    // -- Conversions --------------------------------------------------------

    /// Converts a `u128` value to this precision type.
    ///
    /// Precision may be lost for values exceeding the type's representable
    /// range.  See each implementation's documentation for details.
    #[must_use]
    fn from_u128(value: u128) -> Self;

    /// Extracts the integer part as `u128`, truncating any fractional
    /// component toward zero.
    ///
    /// Negative values are clamped to `0`.
    #[must_use]
    fn to_u128(&self) -> u128;

    /// Converts an `f64` value to this precision type.
    ///
    /// Precision may be lost depending on the target type's capabilities.
    #[must_use]
    fn from_f64(value: f64) -> Self;

    /// Converts this value to `f64`, potentially losing precision.
    #[must_use]
    fn to_f64_lossy(&self) -> f64;

    // -- Checked arithmetic -------------------------------------------------

    /// Checked addition.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::Overflow`] if the result is not representable.
    fn checked_add(&self, other: &Self) -> Result<Self, AmmError>;

    /// Checked subtraction.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::Underflow`] if the result is not representable.
    fn checked_sub(&self, other: &Self) -> Result<Self, AmmError>;

    /// Checked multiplication.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::Overflow`] if the result is not representable.
    fn checked_mul(&self, other: &Self) -> Result<Self, AmmError>;

    /// Checked division with explicit [`Rounding`] direction.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::DivisionByZero`] if `other` is zero.
    /// Returns [`AmmError::Overflow`] if the result is not representable.
    fn checked_div(&self, other: &Self, rounding: Rounding) -> Result<Self, AmmError>;

    // -- Comparison helpers -------------------------------------------------

    /// Returns the smaller of two values.
    #[must_use]
    fn min(&self, other: &Self) -> Self;

    /// Returns the larger of two values.
    #[must_use]
    fn max(&self, other: &Self) -> Self;

    /// Returns the absolute value.
    #[must_use]
    fn abs(&self) -> Self;

    /// Returns `true` if the value is zero.
    #[must_use]
    fn is_zero(&self) -> bool;
}
