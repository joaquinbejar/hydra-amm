//! Exchange rate between two tokens.

use core::fmt;

use super::{Amount, Rounding};
use crate::error::AmmError;

/// Exchange rate between two tokens as a dimensionless ratio (`amount_b / amount_a`).
///
/// Wraps an `f64` value that must be finite and non-negative. For
/// fixed-point arithmetic, a future implementation behind the
/// `fixed-point` feature flag will wrap `I80F48`.
///
/// # Examples
///
/// ```
/// use hydra_amm::domain::Price;
///
/// let price = Price::new(1.5);
/// assert!(price.is_ok());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct Price(f64);

impl Price {
    /// Price ratio of 1:1.
    pub const ONE: Self = Self(1.0);

    /// Price ratio of zero.
    pub const ZERO: Self = Self(0.0);

    /// Creates a new `Price` from an `f64` value.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::InvalidPrice`] if the value is negative, NaN,
    /// or infinite.
    pub fn new(value: f64) -> crate::error::Result<Self> {
        if !value.is_finite() || value < 0.0 {
            return Err(AmmError::InvalidPrice(
                "price must be finite and non-negative",
            ));
        }
        Ok(Self(value))
    }

    /// Returns the underlying `f64` value.
    #[must_use]
    pub const fn get(&self) -> f64 {
        self.0
    }

    /// Returns `true` if the price is finite.
    ///
    /// Always returns `true` for a properly constructed `Price`.
    #[must_use]
    pub fn is_finite(&self) -> bool {
        self.0.is_finite()
    }

    /// Computes a price from two amounts: `amount_b / amount_a`.
    ///
    /// The `_rounding` parameter is accepted for API consistency with
    /// fixed-point implementations but is unused for `f64` arithmetic.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::DivisionByZero`] if `amount_a` is zero.
    /// Returns [`AmmError::InvalidPrice`] if the resulting ratio is not
    /// finite.
    pub fn from_amounts(
        amount_b: Amount,
        amount_a: Amount,
        _rounding: Rounding,
    ) -> crate::error::Result<Self> {
        if amount_a.is_zero() {
            return Err(AmmError::DivisionByZero);
        }
        let price = amount_b.get() as f64 / amount_a.get() as f64;
        Self::new(price)
    }

    /// Scales an [`Amount`] by this price.
    ///
    /// The result is rounded according to the specified [`Rounding`]
    /// direction before conversion back to an integer [`Amount`].
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::Overflow`] if the result is not finite or
    /// exceeds the representable `u128` range.
    pub fn multiply(&self, amount: Amount, rounding: Rounding) -> crate::error::Result<Amount> {
        let result = self.0 * amount.get() as f64;
        if !result.is_finite() || result < 0.0 {
            return Err(AmmError::Overflow("price multiply overflow"));
        }

        let rounded = match rounding {
            Rounding::Down => result.floor(),
            Rounding::Up => result.ceil(),
        };

        #[allow(clippy::cast_precision_loss)]
        let max = u128::MAX as f64;
        if rounded > max {
            return Err(AmmError::Overflow("price multiply exceeds maximum amount"));
        }

        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let int_val = rounded as u128;
        Ok(Amount::new(int_val))
    }

    /// Computes the reciprocal price (`1 / self`).
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::DivisionByZero`] if the price is zero.
    /// Returns [`AmmError::InvalidPrice`] if the reciprocal is not finite.
    pub fn inverse(&self) -> crate::error::Result<Self> {
        if self.0 == 0.0 {
            return Err(AmmError::DivisionByZero);
        }
        let inv = 1.0 / self.0;
        Self::new(inv)
    }
}

impl fmt::Display for Price {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;

    // -- Construction -------------------------------------------------------

    #[test]
    fn new_valid() {
        let Ok(p) = Price::new(1.5) else {
            panic!("expected Ok");
        };
        assert!((p.get() - 1.5).abs() < f64::EPSILON);
    }

    #[test]
    fn new_zero() {
        let Ok(p) = Price::new(0.0) else {
            panic!("expected Ok");
        };
        assert!((p.get() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn new_negative() {
        assert!(Price::new(-1.0).is_err());
    }

    #[test]
    fn new_nan() {
        assert!(Price::new(f64::NAN).is_err());
    }

    #[test]
    fn new_infinity() {
        assert!(Price::new(f64::INFINITY).is_err());
    }

    #[test]
    fn new_neg_infinity() {
        assert!(Price::new(f64::NEG_INFINITY).is_err());
    }

    // -- Constants ----------------------------------------------------------

    #[test]
    fn constants() {
        assert!((Price::ONE.get() - 1.0).abs() < f64::EPSILON);
        assert!((Price::ZERO.get() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn constants_are_finite() {
        assert!(Price::ONE.is_finite());
        assert!(Price::ZERO.is_finite());
    }

    // -- from_amounts -------------------------------------------------------

    #[test]
    fn from_amounts_normal() {
        let Ok(p) = Price::from_amounts(Amount::new(300), Amount::new(100), Rounding::Down) else {
            panic!("expected Ok");
        };
        assert!((p.get() - 3.0).abs() < f64::EPSILON);
    }

    #[test]
    fn from_amounts_zero_numerator() {
        let Ok(p) = Price::from_amounts(Amount::ZERO, Amount::new(100), Rounding::Down) else {
            panic!("expected Ok");
        };
        assert!((p.get() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn from_amounts_zero_denominator() {
        let result = Price::from_amounts(Amount::new(100), Amount::ZERO, Rounding::Down);
        assert!(result.is_err());
    }

    // -- multiply -----------------------------------------------------------

    #[test]
    fn multiply_round_down() {
        let Ok(p) = Price::new(1.5) else {
            panic!("expected Ok");
        };
        let Ok(result) = p.multiply(Amount::new(10), Rounding::Down) else {
            panic!("expected Ok");
        };
        assert_eq!(result, Amount::new(15));
    }

    #[test]
    fn multiply_round_up() {
        let Ok(p) = Price::new(1.1) else {
            panic!("expected Ok");
        };
        let Ok(result) = p.multiply(Amount::new(10), Rounding::Up) else {
            panic!("expected Ok");
        };
        // 1.1 * 10 = 11.0 (exact), ceil = 11
        assert_eq!(result, Amount::new(11));
    }

    #[test]
    fn multiply_zero_amount() {
        let Ok(p) = Price::new(1.5) else {
            panic!("expected Ok");
        };
        let Ok(result) = p.multiply(Amount::ZERO, Rounding::Down) else {
            panic!("expected Ok");
        };
        assert_eq!(result, Amount::ZERO);
    }

    #[test]
    fn multiply_zero_price() {
        let Ok(result) = Price::ZERO.multiply(Amount::new(100), Rounding::Down) else {
            panic!("expected Ok");
        };
        assert_eq!(result, Amount::ZERO);
    }

    // -- inverse ------------------------------------------------------------

    #[test]
    fn inverse_normal() {
        let Ok(p) = Price::new(2.0) else {
            panic!("expected Ok");
        };
        let Ok(inv) = p.inverse() else {
            panic!("expected Ok");
        };
        assert!((inv.get() - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn inverse_one() {
        let Ok(inv) = Price::ONE.inverse() else {
            panic!("expected Ok");
        };
        assert!((inv.get() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn inverse_zero() {
        assert!(Price::ZERO.inverse().is_err());
    }

    // -- Display ------------------------------------------------------------

    #[test]
    fn display() {
        let Ok(p) = Price::new(1.5) else {
            panic!("expected Ok");
        };
        assert_eq!(format!("{p}"), "1.5");
    }

    // -- Ordering -----------------------------------------------------------

    #[test]
    fn ordering() {
        assert!(Price::ZERO < Price::ONE);
    }

    // -- Copy ---------------------------------------------------------------

    #[test]
    fn copy_semantics() {
        let Ok(a) = Price::new(1.5) else {
            panic!("expected Ok");
        };
        let b = a;
        assert_eq!(a, b);
    }
}
