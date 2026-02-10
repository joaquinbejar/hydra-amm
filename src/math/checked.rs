//! Checked arithmetic trait for domain wrapper types.
//!
//! The [`CheckedArithmetic`] trait provides fallible arithmetic operations
//! that return [`Result<Self, AmmError>`](crate::error::AmmError) instead
//! of panicking on overflow, underflow, or division by zero.
//!
//! # Implementations
//!
//! - [`Amount`] — token quantities (`u128`)
//! - [`Liquidity`] — pool share quantities (`u128`)
//!
//! # Examples
//!
//! ```
//! use hydra_amm::domain::{Amount, Rounding};
//! use hydra_amm::math::CheckedArithmetic;
//!
//! let a = Amount::new(100);
//! let b = Amount::new(200);
//! let sum = a.safe_add(&b);
//! assert!(sum.is_ok());
//! ```

use crate::domain::{Amount, Liquidity, Rounding};
use crate::error::AmmError;

/// Fallible arithmetic for domain wrapper types.
///
/// Every method returns [`Result<Self, AmmError>`] with a specific error
/// variant so callers can distinguish overflow from underflow from
/// division by zero.
///
/// # Contract
///
/// - **No panics** — all error conditions produce `Err`.
/// - **No saturation** — saturation hides bugs; errors propagate instead.
/// - Implementations must delegate to the inner type's checked operations.
pub trait CheckedArithmetic: Sized {
    /// Checked addition.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::Overflow`] if the result exceeds the
    /// representable range.
    fn safe_add(&self, other: &Self) -> Result<Self, AmmError>;

    /// Checked subtraction.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::Underflow`] if the result would be negative.
    fn safe_sub(&self, other: &Self) -> Result<Self, AmmError>;

    /// Checked multiplication.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::Overflow`] if the result exceeds the
    /// representable range.
    fn safe_mul(&self, other: &Self) -> Result<Self, AmmError>;

    /// Checked division with explicit [`Rounding`] direction.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::DivisionByZero`] if `other` is zero.
    fn safe_div(&self, other: &Self, rounding: Rounding) -> Result<Self, AmmError>;

    /// Checked addition of a raw `u128` value.
    ///
    /// Convenience method that wraps the raw value before adding.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::Overflow`] if the result exceeds the
    /// representable range.
    fn safe_add_u128(&self, value: u128) -> Result<Self, AmmError>;
}

// ---------------------------------------------------------------------------
// Amount
// ---------------------------------------------------------------------------

impl CheckedArithmetic for Amount {
    #[inline]
    fn safe_add(&self, other: &Self) -> Result<Self, AmmError> {
        self.checked_add(other)
            .ok_or(AmmError::Overflow("amount addition overflow"))
    }

    #[inline]
    fn safe_sub(&self, other: &Self) -> Result<Self, AmmError> {
        self.checked_sub(other)
            .ok_or(AmmError::Underflow("amount subtraction underflow"))
    }

    #[inline]
    fn safe_mul(&self, other: &Self) -> Result<Self, AmmError> {
        self.checked_mul(other)
            .ok_or(AmmError::Overflow("amount multiplication overflow"))
    }

    #[inline]
    fn safe_div(&self, other: &Self, rounding: Rounding) -> Result<Self, AmmError> {
        self.checked_div(other, rounding)
            .ok_or(AmmError::DivisionByZero)
    }

    #[inline]
    fn safe_add_u128(&self, value: u128) -> Result<Self, AmmError> {
        self.checked_add(&Amount::new(value))
            .ok_or(AmmError::Overflow("amount add u128 overflow"))
    }
}

// ---------------------------------------------------------------------------
// Liquidity
// ---------------------------------------------------------------------------

impl CheckedArithmetic for Liquidity {
    #[inline]
    fn safe_add(&self, other: &Self) -> Result<Self, AmmError> {
        self.checked_add(other)
            .ok_or(AmmError::Overflow("liquidity addition overflow"))
    }

    #[inline]
    fn safe_sub(&self, other: &Self) -> Result<Self, AmmError> {
        self.checked_sub(other)
            .ok_or(AmmError::Underflow("liquidity subtraction underflow"))
    }

    #[inline]
    fn safe_mul(&self, other: &Self) -> Result<Self, AmmError> {
        self.get()
            .checked_mul(other.get())
            .map(Liquidity::new)
            .ok_or(AmmError::Overflow("liquidity multiplication overflow"))
    }

    fn safe_div(&self, other: &Self, rounding: Rounding) -> Result<Self, AmmError> {
        if other.is_zero() {
            return Err(AmmError::DivisionByZero);
        }
        let n = self.get();
        let d = other.get();
        let result = match rounding {
            Rounding::Down => n / d,
            Rounding::Up => {
                let q = n / d;
                let r = n % d;
                if r != 0 { q + 1 } else { q }
            }
        };
        Ok(Liquidity::new(result))
    }

    #[inline]
    fn safe_add_u128(&self, value: u128) -> Result<Self, AmmError> {
        self.checked_add(&Liquidity::new(value))
            .ok_or(AmmError::Overflow("liquidity add u128 overflow"))
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------------
    // Amount
    // -----------------------------------------------------------------------

    mod amount {
        use super::*;

        // -- safe_add -------------------------------------------------------

        #[test]
        fn add_ok() {
            let Ok(r) = Amount::new(100).safe_add(&Amount::new(200)) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Amount::new(300));
        }

        #[test]
        fn add_overflow() {
            let err = Amount::MAX.safe_add(&Amount::new(1));
            assert!(err.is_err());
            let Err(AmmError::Overflow(_)) = err else {
                panic!("expected Overflow");
            };
        }

        // -- safe_sub -------------------------------------------------------

        #[test]
        fn sub_ok() {
            let Ok(r) = Amount::new(300).safe_sub(&Amount::new(100)) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Amount::new(200));
        }

        #[test]
        fn sub_underflow() {
            let err = Amount::new(1).safe_sub(&Amount::new(2));
            assert!(err.is_err());
            let Err(AmmError::Underflow(_)) = err else {
                panic!("expected Underflow");
            };
        }

        // -- safe_mul -------------------------------------------------------

        #[test]
        fn mul_ok() {
            let Ok(r) = Amount::new(100).safe_mul(&Amount::new(200)) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Amount::new(20_000));
        }

        #[test]
        fn mul_overflow() {
            let err = Amount::MAX.safe_mul(&Amount::new(2));
            assert!(err.is_err());
            let Err(AmmError::Overflow(_)) = err else {
                panic!("expected Overflow");
            };
        }

        // -- safe_div -------------------------------------------------------

        #[test]
        fn div_round_down() {
            let Ok(r) = Amount::new(10).safe_div(&Amount::new(3), Rounding::Down) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Amount::new(3));
        }

        #[test]
        fn div_round_up() {
            let Ok(r) = Amount::new(10).safe_div(&Amount::new(3), Rounding::Up) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Amount::new(4));
        }

        #[test]
        fn div_exact() {
            let Ok(r_down) = Amount::new(10).safe_div(&Amount::new(2), Rounding::Down) else {
                panic!("expected Ok");
            };
            let Ok(r_up) = Amount::new(10).safe_div(&Amount::new(2), Rounding::Up) else {
                panic!("expected Ok");
            };
            assert_eq!(r_down, Amount::new(5));
            assert_eq!(r_up, Amount::new(5));
        }

        #[test]
        fn div_by_zero() {
            let err = Amount::new(100).safe_div(&Amount::ZERO, Rounding::Down);
            assert!(err.is_err());
            let Err(AmmError::DivisionByZero) = err else {
                panic!("expected DivisionByZero");
            };
        }

        // -- safe_add_u128 --------------------------------------------------

        #[test]
        fn add_u128_ok() {
            let Ok(r) = Amount::new(100).safe_add_u128(50) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Amount::new(150));
        }

        #[test]
        fn add_u128_overflow() {
            let err = Amount::MAX.safe_add_u128(1);
            assert!(err.is_err());
            let Err(AmmError::Overflow(_)) = err else {
                panic!("expected Overflow");
            };
        }

        // -- chaining -------------------------------------------------------

        #[test]
        fn chaining_works() {
            // (100 + 200) * 3 - 100 = 800
            let result = Amount::new(100)
                .safe_add(&Amount::new(200))
                .and_then(|v| v.safe_mul(&Amount::new(3)))
                .and_then(|v| v.safe_sub(&Amount::new(100)));
            let Ok(r) = result else {
                panic!("expected Ok");
            };
            assert_eq!(r, Amount::new(800));
        }

        #[test]
        fn add_zero_identity() {
            let Ok(r) = Amount::new(42).safe_add(&Amount::ZERO) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Amount::new(42));
        }

        #[test]
        fn sub_to_zero() {
            let Ok(r) = Amount::new(42).safe_sub(&Amount::new(42)) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Amount::ZERO);
        }

        #[test]
        fn mul_by_zero() {
            let Ok(r) = Amount::new(999).safe_mul(&Amount::ZERO) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Amount::ZERO);
        }

        #[test]
        fn mul_by_one() {
            let Ok(r) = Amount::new(42).safe_mul(&Amount::new(1)) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Amount::new(42));
        }

        #[test]
        fn div_zero_numerator() {
            let Ok(r) = Amount::ZERO.safe_div(&Amount::new(10), Rounding::Down) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Amount::ZERO);
        }

        #[test]
        fn div_by_one() {
            let Ok(r) = Amount::new(42).safe_div(&Amount::new(1), Rounding::Down) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Amount::new(42));
        }

        #[test]
        fn add_u128_zero() {
            let Ok(r) = Amount::new(42).safe_add_u128(0) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Amount::new(42));
        }
    }

    // -----------------------------------------------------------------------
    // Liquidity
    // -----------------------------------------------------------------------

    mod liquidity {
        use super::*;

        // -- safe_add -------------------------------------------------------

        #[test]
        fn add_ok() {
            let Ok(r) = Liquidity::new(100).safe_add(&Liquidity::new(200)) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Liquidity::new(300));
        }

        #[test]
        fn add_overflow() {
            let err = Liquidity::new(u128::MAX).safe_add(&Liquidity::new(1));
            assert!(err.is_err());
            let Err(AmmError::Overflow(_)) = err else {
                panic!("expected Overflow");
            };
        }

        // -- safe_sub -------------------------------------------------------

        #[test]
        fn sub_ok() {
            let Ok(r) = Liquidity::new(300).safe_sub(&Liquidity::new(100)) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Liquidity::new(200));
        }

        #[test]
        fn sub_underflow() {
            let err = Liquidity::new(1).safe_sub(&Liquidity::new(2));
            assert!(err.is_err());
            let Err(AmmError::Underflow(_)) = err else {
                panic!("expected Underflow");
            };
        }

        // -- safe_mul -------------------------------------------------------

        #[test]
        fn mul_ok() {
            let Ok(r) = Liquidity::new(100).safe_mul(&Liquidity::new(200)) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Liquidity::new(20_000));
        }

        #[test]
        fn mul_overflow() {
            let err = Liquidity::new(u128::MAX).safe_mul(&Liquidity::new(2));
            assert!(err.is_err());
            let Err(AmmError::Overflow(_)) = err else {
                panic!("expected Overflow");
            };
        }

        // -- safe_div -------------------------------------------------------

        #[test]
        fn div_round_down() {
            let Ok(r) = Liquidity::new(10).safe_div(&Liquidity::new(3), Rounding::Down) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Liquidity::new(3));
        }

        #[test]
        fn div_round_up() {
            let Ok(r) = Liquidity::new(10).safe_div(&Liquidity::new(3), Rounding::Up) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Liquidity::new(4));
        }

        #[test]
        fn div_exact() {
            let Ok(r_down) = Liquidity::new(10).safe_div(&Liquidity::new(2), Rounding::Down) else {
                panic!("expected Ok");
            };
            let Ok(r_up) = Liquidity::new(10).safe_div(&Liquidity::new(2), Rounding::Up) else {
                panic!("expected Ok");
            };
            assert_eq!(r_down, Liquidity::new(5));
            assert_eq!(r_up, Liquidity::new(5));
        }

        #[test]
        fn div_by_zero() {
            let err = Liquidity::new(100).safe_div(&Liquidity::ZERO, Rounding::Down);
            assert!(err.is_err());
            let Err(AmmError::DivisionByZero) = err else {
                panic!("expected DivisionByZero");
            };
        }

        // -- safe_add_u128 --------------------------------------------------

        #[test]
        fn add_u128_ok() {
            let Ok(r) = Liquidity::new(100).safe_add_u128(50) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Liquidity::new(150));
        }

        #[test]
        fn add_u128_overflow() {
            let err = Liquidity::new(u128::MAX).safe_add_u128(1);
            assert!(err.is_err());
            let Err(AmmError::Overflow(_)) = err else {
                panic!("expected Overflow");
            };
        }

        // -- chaining -------------------------------------------------------

        #[test]
        fn chaining_works() {
            // (100 + 200) * 3 - 100 = 800
            let result = Liquidity::new(100)
                .safe_add(&Liquidity::new(200))
                .and_then(|v| v.safe_mul(&Liquidity::new(3)))
                .and_then(|v| v.safe_sub(&Liquidity::new(100)));
            let Ok(r) = result else {
                panic!("expected Ok");
            };
            assert_eq!(r, Liquidity::new(800));
        }

        #[test]
        fn add_zero_identity() {
            let Ok(r) = Liquidity::new(42).safe_add(&Liquidity::ZERO) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Liquidity::new(42));
        }

        #[test]
        fn sub_to_zero() {
            let Ok(r) = Liquidity::new(42).safe_sub(&Liquidity::new(42)) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Liquidity::ZERO);
        }

        #[test]
        fn mul_by_zero() {
            let Ok(r) = Liquidity::new(999).safe_mul(&Liquidity::ZERO) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Liquidity::ZERO);
        }

        #[test]
        fn mul_by_one() {
            let Ok(r) = Liquidity::new(42).safe_mul(&Liquidity::new(1)) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Liquidity::new(42));
        }

        #[test]
        fn div_zero_numerator() {
            let Ok(r) = Liquidity::ZERO.safe_div(&Liquidity::new(10), Rounding::Down) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Liquidity::ZERO);
        }

        #[test]
        fn div_by_one() {
            let Ok(r) = Liquidity::new(42).safe_div(&Liquidity::new(1), Rounding::Down) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Liquidity::new(42));
        }

        #[test]
        fn add_u128_zero() {
            let Ok(r) = Liquidity::new(42).safe_add_u128(0) else {
                panic!("expected Ok");
            };
            assert_eq!(r, Liquidity::new(42));
        }
    }
}
