//! Outcome of a swap operation.

use core::fmt;

use super::{Amount, Price, Rounding};
use crate::error::AmmError;

/// The outcome of a swap operation, including amounts exchanged and fees paid.
///
/// # Invariants
///
/// - `amount_in > 0` and `amount_out > 0` — both amounts must be positive.
/// - `fee < amount_in` — fee must be less than the input amount.
///
/// # Examples
///
/// ```
/// use hydra_amm::domain::{Amount, SwapResult};
///
/// let result = SwapResult::new(Amount::new(1000), Amount::new(990), Amount::new(3));
/// assert!(result.is_ok());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SwapResult {
    amount_in: Amount,
    amount_out: Amount,
    fee: Amount,
}

impl SwapResult {
    /// Creates a new `SwapResult` with validated invariants.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::InvalidQuantity`] if:
    /// - `amount_in` is zero
    /// - `amount_out` is zero
    /// - `fee >= amount_in`
    pub const fn new(
        amount_in: Amount,
        amount_out: Amount,
        fee: Amount,
    ) -> crate::error::Result<Self> {
        if amount_in.is_zero() {
            return Err(AmmError::InvalidQuantity("amount_in must be positive"));
        }
        if amount_out.is_zero() {
            return Err(AmmError::InvalidQuantity("amount_out must be positive"));
        }
        if fee.get() >= amount_in.get() {
            return Err(AmmError::InvalidQuantity("fee must be less than amount_in"));
        }
        Ok(Self {
            amount_in,
            amount_out,
            fee,
        })
    }

    /// Returns the input amount.
    pub const fn amount_in(&self) -> Amount {
        self.amount_in
    }

    /// Returns the output amount.
    pub const fn amount_out(&self) -> Amount {
        self.amount_out
    }

    /// Returns the fee paid.
    pub const fn fee(&self) -> Amount {
        self.fee
    }

    /// Computes the realized price as `amount_out / amount_in`.
    ///
    /// The `rounding` parameter is accepted for API consistency with
    /// fixed-point implementations.
    ///
    /// # Errors
    ///
    /// Returns an error if the price computation fails.
    pub fn effective_price(&self, rounding: Rounding) -> crate::error::Result<Price> {
        Price::from_amounts(self.amount_out, self.amount_in, rounding)
    }

    /// Computes the slippage percentage relative to a reference price.
    ///
    /// The formula is `|effective_price - reference_price| / reference_price * 100`.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::DivisionByZero`] if `reference_price` is zero.
    /// Returns an error if the effective price computation fails.
    pub fn slippage_percent(
        &self,
        reference_price: Price,
        rounding: Rounding,
    ) -> crate::error::Result<f64> {
        if reference_price.get() == 0.0 {
            return Err(AmmError::DivisionByZero);
        }
        let effective = self.effective_price(rounding)?;
        let diff = (effective.get() - reference_price.get()).abs();
        Ok(diff / reference_price.get() * 100.0)
    }
}

impl fmt::Display for SwapResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "SwapResult(in={}, out={}, fee={})",
            self.amount_in, self.amount_out, self.fee
        )
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;

    // -- Construction -------------------------------------------------------

    #[test]
    fn valid_result() {
        let Ok(r) = SwapResult::new(Amount::new(1000), Amount::new(990), Amount::new(3)) else {
            panic!("expected Ok");
        };
        assert_eq!(r.amount_in(), Amount::new(1000));
        assert_eq!(r.amount_out(), Amount::new(990));
        assert_eq!(r.fee(), Amount::new(3));
    }

    #[test]
    fn valid_zero_fee() {
        let result = SwapResult::new(Amount::new(100), Amount::new(100), Amount::ZERO);
        assert!(result.is_ok());
    }

    #[test]
    fn invalid_zero_amount_in() {
        let result = SwapResult::new(Amount::ZERO, Amount::new(100), Amount::ZERO);
        assert!(result.is_err());
    }

    #[test]
    fn invalid_zero_amount_out() {
        let result = SwapResult::new(Amount::new(100), Amount::ZERO, Amount::ZERO);
        assert!(result.is_err());
    }

    #[test]
    fn invalid_fee_equals_amount_in() {
        let result = SwapResult::new(Amount::new(100), Amount::new(50), Amount::new(100));
        assert!(result.is_err());
    }

    #[test]
    fn invalid_fee_exceeds_amount_in() {
        let result = SwapResult::new(Amount::new(100), Amount::new(50), Amount::new(200));
        assert!(result.is_err());
    }

    // -- effective_price ----------------------------------------------------

    #[test]
    fn effective_price_normal() {
        let Ok(r) = SwapResult::new(Amount::new(100), Amount::new(200), Amount::new(1)) else {
            panic!("expected Ok");
        };
        let Ok(p) = r.effective_price(Rounding::Down) else {
            panic!("expected Ok");
        };
        assert!((p.get() - 2.0).abs() < f64::EPSILON);
    }

    // -- slippage_percent ---------------------------------------------------

    #[test]
    fn slippage_zero_when_price_matches() {
        let Ok(r) = SwapResult::new(Amount::new(100), Amount::new(200), Amount::new(1)) else {
            panic!("expected Ok");
        };
        let Ok(ref_price) = Price::new(2.0) else {
            panic!("expected Ok");
        };
        let Ok(slippage) = r.slippage_percent(ref_price, Rounding::Down) else {
            panic!("expected Ok");
        };
        assert!(slippage.abs() < f64::EPSILON);
    }

    #[test]
    fn slippage_positive_when_price_differs() {
        let Ok(r) = SwapResult::new(Amount::new(100), Amount::new(190), Amount::new(1)) else {
            panic!("expected Ok");
        };
        let Ok(ref_price) = Price::new(2.0) else {
            panic!("expected Ok");
        };
        let Ok(slippage) = r.slippage_percent(ref_price, Rounding::Down) else {
            panic!("expected Ok");
        };
        // effective = 1.9, |1.9 - 2.0| / 2.0 * 100 = 5.0
        assert!((slippage - 5.0).abs() < 0.01);
    }

    #[test]
    fn slippage_zero_reference_rejected() {
        let Ok(r) = SwapResult::new(Amount::new(100), Amount::new(200), Amount::new(1)) else {
            panic!("expected Ok");
        };
        assert!(r.slippage_percent(Price::ZERO, Rounding::Down).is_err());
    }

    // -- Display ------------------------------------------------------------

    #[test]
    fn display() {
        let Ok(r) = SwapResult::new(Amount::new(100), Amount::new(90), Amount::new(3)) else {
            panic!("expected Ok");
        };
        let s = format!("{r}");
        assert!(s.contains("100"));
        assert!(s.contains("90"));
        assert!(s.contains("3"));
    }

    // -- Copy ---------------------------------------------------------------

    #[test]
    fn copy_semantics() {
        let Ok(a) = SwapResult::new(Amount::new(100), Amount::new(90), Amount::new(1)) else {
            panic!("expected Ok");
        };
        let b = a;
        assert_eq!(a, b);
    }

    #[test]
    fn hash_consistency() {
        use core::hash::{Hash, Hasher};
        fn hash_of<T: Hash>(t: &T) -> u64 {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            t.hash(&mut h);
            h.finish()
        }
        let Ok(a) = SwapResult::new(Amount::new(100), Amount::new(90), Amount::new(3)) else {
            panic!("expected Ok");
        };
        let Ok(b) = SwapResult::new(Amount::new(100), Amount::new(90), Amount::new(3)) else {
            panic!("expected Ok");
        };
        assert_eq!(hash_of(&a), hash_of(&b));
    }

    #[test]
    fn fee_boundary_one_less_than_amount_in() {
        // fee = amount_in - 1 is the maximum valid fee
        let result = SwapResult::new(Amount::new(100), Amount::new(50), Amount::new(99));
        assert!(result.is_ok());
    }

    #[test]
    fn effective_price_round_up() {
        let Ok(r) = SwapResult::new(Amount::new(3), Amount::new(10), Amount::new(1)) else {
            panic!("expected Ok");
        };
        let Ok(p) = r.effective_price(Rounding::Up) else {
            panic!("expected Ok");
        };
        // 10 / 3 = 3.333...
        assert!(p.get() > 3.0);
    }

    #[test]
    fn debug_format() {
        let Ok(r) = SwapResult::new(Amount::new(100), Amount::new(90), Amount::new(3)) else {
            panic!("expected Ok");
        };
        let dbg = format!("{r:?}");
        assert!(dbg.contains("SwapResult"));
    }

    #[test]
    fn slippage_large_deviation() {
        // effective price = 100/100 = 1.0, ref = 2.0 => |1.0 - 2.0| / 2.0 * 100 = 50%
        let Ok(r) = SwapResult::new(Amount::new(100), Amount::new(100), Amount::new(1)) else {
            panic!("expected Ok");
        };
        let Ok(ref_price) = Price::new(2.0) else {
            panic!("expected Ok");
        };
        let Ok(slippage) = r.slippage_percent(ref_price, Rounding::Down) else {
            panic!("expected Ok");
        };
        assert!((slippage - 50.0).abs() < 0.01);
    }
}
