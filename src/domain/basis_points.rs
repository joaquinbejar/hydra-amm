//! Basis-point representation for percentages.

use core::fmt;

use super::{Amount, Rounding};
use crate::error::AmmError;

/// Maximum value that represents 100%.
const MAX_BPS: u32 = 10_000;

/// A percentage expressed in basis points (1 bp = 0.01%, 10 000 bp = 100%).
///
/// All `u32` values are technically valid, but values above 10 000 are
/// nonsensical as percentages. Use [`is_valid_percent`](Self::is_valid_percent)
/// to check.
///
/// # Examples
///
/// ```
/// use hydra_amm::domain::BasisPoints;
///
/// let bp = BasisPoints::new(30);
/// assert_eq!(bp.get(), 30);
/// assert!(bp.is_valid_percent());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct BasisPoints(u32);

impl BasisPoints {
    /// Zero basis points (0%).
    pub const ZERO: Self = Self(0);

    /// 100% expressed in basis points.
    pub const MAX_PERCENT: Self = Self(MAX_BPS);

    /// Creates a new `BasisPoints` from a raw `u32` value.
    pub const fn new(value: u32) -> Self {
        Self(value)
    }

    /// Returns the underlying `u32` value.
    #[must_use]
    pub const fn get(&self) -> u32 {
        self.0
    }

    /// Returns `true` if the value is in the valid percentage range (`0..=10_000`).
    #[must_use]
    pub const fn is_valid_percent(&self) -> bool {
        self.0 <= MAX_BPS
    }

    /// Converts to a floating-point percentage in the range `0.0..=100.0`.
    ///
    /// For example, 30 bp → 0.30%.
    #[must_use]
    pub fn as_percent(&self) -> f64 {
        self.0 as f64 / 100.0
    }

    /// Computes `amount * (self / 10_000)` with explicit rounding.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::Overflow`] if the intermediate multiplication overflows.
    pub const fn apply(&self, amount: Amount, rounding: Rounding) -> crate::error::Result<Amount> {
        let bps = self.0 as u128;
        let raw = amount.get();

        let product = match raw.checked_mul(bps) {
            Some(v) => v,
            None => return Err(AmmError::Overflow("basis points apply overflow")),
        };

        let divisor = MAX_BPS as u128;

        match rounding {
            Rounding::Down => Ok(Amount::new(product / divisor)),
            Rounding::Up => {
                // Ceiling: (product + divisor - 1) / divisor
                // divisor is 10_000, so (divisor - 1) is small; overflow here
                // is only possible when product is extremely close to u128::MAX.
                match product.checked_add(divisor - 1) {
                    Some(n) => Ok(Amount::new(n / divisor)),
                    None => {
                        let q = product / divisor;
                        let r = product % divisor;
                        if r != 0 {
                            Ok(Amount::new(q + 1))
                        } else {
                            Ok(Amount::new(q))
                        }
                    }
                }
            }
        }
    }
}

impl fmt::Display for BasisPoints {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}bp", self.0)
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;

    #[test]
    fn new_and_get() {
        assert_eq!(BasisPoints::new(30).get(), 30);
    }

    #[test]
    fn constants() {
        assert_eq!(BasisPoints::ZERO.get(), 0);
        assert_eq!(BasisPoints::MAX_PERCENT.get(), 10_000);
    }

    #[test]
    fn default_is_zero() {
        assert_eq!(BasisPoints::default(), BasisPoints::ZERO);
    }

    #[test]
    fn is_valid_percent_in_range() {
        assert!(BasisPoints::ZERO.is_valid_percent());
        assert!(BasisPoints::new(5_000).is_valid_percent());
        assert!(BasisPoints::MAX_PERCENT.is_valid_percent());
    }

    #[test]
    fn is_valid_percent_out_of_range() {
        assert!(!BasisPoints::new(10_001).is_valid_percent());
        assert!(!BasisPoints::new(u32::MAX).is_valid_percent());
    }

    #[test]
    fn as_percent_thirty_bp() {
        let bp = BasisPoints::new(30);
        let pct = bp.as_percent();
        assert!((pct - 0.30).abs() < f64::EPSILON);
    }

    #[test]
    fn as_percent_one_hundred() {
        let bp = BasisPoints::MAX_PERCENT;
        let pct = bp.as_percent();
        assert!((pct - 100.0).abs() < f64::EPSILON);
    }

    #[test]
    fn display() {
        assert_eq!(format!("{}", BasisPoints::new(30)), "30bp");
    }

    #[test]
    fn ordering() {
        assert!(BasisPoints::new(1) < BasisPoints::new(5));
    }

    // -- apply --------------------------------------------------------------

    #[test]
    fn apply_round_down() {
        // 30bp of 1_000_000 = 1_000_000 * 30 / 10_000 = 3_000
        let bp = BasisPoints::new(30);
        let amount = Amount::new(1_000_000);
        let Ok(result) = bp.apply(amount, Rounding::Down) else {
            panic!("expected Ok");
        };
        assert_eq!(result, Amount::new(3_000));
    }

    #[test]
    fn apply_round_up_exact() {
        // 100bp of 10_000 = 10_000 * 100 / 10_000 = 100 (exact)
        let bp = BasisPoints::new(100);
        let amount = Amount::new(10_000);
        let Ok(result) = bp.apply(amount, Rounding::Up) else {
            panic!("expected Ok");
        };
        assert_eq!(result, Amount::new(100));
    }

    #[test]
    fn apply_round_up_remainder() {
        // 30bp of 1 = 1 * 30 / 10_000 = 0.003 → ceil = 1
        let bp = BasisPoints::new(30);
        let amount = Amount::new(1);
        let Ok(result) = bp.apply(amount, Rounding::Up) else {
            panic!("expected Ok");
        };
        assert_eq!(result, Amount::new(1));
    }

    #[test]
    fn apply_round_down_remainder() {
        // 30bp of 1 = 1 * 30 / 10_000 = 0.003 → floor = 0
        let bp = BasisPoints::new(30);
        let amount = Amount::new(1);
        let Ok(result) = bp.apply(amount, Rounding::Down) else {
            panic!("expected Ok");
        };
        assert_eq!(result, Amount::ZERO);
    }

    #[test]
    fn apply_zero_amount() {
        let bp = BasisPoints::new(30);
        let Ok(result) = bp.apply(Amount::ZERO, Rounding::Down) else {
            panic!("expected Ok");
        };
        assert_eq!(result, Amount::ZERO);
    }

    #[test]
    fn apply_zero_bp() {
        let bp = BasisPoints::ZERO;
        let Ok(result) = bp.apply(Amount::new(1_000_000), Rounding::Down) else {
            panic!("expected Ok");
        };
        assert_eq!(result, Amount::ZERO);
    }

    #[test]
    fn apply_overflow() {
        let bp = BasisPoints::new(u32::MAX);
        let amount = Amount::MAX;
        let result = bp.apply(amount, Rounding::Down);
        assert!(result.is_err());
    }

    // -- Copy ---------------------------------------------------------------

    #[test]
    fn copy_semantics() {
        let a = BasisPoints::new(30);
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
        let a = BasisPoints::new(30);
        let b = BasisPoints::new(30);
        assert_eq!(hash_of(&a), hash_of(&b));
    }

    #[test]
    fn apply_100_percent() {
        // 10_000bp of 1_000 = 1_000 (full amount)
        let bp = BasisPoints::MAX_PERCENT;
        let Ok(result) = bp.apply(Amount::new(1_000), Rounding::Down) else {
            panic!("expected Ok");
        };
        assert_eq!(result, Amount::new(1_000));
    }

    #[test]
    fn apply_50_percent() {
        // 5_000bp of 1_000 = 500
        let bp = BasisPoints::new(5_000);
        let Ok(result) = bp.apply(Amount::new(1_000), Rounding::Down) else {
            panic!("expected Ok");
        };
        assert_eq!(result, Amount::new(500));
    }

    #[test]
    fn debug_format() {
        let bp = BasisPoints::new(30);
        let dbg = format!("{bp:?}");
        assert!(dbg.contains("BasisPoints"));
    }

    #[test]
    fn as_percent_zero() {
        assert!((BasisPoints::ZERO.as_percent() - 0.0).abs() < f64::EPSILON);
    }
}
