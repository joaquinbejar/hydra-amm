//! Raw token amount with checked arithmetic.

use core::fmt;

use super::Rounding;

/// A raw token amount in the smallest unit (wei, satoshi, or equivalent).
///
/// `Amount` never interprets decimals — that responsibility lies with
/// [`Token`](super::Token). All `u128` values are valid amounts.
///
/// Arithmetic methods are checked: they return `None` on overflow,
/// underflow, or division by zero instead of panicking.
///
/// # Examples
///
/// ```
/// use hydra_amm::domain::{Amount, Rounding};
///
/// let a = Amount::new(100);
/// let b = Amount::new(200);
/// assert_eq!(a.checked_add(&b), Some(Amount::new(300)));
/// assert_eq!(b.checked_sub(&a), Some(Amount::new(100)));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[must_use]
pub struct Amount(u128);

impl Amount {
    /// Zero amount.
    pub const ZERO: Self = Self(0);

    /// Maximum representable amount.
    pub const MAX: Self = Self(u128::MAX);

    /// Creates a new `Amount` from a raw `u128` value.
    pub const fn new(value: u128) -> Self {
        Self(value)
    }

    /// Returns the underlying `u128` value.
    #[must_use]
    pub const fn get(&self) -> u128 {
        self.0
    }

    /// Returns `true` if the amount is zero.
    #[must_use]
    pub const fn is_zero(&self) -> bool {
        self.0 == 0
    }

    /// Checked addition. Returns `None` on overflow.
    #[must_use]
    pub const fn checked_add(&self, other: &Self) -> Option<Self> {
        match self.0.checked_add(other.0) {
            Some(v) => Some(Self(v)),
            None => None,
        }
    }

    /// Checked subtraction. Returns `None` on underflow.
    #[must_use]
    pub const fn checked_sub(&self, other: &Self) -> Option<Self> {
        match self.0.checked_sub(other.0) {
            Some(v) => Some(Self(v)),
            None => None,
        }
    }

    /// Checked multiplication. Returns `None` on overflow.
    #[must_use]
    pub const fn checked_mul(&self, other: &Self) -> Option<Self> {
        match self.0.checked_mul(other.0) {
            Some(v) => Some(Self(v)),
            None => None,
        }
    }

    /// Checked division with explicit rounding direction.
    ///
    /// - [`Rounding::Down`]: floor division (round towards zero).
    /// - [`Rounding::Up`]: ceiling division — `(n + d - 1) / d`.
    ///
    /// Returns `None` if `divisor` is zero.
    #[must_use]
    pub const fn checked_div(&self, divisor: &Self, rounding: Rounding) -> Option<Self> {
        if divisor.0 == 0 {
            return None;
        }
        match rounding {
            Rounding::Down => Some(Self(self.0 / divisor.0)),
            Rounding::Up => {
                // Ceiling division: (n + d - 1) / d
                // Safe because divisor > 0 guarantees (divisor.0 - 1) does not underflow.
                let numerator = match self.0.checked_add(divisor.0 - 1) {
                    Some(v) => v,
                    None => {
                        // Overflow in (n + d - 1).  Fall back to:
                        //   ceil(n / d) = floor(n / d) + (n % d != 0) as u128
                        let q = self.0 / divisor.0;
                        let r = self.0 % divisor.0;
                        if r != 0 {
                            // q + 1 cannot overflow because n < u128::MAX when r != 0
                            // (if n == u128::MAX and d == 1 then r == 0).
                            return Some(Self(q + 1));
                        }
                        return Some(Self(q));
                    }
                };
                Some(Self(numerator / divisor.0))
            }
        }
    }
}

impl fmt::Display for Amount {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;

    // -- Construction & accessors -------------------------------------------

    #[test]
    fn new_and_get() {
        let a = Amount::new(42);
        assert_eq!(a.get(), 42);
    }

    #[test]
    fn constants() {
        assert_eq!(Amount::ZERO.get(), 0);
        assert_eq!(Amount::MAX.get(), u128::MAX);
    }

    #[test]
    fn default_is_zero() {
        assert_eq!(Amount::default(), Amount::ZERO);
    }

    #[test]
    fn is_zero_true() {
        assert!(Amount::ZERO.is_zero());
    }

    #[test]
    fn is_zero_false() {
        assert!(!Amount::new(1).is_zero());
    }

    // -- Display ------------------------------------------------------------

    #[test]
    fn display() {
        assert_eq!(format!("{}", Amount::new(1_000_000)), "1000000");
    }

    // -- Ordering -----------------------------------------------------------

    #[test]
    fn ordering() {
        assert!(Amount::new(1) < Amount::new(2));
        assert!(Amount::new(2) > Amount::new(1));
        assert_eq!(Amount::new(5), Amount::new(5));
    }

    // -- checked_add --------------------------------------------------------

    #[test]
    fn add_normal() {
        let a = Amount::new(100);
        let b = Amount::new(200);
        assert_eq!(a.checked_add(&b), Some(Amount::new(300)));
    }

    #[test]
    fn add_zero() {
        let a = Amount::new(42);
        assert_eq!(a.checked_add(&Amount::ZERO), Some(a));
    }

    #[test]
    fn add_overflow() {
        let a = Amount::MAX;
        let b = Amount::new(1);
        assert_eq!(a.checked_add(&b), None);
    }

    // -- checked_sub --------------------------------------------------------

    #[test]
    fn sub_normal() {
        let a = Amount::new(300);
        let b = Amount::new(100);
        assert_eq!(a.checked_sub(&b), Some(Amount::new(200)));
    }

    #[test]
    fn sub_to_zero() {
        let a = Amount::new(42);
        assert_eq!(a.checked_sub(&a), Some(Amount::ZERO));
    }

    #[test]
    fn sub_underflow() {
        let a = Amount::new(1);
        let b = Amount::new(2);
        assert_eq!(a.checked_sub(&b), None);
    }

    // -- checked_mul --------------------------------------------------------

    #[test]
    fn mul_normal() {
        let a = Amount::new(100);
        let b = Amount::new(200);
        assert_eq!(a.checked_mul(&b), Some(Amount::new(20_000)));
    }

    #[test]
    fn mul_by_zero() {
        assert_eq!(
            Amount::new(42).checked_mul(&Amount::ZERO),
            Some(Amount::ZERO)
        );
    }

    #[test]
    fn mul_by_one() {
        let a = Amount::new(42);
        assert_eq!(a.checked_mul(&Amount::new(1)), Some(a));
    }

    #[test]
    fn mul_overflow() {
        let a = Amount::MAX;
        let b = Amount::new(2);
        assert_eq!(a.checked_mul(&b), None);
    }

    // -- checked_div --------------------------------------------------------

    #[test]
    fn div_exact_round_down() {
        let a = Amount::new(100);
        let d = Amount::new(10);
        assert_eq!(a.checked_div(&d, Rounding::Down), Some(Amount::new(10)));
    }

    #[test]
    fn div_exact_round_up() {
        let a = Amount::new(100);
        let d = Amount::new(10);
        assert_eq!(a.checked_div(&d, Rounding::Up), Some(Amount::new(10)));
    }

    #[test]
    fn div_remainder_round_down() {
        let a = Amount::new(10);
        let d = Amount::new(3);
        assert_eq!(a.checked_div(&d, Rounding::Down), Some(Amount::new(3)));
    }

    #[test]
    fn div_remainder_round_up() {
        let a = Amount::new(10);
        let d = Amount::new(3);
        assert_eq!(a.checked_div(&d, Rounding::Up), Some(Amount::new(4)));
    }

    #[test]
    fn div_by_zero() {
        let a = Amount::new(100);
        assert_eq!(a.checked_div(&Amount::ZERO, Rounding::Down), None);
        assert_eq!(a.checked_div(&Amount::ZERO, Rounding::Up), None);
    }

    #[test]
    fn div_zero_numerator() {
        let d = Amount::new(10);
        assert_eq!(
            Amount::ZERO.checked_div(&d, Rounding::Down),
            Some(Amount::ZERO)
        );
        assert_eq!(
            Amount::ZERO.checked_div(&d, Rounding::Up),
            Some(Amount::ZERO)
        );
    }

    #[test]
    fn div_by_one() {
        let a = Amount::new(42);
        assert_eq!(a.checked_div(&Amount::new(1), Rounding::Down), Some(a));
        assert_eq!(a.checked_div(&Amount::new(1), Rounding::Up), Some(a));
    }

    #[test]
    fn div_max_round_up_overflow_path() {
        // u128::MAX / 2 with remainder should exercise the overflow fallback
        // in ceiling division: (MAX + 1) would overflow.
        let a = Amount::MAX;
        let d = Amount::new(2);
        // floor(MAX / 2) = (2^128 - 1) / 2 = 2^127 - 1 (170141183460469231731687303715884105727)
        // ceil(MAX / 2) = floor + 1
        let floor = a.checked_div(&d, Rounding::Down);
        let ceil = a.checked_div(&d, Rounding::Up);
        let Ok(expected_floor) = u128::MAX.checked_div(2).ok_or(()) else {
            panic!("u128 div");
        };
        assert_eq!(floor, Some(Amount::new(expected_floor)));
        assert_eq!(ceil, Some(Amount::new(expected_floor + 1)));
    }

    #[test]
    fn div_max_by_max() {
        let a = Amount::MAX;
        assert_eq!(a.checked_div(&a, Rounding::Down), Some(Amount::new(1)));
        assert_eq!(a.checked_div(&a, Rounding::Up), Some(Amount::new(1)));
    }

    // -- Copy semantics -----------------------------------------------------

    #[test]
    fn copy_semantics() {
        let a = Amount::new(99);
        let b = a;
        assert_eq!(a, b);
    }

    #[test]
    fn debug_format() {
        let a = Amount::new(42);
        let dbg = format!("{a:?}");
        assert!(dbg.contains("Amount"));
        assert!(dbg.contains("42"));
    }

    #[test]
    fn hash_consistency() {
        use core::hash::{Hash, Hasher};
        fn hash_of<T: Hash>(t: &T) -> u64 {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            t.hash(&mut h);
            h.finish()
        }
        let a = Amount::new(100);
        let b = Amount::new(100);
        assert_eq!(hash_of(&a), hash_of(&b));
    }

    #[test]
    fn mul_identity() {
        let a = Amount::new(999);
        assert_eq!(a.checked_mul(&Amount::new(1)), Some(a));
    }

    #[test]
    fn sub_zero_identity() {
        let a = Amount::new(42);
        assert_eq!(a.checked_sub(&Amount::ZERO), Some(a));
    }

    #[test]
    fn div_larger_divisor_round_down() {
        // 1 / 2 = 0 (floor)
        assert_eq!(
            Amount::new(1).checked_div(&Amount::new(2), Rounding::Down),
            Some(Amount::ZERO)
        );
    }

    #[test]
    fn div_larger_divisor_round_up() {
        // 1 / 2 = 1 (ceil)
        assert_eq!(
            Amount::new(1).checked_div(&Amount::new(2), Rounding::Up),
            Some(Amount::new(1))
        );
    }
}
