//! Liquidity units for concentrated positions.

use core::fmt;

use super::Amount;

/// Liquidity units in a concentrated position.
///
/// This is distinct from [`Amount`] because it measures the amount of
/// liquidity available in a price range, not the amount of a specific token.
/// All `u128` values are valid liquidity amounts.
///
/// # Examples
///
/// ```
/// use hydra_amm::domain::Liquidity;
///
/// let a = Liquidity::new(1_000);
/// let b = Liquidity::new(2_000);
/// assert_eq!(a.checked_add(&b), Some(Liquidity::new(3_000)));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Liquidity(u128);

impl Liquidity {
    /// No liquidity.
    pub const ZERO: Self = Self(0);

    /// Creates a new `Liquidity` from a raw `u128` value.
    pub const fn new(value: u128) -> Self {
        Self(value)
    }

    /// Returns the underlying `u128` value.
    #[must_use]
    pub const fn get(&self) -> u128 {
        self.0
    }

    /// Returns `true` if the liquidity is zero.
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

    /// Scales an [`Amount`] by this liquidity value.
    ///
    /// Returns `None` on overflow.
    #[must_use]
    pub const fn checked_mul_amount(&self, amount: &Amount) -> Option<Amount> {
        match self.0.checked_mul(amount.get()) {
            Some(v) => Some(Amount::new(v)),
            None => None,
        }
    }
}

impl fmt::Display for Liquidity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;

    #[test]
    fn new_and_get() {
        assert_eq!(Liquidity::new(42).get(), 42);
    }

    #[test]
    fn zero_constant() {
        assert_eq!(Liquidity::ZERO.get(), 0);
        assert!(Liquidity::ZERO.is_zero());
    }

    #[test]
    fn default_is_zero() {
        assert_eq!(Liquidity::default(), Liquidity::ZERO);
    }

    #[test]
    fn is_zero_false() {
        assert!(!Liquidity::new(1).is_zero());
    }

    #[test]
    fn display() {
        assert_eq!(format!("{}", Liquidity::new(1_000)), "1000");
    }

    #[test]
    fn ordering() {
        assert!(Liquidity::new(1) < Liquidity::new(2));
    }

    // -- checked_add --------------------------------------------------------

    #[test]
    fn add_normal() {
        let a = Liquidity::new(100);
        let b = Liquidity::new(200);
        assert_eq!(a.checked_add(&b), Some(Liquidity::new(300)));
    }

    #[test]
    fn add_zero() {
        let a = Liquidity::new(42);
        assert_eq!(a.checked_add(&Liquidity::ZERO), Some(a));
    }

    #[test]
    fn add_overflow() {
        let a = Liquidity::new(u128::MAX);
        assert_eq!(a.checked_add(&Liquidity::new(1)), None);
    }

    // -- checked_sub --------------------------------------------------------

    #[test]
    fn sub_normal() {
        let a = Liquidity::new(300);
        let b = Liquidity::new(100);
        assert_eq!(a.checked_sub(&b), Some(Liquidity::new(200)));
    }

    #[test]
    fn sub_to_zero() {
        let a = Liquidity::new(42);
        assert_eq!(a.checked_sub(&a), Some(Liquidity::ZERO));
    }

    #[test]
    fn sub_underflow() {
        let a = Liquidity::new(1);
        assert_eq!(a.checked_sub(&Liquidity::new(2)), None);
    }

    // -- checked_mul_amount -------------------------------------------------

    #[test]
    fn mul_amount_normal() {
        let l = Liquidity::new(100);
        let a = Amount::new(50);
        assert_eq!(l.checked_mul_amount(&a), Some(Amount::new(5_000)));
    }

    #[test]
    fn mul_amount_zero() {
        let l = Liquidity::new(100);
        assert_eq!(l.checked_mul_amount(&Amount::ZERO), Some(Amount::ZERO));
    }

    #[test]
    fn mul_amount_overflow() {
        let l = Liquidity::new(u128::MAX);
        let a = Amount::new(2);
        assert_eq!(l.checked_mul_amount(&a), None);
    }

    // -- Copy ---------------------------------------------------------------

    #[test]
    fn copy_semantics() {
        let a = Liquidity::new(99);
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
        let a = Liquidity::new(500);
        let b = Liquidity::new(500);
        assert_eq!(hash_of(&a), hash_of(&b));
    }

    #[test]
    fn debug_format() {
        let l = Liquidity::new(42);
        let dbg = format!("{l:?}");
        assert!(dbg.contains("Liquidity"));
    }

    #[test]
    fn mul_amount_by_one() {
        let l = Liquidity::new(1);
        let a = Amount::new(999);
        assert_eq!(l.checked_mul_amount(&a), Some(a));
    }

    #[test]
    fn sub_to_zero_is_zero() {
        let l = Liquidity::new(42);
        assert_eq!(l.checked_sub(&l), Some(Liquidity::ZERO));
        assert!(l.checked_sub(&l).is_some_and(|v| v.is_zero()));
    }
}
