//! Discrete price point for concentrated liquidity models.

use core::fmt;

use crate::error::AmmError;

/// Minimum valid tick index (Uniswap v3 standard).
const MIN_TICK: i32 = -887_272;

/// Maximum valid tick index (Uniswap v3 standard).
const MAX_TICK: i32 = 887_272;

/// A discrete price point in the concentrated liquidity model.
///
/// Follows the Uniswap v3 convention where price increases exponentially
/// with the tick index: `price = 1.0001^tick`. Valid tick indices range
/// from [`MIN`](Self::MIN) (`-887272`) to [`MAX`](Self::MAX) (`887272`).
///
/// # Examples
///
/// ```
/// use hydra_amm::domain::Tick;
///
/// let tick = Tick::new(100);
/// assert!(tick.is_ok());
/// assert_eq!(tick.unwrap_or(Tick::ZERO).get(), 100);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Tick(i32);

impl Tick {
    /// Minimum valid tick (`-887272`).
    pub const MIN: Self = Self(MIN_TICK);

    /// Maximum valid tick (`887272`).
    pub const MAX: Self = Self(MAX_TICK);

    /// Neutral tick where `price = 1.0001^0 = 1.0`.
    pub const ZERO: Self = Self(0);

    /// Creates a new `Tick` with range validation.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::InvalidTick`] if `value` is outside
    /// the range `[-887272, 887272]`.
    pub const fn new(value: i32) -> crate::error::Result<Self> {
        if value < MIN_TICK || value > MAX_TICK {
            return Err(AmmError::InvalidTick("tick out of range [-887272, 887272]"));
        }
        Ok(Self(value))
    }

    /// Returns the underlying `i32` tick index.
    #[must_use]
    pub const fn get(&self) -> i32 {
        self.0
    }

    /// Returns `true` if this tick is within the valid range.
    ///
    /// Always returns `true` for a properly constructed `Tick`.
    #[must_use]
    pub const fn is_valid(&self) -> bool {
        self.0 >= MIN_TICK && self.0 <= MAX_TICK
    }

    /// Checked addition of a delta to this tick.
    ///
    /// Returns `None` if the result would be outside the valid tick range.
    #[must_use]
    pub const fn checked_add(&self, delta: i32) -> Option<Self> {
        match self.0.checked_add(delta) {
            Some(v) if v >= MIN_TICK && v <= MAX_TICK => Some(Self(v)),
            _ => None,
        }
    }

    /// Checked subtraction of a delta from this tick.
    ///
    /// Returns `None` if the result would be outside the valid tick range.
    #[must_use]
    pub const fn checked_sub(&self, delta: i32) -> Option<Self> {
        match self.0.checked_sub(delta) {
            Some(v) if v >= MIN_TICK && v <= MAX_TICK => Some(Self(v)),
            _ => None,
        }
    }

    /// Returns `true` if the given tick spacing is valid (non-zero).
    ///
    /// A spacing of zero would result in an infinite number of ticks and
    /// is therefore invalid.
    #[must_use]
    pub const fn spacing_is_valid(spacing: u16) -> bool {
        spacing > 0
    }
}

impl fmt::Display for Tick {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Tick({})", self.0)
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;

    // -- Construction -------------------------------------------------------

    #[test]
    fn valid_zero() {
        let Ok(t) = Tick::new(0) else {
            panic!("expected Ok");
        };
        assert_eq!(t.get(), 0);
    }

    #[test]
    fn valid_min() {
        let Ok(t) = Tick::new(-887_272) else {
            panic!("expected Ok");
        };
        assert_eq!(t, Tick::MIN);
    }

    #[test]
    fn valid_max() {
        let Ok(t) = Tick::new(887_272) else {
            panic!("expected Ok");
        };
        assert_eq!(t, Tick::MAX);
    }

    #[test]
    fn valid_positive() {
        let Ok(t) = Tick::new(1_000) else {
            panic!("expected Ok");
        };
        assert_eq!(t.get(), 1_000);
    }

    #[test]
    fn valid_negative() {
        let Ok(t) = Tick::new(-500_000) else {
            panic!("expected Ok");
        };
        assert_eq!(t.get(), -500_000);
    }

    #[test]
    fn invalid_below_min() {
        let Err(e) = Tick::new(-887_273) else {
            panic!("expected Err");
        };
        assert_eq!(
            e,
            AmmError::InvalidTick("tick out of range [-887272, 887272]")
        );
    }

    #[test]
    fn invalid_above_max() {
        let Err(e) = Tick::new(887_273) else {
            panic!("expected Err");
        };
        assert_eq!(
            e,
            AmmError::InvalidTick("tick out of range [-887272, 887272]")
        );
    }

    #[test]
    fn invalid_i32_min() {
        assert!(Tick::new(i32::MIN).is_err());
    }

    #[test]
    fn invalid_i32_max() {
        assert!(Tick::new(i32::MAX).is_err());
    }

    // -- Constants ----------------------------------------------------------

    #[test]
    fn constants() {
        assert_eq!(Tick::MIN.get(), -887_272);
        assert_eq!(Tick::MAX.get(), 887_272);
        assert_eq!(Tick::ZERO.get(), 0);
    }

    #[test]
    fn constants_are_valid() {
        assert!(Tick::MIN.is_valid());
        assert!(Tick::MAX.is_valid());
        assert!(Tick::ZERO.is_valid());
    }

    // -- checked_add --------------------------------------------------------

    #[test]
    fn add_normal() {
        let t = Tick::ZERO;
        assert_eq!(t.checked_add(100), Some(Tick(100)));
    }

    #[test]
    fn add_negative_delta() {
        let t = Tick::ZERO;
        assert_eq!(t.checked_add(-100), Some(Tick(-100)));
    }

    #[test]
    fn add_stays_at_max() {
        let Ok(t) = Tick::new(887_271) else {
            panic!("expected Ok");
        };
        assert_eq!(t.checked_add(1), Some(Tick::MAX));
    }

    #[test]
    fn add_exceeds_max() {
        assert_eq!(Tick::MAX.checked_add(1), None);
    }

    #[test]
    fn add_exceeds_min() {
        assert_eq!(Tick::MIN.checked_add(-1), None);
    }

    #[test]
    fn add_zero() {
        let t = Tick(42);
        assert_eq!(t.checked_add(0), Some(t));
    }

    // -- checked_sub --------------------------------------------------------

    #[test]
    fn sub_normal() {
        let t = Tick::ZERO;
        assert_eq!(t.checked_sub(100), Some(Tick(-100)));
    }

    #[test]
    fn sub_negative_delta() {
        let t = Tick::ZERO;
        assert_eq!(t.checked_sub(-100), Some(Tick(100)));
    }

    #[test]
    fn sub_stays_at_min() {
        let Ok(t) = Tick::new(-887_271) else {
            panic!("expected Ok");
        };
        assert_eq!(t.checked_sub(1), Some(Tick::MIN));
    }

    #[test]
    fn sub_exceeds_min() {
        assert_eq!(Tick::MIN.checked_sub(1), None);
    }

    #[test]
    fn sub_exceeds_max() {
        assert_eq!(Tick::MAX.checked_sub(-1), None);
    }

    #[test]
    fn sub_zero() {
        let t = Tick(42);
        assert_eq!(t.checked_sub(0), Some(t));
    }

    // -- spacing_is_valid ---------------------------------------------------

    #[test]
    fn spacing_valid() {
        assert!(Tick::spacing_is_valid(1));
        assert!(Tick::spacing_is_valid(10));
        assert!(Tick::spacing_is_valid(60));
        assert!(Tick::spacing_is_valid(200));
    }

    #[test]
    fn spacing_zero_invalid() {
        assert!(!Tick::spacing_is_valid(0));
    }

    // -- Display ------------------------------------------------------------

    #[test]
    fn display() {
        assert_eq!(format!("{}", Tick::ZERO), "Tick(0)");
        assert_eq!(format!("{}", Tick::MIN), "Tick(-887272)");
    }

    // -- Ordering -----------------------------------------------------------

    #[test]
    fn ordering() {
        assert!(Tick::MIN < Tick::ZERO);
        assert!(Tick::ZERO < Tick::MAX);
    }

    // -- Copy ---------------------------------------------------------------

    #[test]
    fn copy_semantics() {
        let a = Tick::ZERO;
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
        let (Ok(a), Ok(b)) = (Tick::new(1000), Tick::new(1000)) else {
            panic!("expected Ok");
        };
        assert_eq!(hash_of(&a), hash_of(&b));
    }

    #[test]
    fn checked_add_i32_overflow() {
        // i32::MAX delta on MAX tick would overflow i32 before range check
        assert_eq!(Tick::MAX.checked_add(i32::MAX), None);
    }

    #[test]
    fn checked_sub_i32_overflow() {
        assert_eq!(Tick::MIN.checked_sub(i32::MAX), None);
    }

    #[test]
    fn display_negative() {
        let Ok(t) = Tick::new(-42) else {
            panic!("expected Ok");
        };
        assert_eq!(format!("{t}"), "Tick(-42)");
    }

    #[test]
    fn spacing_max_u16_valid() {
        assert!(Tick::spacing_is_valid(u16::MAX));
    }
}
