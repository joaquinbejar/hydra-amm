//! Token decimal places.

use crate::error::AmmError;

/// Maximum allowed decimal places (EVM standard).
const MAX_DECIMALS: u8 = 18;

/// Represents the number of decimal places for a token amount.
///
/// Valid range is `0..=18`, matching the common blockchain standard.
/// Construction is validated: values above 18 are rejected.
///
/// # Examples
///
/// ```
/// use hydra_amm::domain::Decimals;
///
/// let d = Decimals::new(6).expect("6 is valid");
/// assert_eq!(d.get(), 6);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Decimals(u8);

impl Default for Decimals {
    fn default() -> Self {
        Self::ZERO
    }
}

impl Decimals {
    /// Zero decimal places.
    pub const ZERO: Self = Self(0);

    /// Maximum standard decimal places (18).
    pub const MAX: Self = Self(MAX_DECIMALS);

    /// Creates a new `Decimals` value after validating the range.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::InvalidPrecision`] if `value` exceeds 18.
    pub const fn new(value: u8) -> Result<Self, AmmError> {
        if value > MAX_DECIMALS {
            return Err(AmmError::InvalidPrecision("decimals must be 0..=18"));
        }
        Ok(Self(value))
    }

    /// Returns the raw decimal count.
    #[must_use]
    pub const fn get(&self) -> u8 {
        self.0
    }

    /// Converts a human-readable amount to the smallest raw unit.
    ///
    /// For example, with `decimals = 6`, an input of `1` yields `1_000_000`.
    ///
    /// This operation cannot overflow because `u64::MAX * 10^18 < u128::MAX`.
    #[must_use]
    pub const fn scale_up(&self, amount: u64) -> u128 {
        (amount as u128) * self.factor()
    }

    /// Converts raw units back to a human-readable amount.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::Overflow`] if the result does not fit in `u64`.
    pub const fn scale_down(&self, raw: u128) -> Result<u64, AmmError> {
        let result = raw / self.factor();
        if result > u64::MAX as u128 {
            return Err(AmmError::Overflow("scale_down result exceeds u64"));
        }
        Ok(result as u64)
    }

    /// Returns `10^decimals` as `u128`.
    #[must_use]
    const fn factor(&self) -> u128 {
        10u128.pow(self.0 as u32)
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;

    #[test]
    fn valid_zero() {
        let Ok(d) = Decimals::new(0) else {
            panic!("expected Ok");
        };
        assert_eq!(d.get(), 0);
    }

    #[test]
    fn valid_six() {
        let Ok(d) = Decimals::new(6) else {
            panic!("expected Ok");
        };
        assert_eq!(d.get(), 6);
    }

    #[test]
    fn valid_eighteen() {
        let Ok(d) = Decimals::new(18) else {
            panic!("expected Ok");
        };
        assert_eq!(d.get(), 18);
    }

    #[test]
    fn invalid_nineteen() {
        let Err(e) = Decimals::new(19) else {
            panic!("expected Err");
        };
        assert_eq!(e, AmmError::InvalidPrecision("decimals must be 0..=18"));
    }

    #[test]
    fn invalid_max_u8() {
        let d = Decimals::new(u8::MAX);
        assert!(d.is_err());
    }

    #[test]
    fn constants() {
        assert_eq!(Decimals::ZERO.get(), 0);
        assert_eq!(Decimals::MAX.get(), 18);
    }

    #[test]
    fn default_is_zero() {
        assert_eq!(Decimals::default(), Decimals::ZERO);
    }

    #[test]
    fn scale_up_usdc() {
        let Ok(d) = Decimals::new(6) else {
            panic!("expected Ok");
        };
        assert_eq!(d.scale_up(1), 1_000_000);
    }

    #[test]
    fn scale_up_eth() {
        let Ok(d) = Decimals::new(18) else {
            panic!("expected Ok");
        };
        assert_eq!(d.scale_up(1), 1_000_000_000_000_000_000);
    }

    #[test]
    fn scale_up_zero_decimals() {
        let d = Decimals::ZERO;
        assert_eq!(d.scale_up(42), 42);
    }

    #[test]
    fn scale_down_usdc() {
        let Ok(d) = Decimals::new(6) else {
            panic!("expected Ok");
        };
        assert_eq!(d.scale_down(1_000_000), Ok(1));
    }

    #[test]
    fn scale_down_with_remainder_truncates() {
        let Ok(d) = Decimals::new(6) else {
            panic!("expected Ok");
        };
        assert_eq!(d.scale_down(1_500_000), Ok(1));
    }

    #[test]
    fn scale_round_trip() {
        let Ok(d) = Decimals::new(8) else {
            panic!("expected Ok");
        };
        let raw = d.scale_up(100);
        assert_eq!(d.scale_down(raw), Ok(100));
    }

    #[test]
    fn ordering() {
        let (Ok(d6), Ok(d18)) = (Decimals::new(6), Decimals::new(18)) else {
            panic!("expected Ok");
        };
        assert!(d6 < d18);
    }
}
