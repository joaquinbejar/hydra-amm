//! Configuration for Order Book hybrid AMM pools (Phoenix style).

use crate::domain::{Amount, FeeTier, TokenPair};
use crate::error::AmmError;

/// Configuration for a hybrid AMM/CLOB (Central Limit Order Book) pool.
///
/// Defines the immutable parameters for a Phoenix-style order book pool:
/// token pair, fee tier, and minimum increments.
///
/// # Constraints
///
/// - All limit orders must be placed at prices that are multiples of `tick_size`.
/// - All quantities must be multiples of `lot_size`.
///
/// # Validation
///
/// - Both `tick_size` and `lot_size` must be non-zero.
/// - The token pair is validated at [`TokenPair`] construction time.
#[derive(Debug, Clone, PartialEq)]
pub struct OrderBookConfig {
    token_pair: TokenPair,
    fee_tier: FeeTier,
    tick_size: Amount,
    lot_size: Amount,
}

impl OrderBookConfig {
    /// Creates a new `OrderBookConfig`.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::InvalidConfiguration`] if `tick_size` or
    /// `lot_size` is zero.
    pub fn new(
        token_pair: TokenPair,
        fee_tier: FeeTier,
        tick_size: Amount,
        lot_size: Amount,
    ) -> Result<Self, AmmError> {
        let config = Self {
            token_pair,
            fee_tier,
            tick_size,
            lot_size,
        };
        config.validate()?;
        Ok(config)
    }

    /// Validates all configuration invariants.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::InvalidConfiguration`] if `tick_size` or
    /// `lot_size` is zero.
    pub fn validate(&self) -> Result<(), AmmError> {
        if self.tick_size.is_zero() {
            return Err(AmmError::InvalidConfiguration("tick size must be non-zero"));
        }
        if self.lot_size.is_zero() {
            return Err(AmmError::InvalidConfiguration("lot size must be non-zero"));
        }
        Ok(())
    }

    /// Returns the token pair.
    #[must_use]
    pub const fn token_pair(&self) -> &TokenPair {
        &self.token_pair
    }

    /// Returns the fee tier.
    #[must_use]
    pub const fn fee_tier(&self) -> FeeTier {
        self.fee_tier
    }

    /// Returns the minimum price increment.
    pub const fn tick_size(&self) -> Amount {
        self.tick_size
    }

    /// Returns the minimum quantity increment.
    pub const fn lot_size(&self) -> Amount {
        self.lot_size
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;
    use crate::domain::{BasisPoints, Decimals, Token, TokenAddress};

    fn make_pair() -> TokenPair {
        let Ok(d6) = Decimals::new(6) else {
            panic!("valid decimals");
        };
        let Ok(d18) = Decimals::new(18) else {
            panic!("valid decimals");
        };
        let tok_a = Token::new(TokenAddress::from_bytes([1u8; 32]), d6);
        let tok_b = Token::new(TokenAddress::from_bytes([2u8; 32]), d18);
        let Ok(pair) = TokenPair::new(tok_a, tok_b) else {
            panic!("expected valid pair");
        };
        pair
    }

    fn fee() -> FeeTier {
        FeeTier::new(BasisPoints::new(30))
    }

    #[test]
    fn valid_config() {
        let result = OrderBookConfig::new(make_pair(), fee(), Amount::new(1), Amount::new(10));
        assert!(result.is_ok());
    }

    #[test]
    fn zero_tick_size_rejected() {
        let result = OrderBookConfig::new(make_pair(), fee(), Amount::ZERO, Amount::new(10));
        assert!(result.is_err());
    }

    #[test]
    fn zero_lot_size_rejected() {
        let result = OrderBookConfig::new(make_pair(), fee(), Amount::new(1), Amount::ZERO);
        assert!(result.is_err());
    }

    #[test]
    fn accessors() {
        let pair = make_pair();
        let f = fee();
        let Ok(cfg) = OrderBookConfig::new(pair, f, Amount::new(5), Amount::new(100)) else {
            panic!("expected Ok");
        };
        assert_eq!(*cfg.token_pair(), pair);
        assert_eq!(cfg.fee_tier(), f);
        assert_eq!(cfg.tick_size(), Amount::new(5));
        assert_eq!(cfg.lot_size(), Amount::new(100));
    }
}
