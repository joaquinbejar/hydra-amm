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
/// - Fee tier must be a valid percentage (0–10 000 basis points).
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
    /// - [`AmmError::InvalidFee`] if the fee tier exceeds 100% (10 000 basis points).
    /// - [`AmmError::InvalidConfiguration`] if `tick_size` or `lot_size` is zero.
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
    /// - [`AmmError::InvalidFee`] if the fee tier exceeds 100% (10 000 basis points).
    /// - [`AmmError::InvalidConfiguration`] if `tick_size` or `lot_size` is zero.
    pub fn validate(&self) -> Result<(), AmmError> {
        if !self.fee_tier.basis_points().is_valid_percent() {
            return Err(AmmError::InvalidFee(
                "fee tier must not exceed 10000 basis points (100%)",
            ));
        }
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

    // -- helpers --------------------------------------------------------------

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

    fn valid_cfg() -> OrderBookConfig {
        let Ok(cfg) = OrderBookConfig::new(make_pair(), fee(), Amount::new(1), Amount::new(10))
        else {
            panic!("expected Ok");
        };
        cfg
    }

    // -- valid construction ---------------------------------------------------

    #[test]
    fn valid_config() {
        let result = OrderBookConfig::new(make_pair(), fee(), Amount::new(1), Amount::new(10));
        assert!(result.is_ok());
    }

    #[test]
    fn valid_with_large_tick_and_lot() {
        let result = OrderBookConfig::new(
            make_pair(),
            fee(),
            Amount::new(u128::MAX),
            Amount::new(u128::MAX),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn valid_with_minimum_sizes() {
        let result = OrderBookConfig::new(make_pair(), fee(), Amount::new(1), Amount::new(1));
        assert!(result.is_ok());
    }

    #[test]
    fn valid_with_standard_fee_tiers() {
        for tier in [
            FeeTier::TIER_0_01_PERCENT,
            FeeTier::TIER_0_05_PERCENT,
            FeeTier::TIER_0_30_PERCENT,
            FeeTier::TIER_1_00_PERCENT,
        ] {
            let result = OrderBookConfig::new(make_pair(), tier, Amount::new(1), Amount::new(10));
            assert!(result.is_ok());
        }
    }

    #[test]
    fn valid_with_zero_fee() {
        let zero_fee = FeeTier::new(BasisPoints::new(0));
        let result = OrderBookConfig::new(make_pair(), zero_fee, Amount::new(1), Amount::new(10));
        assert!(result.is_ok());
    }

    #[test]
    fn valid_with_max_valid_fee() {
        let max_fee = FeeTier::new(BasisPoints::new(10_000));
        let result = OrderBookConfig::new(make_pair(), max_fee, Amount::new(1), Amount::new(10));
        assert!(result.is_ok());
    }

    // -- fee_tier validation --------------------------------------------------

    #[test]
    fn fee_exceeding_100_percent_rejected() {
        let bad_fee = FeeTier::new(BasisPoints::new(10_001));
        let result = OrderBookConfig::new(make_pair(), bad_fee, Amount::new(1), Amount::new(10));
        assert!(matches!(result, Err(AmmError::InvalidFee(_))));
    }

    #[test]
    fn fee_way_above_range_rejected() {
        let bad_fee = FeeTier::new(BasisPoints::new(u32::MAX));
        let result = OrderBookConfig::new(make_pair(), bad_fee, Amount::new(1), Amount::new(10));
        assert!(matches!(result, Err(AmmError::InvalidFee(_))));
    }

    // -- tick_size validation -------------------------------------------------

    #[test]
    fn zero_tick_size_rejected() {
        let result = OrderBookConfig::new(make_pair(), fee(), Amount::ZERO, Amount::new(10));
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    // -- lot_size validation --------------------------------------------------

    #[test]
    fn zero_lot_size_rejected() {
        let result = OrderBookConfig::new(make_pair(), fee(), Amount::new(1), Amount::ZERO);
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    // -- both zero ------------------------------------------------------------

    #[test]
    fn both_sizes_zero_rejected() {
        let result = OrderBookConfig::new(make_pair(), fee(), Amount::ZERO, Amount::ZERO);
        // tick_size checked first
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    // -- validate on existing instance ----------------------------------------

    #[test]
    fn validate_on_valid_config_succeeds() {
        let cfg = valid_cfg();
        assert!(cfg.validate().is_ok());
    }

    // -- accessors ------------------------------------------------------------

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

    // -- Clone & PartialEq ---------------------------------------------------

    #[test]
    fn clone_equality() {
        let cfg = valid_cfg();
        let cloned = cfg.clone();
        assert_eq!(cfg, cloned);
    }

    #[test]
    fn different_tick_size_not_equal() {
        let Ok(a) = OrderBookConfig::new(make_pair(), fee(), Amount::new(1), Amount::new(10))
        else {
            panic!("expected Ok");
        };
        let Ok(b) = OrderBookConfig::new(make_pair(), fee(), Amount::new(5), Amount::new(10))
        else {
            panic!("expected Ok");
        };
        assert_ne!(a, b);
    }

    #[test]
    fn different_lot_size_not_equal() {
        let Ok(a) = OrderBookConfig::new(make_pair(), fee(), Amount::new(1), Amount::new(10))
        else {
            panic!("expected Ok");
        };
        let Ok(b) = OrderBookConfig::new(make_pair(), fee(), Amount::new(1), Amount::new(100))
        else {
            panic!("expected Ok");
        };
        assert_ne!(a, b);
    }

    // -- Debug ----------------------------------------------------------------

    #[test]
    fn debug_format_contains_struct_name() {
        let cfg = valid_cfg();
        let dbg = format!("{cfg:?}");
        assert!(dbg.contains("OrderBookConfig"));
    }
}
