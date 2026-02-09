//! Configuration for Dynamic / Proactive Market Maker pools (DODO style).

use crate::domain::{Amount, FeeTier, Price, TokenPair};
use crate::error::AmmError;

/// Configuration for a Dynamic (Proactive Market Maker) pool.
///
/// Defines the immutable parameters for a DODO-style pool that uses an
/// external price oracle to concentrate liquidity around the market price.
///
/// # Slippage Coefficient
///
/// The `slippage_coefficient` (`k`) controls liquidity concentration:
///
/// - `k = 0.0` — infinite liquidity at oracle price (effectively a taker)
/// - `k = 1.0` — behaves like constant product
/// - Typical values: 0.1–0.5
///
/// # Validation
///
/// - `slippage_coefficient` must be in the range `[0.0, 1.0]` and finite.
/// - Both reserves must be non-zero.
/// - `oracle_price` must be positive (non-zero).
#[derive(Debug, Clone, PartialEq)]
pub struct DynamicConfig {
    token_pair: TokenPair,
    fee_tier: FeeTier,
    oracle_price: Price,
    slippage_coefficient: f64,
    base_reserve: Amount,
    quote_reserve: Amount,
}

impl DynamicConfig {
    /// Creates a new `DynamicConfig`.
    ///
    /// # Arguments
    ///
    /// - `slippage_coefficient` — the `k` parameter in `[0.0, 1.0]`.
    /// - `oracle_price` — reference mid-price from external oracle (must
    ///   be positive).
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidConfiguration`] if `slippage_coefficient` is
    ///   outside `[0.0, 1.0]` or not finite.
    /// - [`AmmError::InvalidConfiguration`] if `oracle_price` is zero.
    /// - [`AmmError::ZeroReserve`] if either reserve is zero.
    pub fn new(
        token_pair: TokenPair,
        fee_tier: FeeTier,
        oracle_price: Price,
        slippage_coefficient: f64,
        base_reserve: Amount,
        quote_reserve: Amount,
    ) -> Result<Self, AmmError> {
        let config = Self {
            token_pair,
            fee_tier,
            oracle_price,
            slippage_coefficient,
            base_reserve,
            quote_reserve,
        };
        config.validate()?;
        Ok(config)
    }

    /// Validates all configuration invariants.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidConfiguration`] if `slippage_coefficient` is
    ///   outside `[0.0, 1.0]` or not finite.
    /// - [`AmmError::InvalidConfiguration`] if `oracle_price` is zero.
    /// - [`AmmError::ZeroReserve`] if either reserve is zero.
    pub fn validate(&self) -> Result<(), AmmError> {
        if !self.slippage_coefficient.is_finite()
            || self.slippage_coefficient < 0.0
            || self.slippage_coefficient > 1.0
        {
            return Err(AmmError::InvalidConfiguration(
                "slippage coefficient must be in [0.0, 1.0] and finite",
            ));
        }
        if self.oracle_price.get() <= 0.0 {
            return Err(AmmError::InvalidConfiguration(
                "oracle price must be positive",
            ));
        }
        if self.base_reserve.is_zero() {
            return Err(AmmError::ZeroReserve);
        }
        if self.quote_reserve.is_zero() {
            return Err(AmmError::ZeroReserve);
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

    /// Returns the oracle reference price.
    #[must_use]
    pub const fn oracle_price(&self) -> Price {
        self.oracle_price
    }

    /// Returns the slippage coefficient (`k`), in the range `[0.0, 1.0]`.
    #[must_use]
    pub const fn slippage_coefficient(&self) -> f64 {
        self.slippage_coefficient
    }

    /// Returns the initial base token reserve.
    pub const fn base_reserve(&self) -> Amount {
        self.base_reserve
    }

    /// Returns the initial quote token reserve.
    pub const fn quote_reserve(&self) -> Amount {
        self.quote_reserve
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

    fn oracle() -> Price {
        let Ok(p) = Price::new(100.0) else {
            panic!("expected valid price");
        };
        p
    }

    #[test]
    fn valid_config() {
        let result = DynamicConfig::new(
            make_pair(),
            fee(),
            oracle(),
            0.5,
            Amount::new(1_000),
            Amount::new(100_000),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn k_zero_valid() {
        let result = DynamicConfig::new(
            make_pair(),
            fee(),
            oracle(),
            0.0,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn k_one_valid() {
        let result = DynamicConfig::new(
            make_pair(),
            fee(),
            oracle(),
            1.0,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn k_negative_rejected() {
        let result = DynamicConfig::new(
            make_pair(),
            fee(),
            oracle(),
            -0.1,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(result.is_err());
    }

    #[test]
    fn k_above_one_rejected() {
        let result = DynamicConfig::new(
            make_pair(),
            fee(),
            oracle(),
            1.1,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(result.is_err());
    }

    #[test]
    fn k_nan_rejected() {
        let result = DynamicConfig::new(
            make_pair(),
            fee(),
            oracle(),
            f64::NAN,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(result.is_err());
    }

    #[test]
    fn zero_base_reserve_rejected() {
        let result = DynamicConfig::new(
            make_pair(),
            fee(),
            oracle(),
            0.5,
            Amount::ZERO,
            Amount::new(1_000),
        );
        assert!(result.is_err());
    }

    #[test]
    fn zero_quote_reserve_rejected() {
        let result = DynamicConfig::new(
            make_pair(),
            fee(),
            oracle(),
            0.5,
            Amount::new(1_000),
            Amount::ZERO,
        );
        assert!(result.is_err());
    }

    #[test]
    fn accessors() {
        let pair = make_pair();
        let f = fee();
        let p = oracle();
        let Ok(cfg) = DynamicConfig::new(pair, f, p, 0.3, Amount::new(500), Amount::new(600))
        else {
            panic!("expected Ok");
        };
        assert_eq!(*cfg.token_pair(), pair);
        assert_eq!(cfg.fee_tier(), f);
        assert_eq!(cfg.oracle_price(), p);
        assert!((cfg.slippage_coefficient() - 0.3).abs() < f64::EPSILON);
        assert_eq!(cfg.base_reserve(), Amount::new(500));
        assert_eq!(cfg.quote_reserve(), Amount::new(600));
    }
}
