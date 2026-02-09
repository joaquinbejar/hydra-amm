//! Configuration for Hybrid / StableSwap AMM pools (Curve style).

use crate::domain::{Amount, FeeTier, TokenPair};
use crate::error::AmmError;

/// Configuration for a Hybrid (StableSwap) AMM pool.
///
/// Defines the immutable parameters for a Curve-style pool specialized
/// in low-slippage swaps between similarly-priced assets (e.g., stablecoins).
///
/// # Amplification Parameter
///
/// The `amplification` parameter (`A`) controls the curve shape:
///
/// - `A = 1` — curve degrades to constant product (`x · y = k`)
/// - `A → ∞` — curve approaches constant sum (`x + y = const`, 1:1 swaps)
/// - Typical range for stablecoin pairs: 50–5000
///
/// # Invariant
///
/// The StableSwap invariant for `n = 2` tokens:
///
/// ```text
/// A · 2 · (x + y) + D = A · D · 2 + D³ / (4xy)
/// ```
///
/// # Validation
///
/// - Both reserves must be non-zero.
/// - Amplification must be greater than zero.
#[derive(Debug, Clone, PartialEq)]
pub struct HybridConfig {
    token_pair: TokenPair,
    fee_tier: FeeTier,
    amplification: u32,
    reserve_a: Amount,
    reserve_b: Amount,
}

impl HybridConfig {
    /// Creates a new `HybridConfig`.
    ///
    /// # Arguments
    ///
    /// - `amplification` — the StableSwap amplification coefficient
    ///   (must be > 0, typically 50–5000).
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidConfiguration`] if `amplification` is zero.
    /// - [`AmmError::ZeroReserve`] if either reserve is zero.
    pub fn new(
        token_pair: TokenPair,
        fee_tier: FeeTier,
        amplification: u32,
        reserve_a: Amount,
        reserve_b: Amount,
    ) -> Result<Self, AmmError> {
        let config = Self {
            token_pair,
            fee_tier,
            amplification,
            reserve_a,
            reserve_b,
        };
        config.validate()?;
        Ok(config)
    }

    /// Validates all configuration invariants.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidConfiguration`] if `amplification` is zero.
    /// - [`AmmError::ZeroReserve`] if either reserve is zero.
    pub fn validate(&self) -> Result<(), AmmError> {
        if self.amplification == 0 {
            return Err(AmmError::InvalidConfiguration(
                "amplification must be greater than zero",
            ));
        }
        if self.reserve_a.is_zero() {
            return Err(AmmError::ZeroReserve);
        }
        if self.reserve_b.is_zero() {
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

    /// Returns the amplification coefficient.
    #[must_use]
    pub const fn amplification(&self) -> u32 {
        self.amplification
    }

    /// Returns the initial reserve of token A.
    pub const fn reserve_a(&self) -> Amount {
        self.reserve_a
    }

    /// Returns the initial reserve of token B.
    pub const fn reserve_b(&self) -> Amount {
        self.reserve_b
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
        let result = HybridConfig::new(
            make_pair(),
            fee(),
            100,
            Amount::new(1_000_000),
            Amount::new(1_000_000),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn zero_amplification_rejected() {
        let result = HybridConfig::new(
            make_pair(),
            fee(),
            0,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(result.is_err());
    }

    #[test]
    fn zero_reserve_a_rejected() {
        let result = HybridConfig::new(make_pair(), fee(), 100, Amount::ZERO, Amount::new(1_000));
        assert!(result.is_err());
    }

    #[test]
    fn zero_reserve_b_rejected() {
        let result = HybridConfig::new(make_pair(), fee(), 100, Amount::new(1_000), Amount::ZERO);
        assert!(result.is_err());
    }

    #[test]
    fn accessors() {
        let pair = make_pair();
        let f = fee();
        let Ok(cfg) = HybridConfig::new(pair, f, 200, Amount::new(500), Amount::new(600)) else {
            panic!("expected Ok");
        };
        assert_eq!(*cfg.token_pair(), pair);
        assert_eq!(cfg.fee_tier(), f);
        assert_eq!(cfg.amplification(), 200);
        assert_eq!(cfg.reserve_a(), Amount::new(500));
        assert_eq!(cfg.reserve_b(), Amount::new(600));
    }
}
