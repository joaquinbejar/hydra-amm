//! Configuration for Constant Product AMM pools (Uniswap V2 style).

use crate::domain::{Amount, FeeTier, TokenPair};
use crate::error::AmmError;

/// Configuration for a Constant Product AMM pool (`x · y = k`).
///
/// Defines the immutable parameters for a Uniswap V2 style pool:
/// token pair, fee tier, and initial reserves.
///
/// # Derived Values
///
/// - Initial invariant: `k = reserve_a × reserve_b`
/// - Initial price (token A in terms of token B): `P₀ = reserve_b / reserve_a`
///
/// # Validation
///
/// - Both reserves must be non-zero.
/// - The token pair is validated at [`TokenPair`] construction time.
#[derive(Debug, Clone, PartialEq)]
pub struct ConstantProductConfig {
    token_pair: TokenPair,
    fee_tier: FeeTier,
    reserve_a: Amount,
    reserve_b: Amount,
}

impl ConstantProductConfig {
    /// Creates a new `ConstantProductConfig`.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::ZeroReserve`] if either reserve is zero.
    pub fn new(
        token_pair: TokenPair,
        fee_tier: FeeTier,
        reserve_a: Amount,
        reserve_b: Amount,
    ) -> Result<Self, AmmError> {
        let config = Self {
            token_pair,
            fee_tier,
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
    /// Returns [`AmmError::ZeroReserve`] if either reserve is zero.
    pub fn validate(&self) -> Result<(), AmmError> {
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
        let result =
            ConstantProductConfig::new(make_pair(), fee(), Amount::new(1_000), Amount::new(2_000));
        assert!(result.is_ok());
    }

    #[test]
    fn zero_reserve_a_rejected() {
        let result =
            ConstantProductConfig::new(make_pair(), fee(), Amount::ZERO, Amount::new(1_000));
        assert!(result.is_err());
    }

    #[test]
    fn zero_reserve_b_rejected() {
        let result =
            ConstantProductConfig::new(make_pair(), fee(), Amount::new(1_000), Amount::ZERO);
        assert!(result.is_err());
    }

    #[test]
    fn accessors() {
        let pair = make_pair();
        let f = fee();
        let Ok(cfg) = ConstantProductConfig::new(pair, f, Amount::new(100), Amount::new(200))
        else {
            panic!("expected Ok");
        };
        assert_eq!(*cfg.token_pair(), pair);
        assert_eq!(cfg.fee_tier(), f);
        assert_eq!(cfg.reserve_a(), Amount::new(100));
        assert_eq!(cfg.reserve_b(), Amount::new(200));
    }
}
