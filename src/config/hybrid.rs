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
/// - Fee tier must be a valid percentage (0–10 000 basis points).
/// - Amplification must be in the range `1..=10_000`.
/// - Both reserves must be non-zero.
/// - The token pair is validated at [`TokenPair`] construction time.
#[derive(Debug, Clone, PartialEq)]
pub struct HybridConfig {
    token_pair: TokenPair,
    fee_tier: FeeTier,
    amplification: u32,
    reserve_a: Amount,
    reserve_b: Amount,
}

impl HybridConfig {
    /// Maximum allowed amplification coefficient.
    const MAX_AMPLIFICATION: u32 = 10_000;

    /// Creates a new `HybridConfig`.
    ///
    /// # Arguments
    ///
    /// - `amplification` — the StableSwap amplification coefficient
    ///   (must be in `1..=10_000`, typically 50–5000).
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidFee`] if the fee tier exceeds 100% (10 000 basis points).
    /// - [`AmmError::InvalidConfiguration`] if `amplification` is zero or exceeds 10 000.
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
    /// - [`AmmError::InvalidFee`] if the fee tier exceeds 100% (10 000 basis points).
    /// - [`AmmError::InvalidConfiguration`] if `amplification` is zero or exceeds 10 000.
    /// - [`AmmError::ZeroReserve`] if either reserve is zero.
    pub fn validate(&self) -> Result<(), AmmError> {
        if !self.fee_tier.basis_points().is_valid_percent() {
            return Err(AmmError::InvalidFee(
                "fee tier must not exceed 10000 basis points (100%)",
            ));
        }
        if self.amplification == 0 || self.amplification > Self::MAX_AMPLIFICATION {
            return Err(AmmError::InvalidConfiguration(
                "amplification must be in the range 1..=10000",
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

    fn valid_cfg() -> HybridConfig {
        let Ok(cfg) = HybridConfig::new(
            make_pair(),
            fee(),
            100,
            Amount::new(1_000_000),
            Amount::new(1_000_000),
        ) else {
            panic!("expected Ok");
        };
        cfg
    }

    // -- valid construction ---------------------------------------------------

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
    fn valid_with_amplification_one() {
        let result = HybridConfig::new(
            make_pair(),
            fee(),
            1,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn valid_with_max_amplification() {
        let result = HybridConfig::new(
            make_pair(),
            fee(),
            10_000,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn valid_with_typical_stablecoin_amplification() {
        for amp in [50, 100, 200, 500, 1_000, 5_000] {
            let result = HybridConfig::new(
                make_pair(),
                fee(),
                amp,
                Amount::new(1_000),
                Amount::new(1_000),
            );
            assert!(result.is_ok());
        }
    }

    #[test]
    fn valid_with_standard_fee_tiers() {
        for tier in [
            FeeTier::TIER_0_01_PERCENT,
            FeeTier::TIER_0_05_PERCENT,
            FeeTier::TIER_0_30_PERCENT,
            FeeTier::TIER_1_00_PERCENT,
        ] {
            let result = HybridConfig::new(
                make_pair(),
                tier,
                100,
                Amount::new(1_000),
                Amount::new(1_000),
            );
            assert!(result.is_ok());
        }
    }

    #[test]
    fn valid_with_zero_fee() {
        let zero_fee = FeeTier::new(BasisPoints::new(0));
        let result = HybridConfig::new(
            make_pair(),
            zero_fee,
            100,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn valid_with_max_valid_fee() {
        let max_fee = FeeTier::new(BasisPoints::new(10_000));
        let result = HybridConfig::new(
            make_pair(),
            max_fee,
            100,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn valid_with_large_reserves() {
        let result = HybridConfig::new(
            make_pair(),
            fee(),
            100,
            Amount::new(u128::MAX),
            Amount::new(u128::MAX),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn valid_with_minimum_reserves() {
        let result = HybridConfig::new(make_pair(), fee(), 1, Amount::new(1), Amount::new(1));
        assert!(result.is_ok());
    }

    // -- fee_tier validation --------------------------------------------------

    #[test]
    fn fee_exceeding_100_percent_rejected() {
        let bad_fee = FeeTier::new(BasisPoints::new(10_001));
        let result = HybridConfig::new(
            make_pair(),
            bad_fee,
            100,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(matches!(result, Err(AmmError::InvalidFee(_))));
    }

    #[test]
    fn fee_way_above_range_rejected() {
        let bad_fee = FeeTier::new(BasisPoints::new(u32::MAX));
        let result = HybridConfig::new(
            make_pair(),
            bad_fee,
            100,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(matches!(result, Err(AmmError::InvalidFee(_))));
    }

    // -- amplification validation ---------------------------------------------

    #[test]
    fn zero_amplification_rejected() {
        let result = HybridConfig::new(
            make_pair(),
            fee(),
            0,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    #[test]
    fn amplification_exceeding_max_rejected() {
        let result = HybridConfig::new(
            make_pair(),
            fee(),
            10_001,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    #[test]
    fn amplification_way_above_max_rejected() {
        let result = HybridConfig::new(
            make_pair(),
            fee(),
            u32::MAX,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    // -- reserve validation ---------------------------------------------------

    #[test]
    fn zero_reserve_a_rejected() {
        let result = HybridConfig::new(make_pair(), fee(), 100, Amount::ZERO, Amount::new(1_000));
        assert!(matches!(result, Err(AmmError::ZeroReserve)));
    }

    #[test]
    fn zero_reserve_b_rejected() {
        let result = HybridConfig::new(make_pair(), fee(), 100, Amount::new(1_000), Amount::ZERO);
        assert!(matches!(result, Err(AmmError::ZeroReserve)));
    }

    #[test]
    fn both_reserves_zero_rejected() {
        let result = HybridConfig::new(make_pair(), fee(), 100, Amount::ZERO, Amount::ZERO);
        assert!(matches!(result, Err(AmmError::ZeroReserve)));
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
        let Ok(cfg) = HybridConfig::new(pair, f, 200, Amount::new(500), Amount::new(600)) else {
            panic!("expected Ok");
        };
        assert_eq!(*cfg.token_pair(), pair);
        assert_eq!(cfg.fee_tier(), f);
        assert_eq!(cfg.amplification(), 200);
        assert_eq!(cfg.reserve_a(), Amount::new(500));
        assert_eq!(cfg.reserve_b(), Amount::new(600));
    }

    // -- Clone & PartialEq ---------------------------------------------------

    #[test]
    fn clone_equality() {
        let cfg = valid_cfg();
        let cloned = cfg.clone();
        assert_eq!(cfg, cloned);
    }

    #[test]
    fn different_amplification_not_equal() {
        let Ok(a) = HybridConfig::new(
            make_pair(),
            fee(),
            100,
            Amount::new(1_000),
            Amount::new(1_000),
        ) else {
            panic!("expected Ok");
        };
        let Ok(b) = HybridConfig::new(
            make_pair(),
            fee(),
            200,
            Amount::new(1_000),
            Amount::new(1_000),
        ) else {
            panic!("expected Ok");
        };
        assert_ne!(a, b);
    }

    // -- Debug ----------------------------------------------------------------

    #[test]
    fn debug_format_contains_struct_name() {
        let cfg = valid_cfg();
        let dbg = format!("{cfg:?}");
        assert!(dbg.contains("HybridConfig"));
    }
}
