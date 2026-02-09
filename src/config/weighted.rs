//! Configuration for Weighted AMM pools (Balancer style).

use crate::domain::{Amount, BasisPoints, FeeTier, Token};
use crate::error::AmmError;

/// Configuration for a Weighted pool supporting N tokens with custom
/// weight distributions (Balancer style).
///
/// # Invariant
///
/// ```text
/// ∏(Bᵢ ^ Wᵢ) = k
/// ```
///
/// where `Bᵢ` is the balance of token `i` and `Wᵢ` is its normalized
/// weight (as a fraction, e.g., 0.5 for 50%).
///
/// # Validation
///
/// - Fee tier must be a valid percentage (0–10 000 basis points).
/// - `tokens.len() == weights.len() == balances.len()`
/// - At least 2 tokens.
/// - No duplicate token addresses.
/// - All individual weights must be greater than zero.
/// - Weights must sum to exactly 10 000 basis points.
/// - All balances must be non-zero.
#[derive(Debug, Clone, PartialEq)]
pub struct WeightedConfig {
    tokens: Vec<Token>,
    weights: Vec<BasisPoints>,
    fee_tier: FeeTier,
    balances: Vec<Amount>,
}

impl WeightedConfig {
    /// Creates a new `WeightedConfig`.
    ///
    /// # Arguments
    ///
    /// - `tokens` — the tokens in the pool (typically 2–8).
    /// - `weights` — the weight of each token in basis points; must sum
    ///   to 10 000.
    /// - `balances` — the initial balance of each token; all must be
    ///   non-zero.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidFee`] if the fee tier exceeds 100% (10 000 basis points).
    /// - [`AmmError::InvalidConfiguration`] if vector lengths differ, or
    ///   fewer than 2 tokens, or duplicate token addresses, or weights do
    ///   not sum to 10 000.
    /// - [`AmmError::InvalidWeight`] if any individual weight is zero.
    /// - [`AmmError::ZeroReserve`] if any balance is zero.
    pub fn new(
        tokens: Vec<Token>,
        weights: Vec<BasisPoints>,
        fee_tier: FeeTier,
        balances: Vec<Amount>,
    ) -> Result<Self, AmmError> {
        let config = Self {
            tokens,
            weights,
            fee_tier,
            balances,
        };
        config.validate()?;
        Ok(config)
    }

    /// Validates all configuration invariants.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidFee`] if the fee tier exceeds 100% (10 000 basis points).
    /// - [`AmmError::InvalidConfiguration`] if vector lengths differ, or
    ///   fewer than 2 tokens, or duplicate token addresses, or weights do
    ///   not sum to 10 000.
    /// - [`AmmError::InvalidWeight`] if any individual weight is zero.
    /// - [`AmmError::ZeroReserve`] if any balance is zero.
    pub fn validate(&self) -> Result<(), AmmError> {
        if !self.fee_tier.basis_points().is_valid_percent() {
            return Err(AmmError::InvalidFee(
                "fee tier must not exceed 10000 basis points (100%)",
            ));
        }
        if self.tokens.len() != self.weights.len() || self.tokens.len() != self.balances.len() {
            return Err(AmmError::InvalidConfiguration(
                "tokens, weights, and balances must have equal length",
            ));
        }
        if self.tokens.len() < 2 {
            return Err(AmmError::InvalidConfiguration(
                "at least 2 tokens are required",
            ));
        }

        // Check for duplicate token addresses (O(n²), fine for ≤8 tokens).
        let mut iter = self.tokens.iter();
        while let Some(token) = iter.next() {
            for other in iter.clone() {
                if token.address() == other.address() {
                    return Err(AmmError::InvalidConfiguration(
                        "duplicate token addresses are not allowed",
                    ));
                }
            }
        }

        for w in &self.weights {
            if w.get() == 0 {
                return Err(AmmError::InvalidWeight(
                    "all individual weights must be greater than zero",
                ));
            }
        }

        let weight_sum: u32 = self.weights.iter().map(|w| w.get()).sum();
        if weight_sum != 10_000 {
            return Err(AmmError::InvalidConfiguration(
                "weights must sum to exactly 10000 basis points",
            ));
        }

        for balance in &self.balances {
            if balance.is_zero() {
                return Err(AmmError::ZeroReserve);
            }
        }

        Ok(())
    }

    /// Returns a reference to the tokens.
    #[must_use]
    pub fn tokens(&self) -> &[Token] {
        &self.tokens
    }

    /// Returns a reference to the weights.
    #[must_use]
    pub fn weights(&self) -> &[BasisPoints] {
        &self.weights
    }

    /// Returns the fee tier.
    #[must_use]
    pub const fn fee_tier(&self) -> FeeTier {
        self.fee_tier
    }

    /// Returns a reference to the initial balances.
    pub fn balances(&self) -> &[Amount] {
        &self.balances
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
#[allow(clippy::indexing_slicing)]
mod tests {
    use super::*;
    use crate::domain::{Decimals, TokenAddress};

    // -- helpers --------------------------------------------------------------

    fn tok(byte: u8, dec: u8) -> Token {
        let Ok(d) = Decimals::new(dec) else {
            panic!("valid decimals");
        };
        Token::new(TokenAddress::from_bytes([byte; 32]), d)
    }

    fn fee() -> FeeTier {
        FeeTier::new(BasisPoints::new(30))
    }

    fn bps(v: u32) -> BasisPoints {
        BasisPoints::new(v)
    }

    fn valid_cfg() -> WeightedConfig {
        let Ok(cfg) = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(5_000), bps(5_000)],
            fee(),
            vec![Amount::new(1_000), Amount::new(2_000)],
        ) else {
            panic!("expected Ok");
        };
        cfg
    }

    // -- valid construction ---------------------------------------------------

    #[test]
    fn valid_two_token_pool() {
        let result = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(5_000), bps(5_000)],
            fee(),
            vec![Amount::new(1_000), Amount::new(2_000)],
        );
        assert!(result.is_ok());
    }

    #[test]
    fn valid_three_token_pool() {
        let result = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18), tok(3, 8)],
            vec![bps(3_333), bps(3_333), bps(3_334)],
            fee(),
            vec![Amount::new(100), Amount::new(200), Amount::new(300)],
        );
        assert!(result.is_ok());
    }

    #[test]
    fn valid_asymmetric_weights() {
        let result = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(8_000), bps(2_000)],
            fee(),
            vec![Amount::new(1_000), Amount::new(500)],
        );
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
            let result = WeightedConfig::new(
                vec![tok(1, 6), tok(2, 18)],
                vec![bps(5_000), bps(5_000)],
                tier,
                vec![Amount::new(1_000), Amount::new(1_000)],
            );
            assert!(result.is_ok());
        }
    }

    #[test]
    fn valid_with_zero_fee() {
        let zero_fee = FeeTier::new(BasisPoints::new(0));
        let result = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(5_000), bps(5_000)],
            zero_fee,
            vec![Amount::new(1), Amount::new(1)],
        );
        assert!(result.is_ok());
    }

    #[test]
    fn valid_with_max_valid_fee() {
        let max_fee = FeeTier::new(BasisPoints::new(10_000));
        let result = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(5_000), bps(5_000)],
            max_fee,
            vec![Amount::new(1), Amount::new(1)],
        );
        assert!(result.is_ok());
    }

    #[test]
    fn valid_with_large_balances() {
        let result = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(5_000), bps(5_000)],
            fee(),
            vec![Amount::new(u128::MAX), Amount::new(u128::MAX)],
        );
        assert!(result.is_ok());
    }

    // -- fee_tier validation --------------------------------------------------

    #[test]
    fn fee_exceeding_100_percent_rejected() {
        let bad_fee = FeeTier::new(BasisPoints::new(10_001));
        let result = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(5_000), bps(5_000)],
            bad_fee,
            vec![Amount::new(1_000), Amount::new(1_000)],
        );
        assert!(matches!(result, Err(AmmError::InvalidFee(_))));
    }

    #[test]
    fn fee_way_above_range_rejected() {
        let bad_fee = FeeTier::new(BasisPoints::new(u32::MAX));
        let result = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(5_000), bps(5_000)],
            bad_fee,
            vec![Amount::new(1_000), Amount::new(1_000)],
        );
        assert!(matches!(result, Err(AmmError::InvalidFee(_))));
    }

    // -- length validation ----------------------------------------------------

    #[test]
    fn mismatched_weights_length_rejected() {
        let result = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(5_000)],
            fee(),
            vec![Amount::new(1_000), Amount::new(2_000)],
        );
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    #[test]
    fn mismatched_balances_length_rejected() {
        let result = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(5_000), bps(5_000)],
            fee(),
            vec![Amount::new(1_000)],
        );
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    // -- min tokens -----------------------------------------------------------

    #[test]
    fn fewer_than_two_tokens_rejected() {
        let result = WeightedConfig::new(
            vec![tok(1, 6)],
            vec![bps(10_000)],
            fee(),
            vec![Amount::new(1_000)],
        );
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    #[test]
    fn empty_tokens_rejected() {
        let result = WeightedConfig::new(vec![], vec![], fee(), vec![]);
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    // -- duplicate tokens -----------------------------------------------------

    #[test]
    fn duplicate_tokens_rejected() {
        let result = WeightedConfig::new(
            vec![tok(1, 6), tok(1, 18)],
            vec![bps(5_000), bps(5_000)],
            fee(),
            vec![Amount::new(1_000), Amount::new(2_000)],
        );
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    // -- individual weight validation -----------------------------------------

    #[test]
    fn zero_weight_rejected() {
        let result = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(0), bps(10_000)],
            fee(),
            vec![Amount::new(1_000), Amount::new(1_000)],
        );
        assert!(matches!(result, Err(AmmError::InvalidWeight(_))));
    }

    #[test]
    fn second_weight_zero_rejected() {
        let result = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(10_000), bps(0)],
            fee(),
            vec![Amount::new(1_000), Amount::new(1_000)],
        );
        assert!(matches!(result, Err(AmmError::InvalidWeight(_))));
    }

    // -- weight sum validation ------------------------------------------------

    #[test]
    fn weights_not_summing_to_10000_rejected() {
        let result = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(4_000), bps(4_000)],
            fee(),
            vec![Amount::new(1_000), Amount::new(2_000)],
        );
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    #[test]
    fn weights_exceeding_10000_rejected() {
        let result = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(6_000), bps(6_000)],
            fee(),
            vec![Amount::new(1_000), Amount::new(1_000)],
        );
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    // -- balance validation ---------------------------------------------------

    #[test]
    fn zero_balance_first_rejected() {
        let result = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(5_000), bps(5_000)],
            fee(),
            vec![Amount::ZERO, Amount::new(1_000)],
        );
        assert!(matches!(result, Err(AmmError::ZeroReserve)));
    }

    #[test]
    fn zero_balance_second_rejected() {
        let result = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(5_000), bps(5_000)],
            fee(),
            vec![Amount::new(1_000), Amount::ZERO],
        );
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
        let Ok(cfg) = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(5_000), bps(5_000)],
            fee(),
            vec![Amount::new(100), Amount::new(200)],
        ) else {
            panic!("expected Ok");
        };
        assert_eq!(cfg.tokens().len(), 2);
        assert_eq!(cfg.weights().len(), 2);
        assert_eq!(cfg.weights()[0], bps(5_000));
        assert_eq!(cfg.weights()[1], bps(5_000));
        assert_eq!(cfg.balances().len(), 2);
        assert_eq!(cfg.balances()[0], Amount::new(100));
        assert_eq!(cfg.balances()[1], Amount::new(200));
        assert_eq!(cfg.fee_tier(), fee());
    }

    // -- Clone & PartialEq ---------------------------------------------------

    #[test]
    fn clone_equality() {
        let cfg = valid_cfg();
        let cloned = cfg.clone();
        assert_eq!(cfg, cloned);
    }

    #[test]
    fn different_weights_not_equal() {
        let Ok(a) = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(5_000), bps(5_000)],
            fee(),
            vec![Amount::new(1_000), Amount::new(1_000)],
        ) else {
            panic!("expected Ok");
        };
        let Ok(b) = WeightedConfig::new(
            vec![tok(1, 6), tok(2, 18)],
            vec![bps(8_000), bps(2_000)],
            fee(),
            vec![Amount::new(1_000), Amount::new(1_000)],
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
        assert!(dbg.contains("WeightedConfig"));
    }
}
