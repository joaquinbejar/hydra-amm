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
/// - Fee tier must be a valid percentage (0–10 000 basis points).
/// - `slippage_coefficient` must be in the range `[0.0, 1.0]` and finite.
/// - `oracle_price` must be positive (non-zero).
/// - Both reserves must be non-zero.
/// - The token pair is validated at [`TokenPair`] construction time.
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
    /// - [`AmmError::InvalidFee`] if the fee tier exceeds 100% (10 000 basis points).
    /// - [`AmmError::InvalidConfiguration`] if `slippage_coefficient` is
    ///   outside `[0.0, 1.0]` or not finite.
    /// - [`AmmError::InvalidPrice`] if `oracle_price` is zero or negative.
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
    /// - [`AmmError::InvalidFee`] if the fee tier exceeds 100% (10 000 basis points).
    /// - [`AmmError::InvalidConfiguration`] if `slippage_coefficient` is
    ///   outside `[0.0, 1.0]` or not finite.
    /// - [`AmmError::InvalidPrice`] if `oracle_price` is zero or negative.
    /// - [`AmmError::ZeroReserve`] if either reserve is zero.
    pub fn validate(&self) -> Result<(), AmmError> {
        if !self.fee_tier.basis_points().is_valid_percent() {
            return Err(AmmError::InvalidFee(
                "fee tier must not exceed 10000 basis points (100%)",
            ));
        }
        if !self.slippage_coefficient.is_finite()
            || self.slippage_coefficient < 0.0
            || self.slippage_coefficient > 1.0
        {
            return Err(AmmError::InvalidConfiguration(
                "slippage coefficient must be in [0.0, 1.0] and finite",
            ));
        }
        if self.oracle_price.get() <= 0.0 {
            return Err(AmmError::InvalidPrice("oracle price must be positive"));
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

    fn oracle() -> Price {
        let Ok(p) = Price::new(100.0) else {
            panic!("expected valid price");
        };
        p
    }

    fn valid_cfg() -> DynamicConfig {
        let Ok(cfg) = DynamicConfig::new(
            make_pair(),
            fee(),
            oracle(),
            0.5,
            Amount::new(1_000),
            Amount::new(100_000),
        ) else {
            panic!("expected Ok");
        };
        cfg
    }

    // -- valid construction ---------------------------------------------------

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
            Amount::new(1),
            Amount::new(1),
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
            Amount::new(1),
            Amount::new(1),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn k_typical_values_valid() {
        for k in [0.1, 0.2, 0.3, 0.5] {
            let result = DynamicConfig::new(
                make_pair(),
                fee(),
                oracle(),
                k,
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
            let result = DynamicConfig::new(
                make_pair(),
                tier,
                oracle(),
                0.5,
                Amount::new(1_000),
                Amount::new(1_000),
            );
            assert!(result.is_ok());
        }
    }

    #[test]
    fn valid_with_zero_fee() {
        let zero_fee = FeeTier::new(BasisPoints::new(0));
        let result = DynamicConfig::new(
            make_pair(),
            zero_fee,
            oracle(),
            0.5,
            Amount::new(1),
            Amount::new(1),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn valid_with_max_valid_fee() {
        let max_fee = FeeTier::new(BasisPoints::new(10_000));
        let result = DynamicConfig::new(
            make_pair(),
            max_fee,
            oracle(),
            0.5,
            Amount::new(1),
            Amount::new(1),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn valid_with_large_reserves() {
        let result = DynamicConfig::new(
            make_pair(),
            fee(),
            oracle(),
            0.5,
            Amount::new(u128::MAX),
            Amount::new(u128::MAX),
        );
        assert!(result.is_ok());
    }

    // -- fee_tier validation --------------------------------------------------

    #[test]
    fn fee_exceeding_100_percent_rejected() {
        let bad_fee = FeeTier::new(BasisPoints::new(10_001));
        let result = DynamicConfig::new(
            make_pair(),
            bad_fee,
            oracle(),
            0.5,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(matches!(result, Err(AmmError::InvalidFee(_))));
    }

    #[test]
    fn fee_way_above_range_rejected() {
        let bad_fee = FeeTier::new(BasisPoints::new(u32::MAX));
        let result = DynamicConfig::new(
            make_pair(),
            bad_fee,
            oracle(),
            0.5,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(matches!(result, Err(AmmError::InvalidFee(_))));
    }

    // -- slippage coefficient validation --------------------------------------

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
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
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
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
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
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    #[test]
    fn k_positive_infinity_rejected() {
        let result = DynamicConfig::new(
            make_pair(),
            fee(),
            oracle(),
            f64::INFINITY,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    #[test]
    fn k_negative_infinity_rejected() {
        let result = DynamicConfig::new(
            make_pair(),
            fee(),
            oracle(),
            f64::NEG_INFINITY,
            Amount::new(1_000),
            Amount::new(1_000),
        );
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    // -- oracle price validation (uses InvalidPrice) --------------------------

    // Note: Price::new() already rejects non-positive values at construction,
    // so we cannot easily construct a Price with value <= 0 to pass to
    // DynamicConfig. The oracle_price check is a defense-in-depth guard.

    // -- reserve validation ---------------------------------------------------

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
        assert!(matches!(result, Err(AmmError::ZeroReserve)));
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
        assert!(matches!(result, Err(AmmError::ZeroReserve)));
    }

    #[test]
    fn both_reserves_zero_rejected() {
        let result = DynamicConfig::new(
            make_pair(),
            fee(),
            oracle(),
            0.5,
            Amount::ZERO,
            Amount::ZERO,
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

    // -- Clone & PartialEq ---------------------------------------------------

    #[test]
    fn clone_equality() {
        let cfg = valid_cfg();
        let cloned = cfg.clone();
        assert_eq!(cfg, cloned);
    }

    #[test]
    fn different_k_not_equal() {
        let Ok(a) = DynamicConfig::new(
            make_pair(),
            fee(),
            oracle(),
            0.3,
            Amount::new(1_000),
            Amount::new(1_000),
        ) else {
            panic!("expected Ok");
        };
        let Ok(b) = DynamicConfig::new(
            make_pair(),
            fee(),
            oracle(),
            0.7,
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
        assert!(dbg.contains("DynamicConfig"));
    }
}
