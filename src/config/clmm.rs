//! Configuration for Concentrated Liquidity Market Maker pools (Uniswap V3 style).

use crate::domain::{FeeTier, Position, Tick, TokenPair};
use crate::error::AmmError;

/// Configuration for a Concentrated Liquidity Market Maker (CLMM) pool.
///
/// Defines the immutable parameters for a Uniswap V3 style pool where
/// liquidity providers concentrate their capital within specific tick
/// (price) ranges.
///
/// # Key Relationships
///
/// - Price at tick `i`: `P(i) = 1.0001^i`
/// - Liquidity `L` relates to reserves: `L = √(x × y)`
///
/// # Validation
///
/// - Fee tier must be a valid percentage (0–10 000 basis points).
/// - `tick_spacing` must be greater than zero.
/// - `current_tick` must be aligned to `tick_spacing`.
/// - Each position's `lower_tick` and `upper_tick` must be aligned to
///   `tick_spacing`.
/// - Each position must have `lower_tick < upper_tick` (enforced by
///   [`Position`] construction).
/// - The token pair is validated at [`TokenPair`] construction time.
#[derive(Debug, Clone, PartialEq)]
pub struct ClmmConfig {
    token_pair: TokenPair,
    fee_tier: FeeTier,
    tick_spacing: u32,
    current_tick: Tick,
    positions: Vec<Position>,
}

impl ClmmConfig {
    /// Creates a new `ClmmConfig`.
    ///
    /// # Arguments
    ///
    /// - `tick_spacing` — granularity of tick positions (standard values:
    ///   1, 10, 60, 200). Must be greater than zero.
    /// - `current_tick` — the active tick at pool creation.
    /// - `positions` — initial liquidity provider positions (may be empty).
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidFee`] if the fee tier exceeds 100% (10 000 basis points).
    /// - [`AmmError::InvalidConfiguration`] if `tick_spacing` is zero.
    /// - [`AmmError::InvalidTick`] if `current_tick` is not aligned to `tick_spacing`.
    /// - [`AmmError::InvalidTickRange`] if any position tick is not aligned to
    ///   `tick_spacing`.
    pub fn new(
        token_pair: TokenPair,
        fee_tier: FeeTier,
        tick_spacing: u32,
        current_tick: Tick,
        positions: Vec<Position>,
    ) -> Result<Self, AmmError> {
        let config = Self {
            token_pair,
            fee_tier,
            tick_spacing,
            current_tick,
            positions,
        };
        config.validate()?;
        Ok(config)
    }

    /// Validates all configuration invariants.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidFee`] if the fee tier exceeds 100% (10 000 basis points).
    /// - [`AmmError::InvalidConfiguration`] if `tick_spacing` is zero.
    /// - [`AmmError::InvalidTick`] if `current_tick` is not aligned to `tick_spacing`.
    /// - [`AmmError::InvalidTickRange`] if any position tick is not aligned to
    ///   `tick_spacing`.
    pub fn validate(&self) -> Result<(), AmmError> {
        if !self.fee_tier.basis_points().is_valid_percent() {
            return Err(AmmError::InvalidFee(
                "fee tier must not exceed 10000 basis points (100%)",
            ));
        }
        if self.tick_spacing == 0 {
            return Err(AmmError::InvalidConfiguration(
                "tick spacing must be greater than zero",
            ));
        }
        let spacing = self.tick_spacing as i32;
        if self.current_tick.get() % spacing != 0 {
            return Err(AmmError::InvalidTick(
                "current tick must be aligned to tick spacing",
            ));
        }
        for pos in &self.positions {
            if pos.lower_tick().get() % spacing != 0 {
                return Err(AmmError::InvalidTickRange(
                    "position lower tick must be aligned to tick spacing",
                ));
            }
            if pos.upper_tick().get() % spacing != 0 {
                return Err(AmmError::InvalidTickRange(
                    "position upper tick must be aligned to tick spacing",
                ));
            }
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

    /// Returns the tick spacing.
    #[must_use]
    pub const fn tick_spacing(&self) -> u32 {
        self.tick_spacing
    }

    /// Returns the current (initial) tick.
    #[must_use]
    pub const fn current_tick(&self) -> Tick {
        self.current_tick
    }

    /// Returns a reference to the initial positions.
    #[must_use]
    pub fn positions(&self) -> &[Position] {
        &self.positions
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
#[allow(clippy::indexing_slicing)]
mod tests {
    use super::*;
    use crate::domain::{BasisPoints, Decimals, Liquidity, Token, TokenAddress};

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

    fn tick(v: i32) -> Tick {
        let Ok(t) = Tick::new(v) else {
            panic!("valid tick expected");
        };
        t
    }

    fn pos(lower: i32, upper: i32, liq: u128) -> Position {
        let Ok(p) = Position::new(tick(lower), tick(upper), Liquidity::new(liq)) else {
            panic!("expected valid position");
        };
        p
    }

    fn valid_cfg() -> ClmmConfig {
        let Ok(cfg) = ClmmConfig::new(make_pair(), fee(), 10, tick(0), vec![]) else {
            panic!("expected Ok");
        };
        cfg
    }

    // -- valid construction ---------------------------------------------------

    #[test]
    fn valid_config_no_positions() {
        let result = ClmmConfig::new(make_pair(), fee(), 10, tick(0), vec![]);
        assert!(result.is_ok());
    }

    #[test]
    fn valid_config_with_aligned_positions() {
        let result = ClmmConfig::new(
            make_pair(),
            fee(),
            10,
            tick(0),
            vec![pos(-100, 100, 1_000), pos(-200, 200, 500)],
        );
        assert!(result.is_ok());
    }

    #[test]
    fn valid_with_spacing_one() {
        let result = ClmmConfig::new(make_pair(), fee(), 1, tick(7), vec![pos(-3, 5, 100)]);
        assert!(result.is_ok());
    }

    #[test]
    fn valid_with_spacing_60() {
        let result = ClmmConfig::new(make_pair(), fee(), 60, tick(120), vec![pos(-60, 180, 1)]);
        assert!(result.is_ok());
    }

    #[test]
    fn valid_with_spacing_200() {
        let result = ClmmConfig::new(make_pair(), fee(), 200, tick(0), vec![pos(-400, 600, 1)]);
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
            let result = ClmmConfig::new(make_pair(), tier, 1, tick(0), vec![]);
            assert!(result.is_ok());
        }
    }

    #[test]
    fn valid_with_zero_fee() {
        let zero_fee = FeeTier::new(BasisPoints::new(0));
        let result = ClmmConfig::new(make_pair(), zero_fee, 1, tick(0), vec![]);
        assert!(result.is_ok());
    }

    #[test]
    fn valid_with_max_valid_fee() {
        let max_fee = FeeTier::new(BasisPoints::new(10_000));
        let result = ClmmConfig::new(make_pair(), max_fee, 1, tick(0), vec![]);
        assert!(result.is_ok());
    }

    #[test]
    fn valid_with_negative_current_tick_aligned() {
        let result = ClmmConfig::new(make_pair(), fee(), 10, tick(-100), vec![]);
        assert!(result.is_ok());
    }

    // -- fee_tier validation --------------------------------------------------

    #[test]
    fn fee_exceeding_100_percent_rejected() {
        let bad_fee = FeeTier::new(BasisPoints::new(10_001));
        let result = ClmmConfig::new(make_pair(), bad_fee, 10, tick(0), vec![]);
        assert!(matches!(result, Err(AmmError::InvalidFee(_))));
    }

    #[test]
    fn fee_way_above_range_rejected() {
        let bad_fee = FeeTier::new(BasisPoints::new(u32::MAX));
        let result = ClmmConfig::new(make_pair(), bad_fee, 10, tick(0), vec![]);
        assert!(matches!(result, Err(AmmError::InvalidFee(_))));
    }

    // -- tick_spacing validation ----------------------------------------------

    #[test]
    fn zero_tick_spacing_rejected() {
        let result = ClmmConfig::new(make_pair(), fee(), 0, tick(0), vec![]);
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    // -- current_tick alignment -----------------------------------------------

    #[test]
    fn current_tick_not_aligned_rejected() {
        let result = ClmmConfig::new(make_pair(), fee(), 10, tick(5), vec![]);
        assert!(matches!(result, Err(AmmError::InvalidTick(_))));
    }

    #[test]
    fn current_tick_off_by_one_rejected() {
        let result = ClmmConfig::new(make_pair(), fee(), 60, tick(1), vec![]);
        assert!(matches!(result, Err(AmmError::InvalidTick(_))));
    }

    #[test]
    fn negative_current_tick_not_aligned_rejected() {
        let result = ClmmConfig::new(make_pair(), fee(), 10, tick(-5), vec![]);
        assert!(matches!(result, Err(AmmError::InvalidTick(_))));
    }

    // -- position tick alignment ----------------------------------------------

    #[test]
    fn position_lower_tick_not_aligned_rejected() {
        let p = pos(-5, 10, 100); // lower=-5 not aligned to spacing=10
        let result = ClmmConfig::new(make_pair(), fee(), 10, tick(0), vec![p]);
        assert!(matches!(result, Err(AmmError::InvalidTickRange(_))));
    }

    #[test]
    fn position_upper_tick_not_aligned_rejected() {
        let p = pos(-10, 15, 100); // upper=15 not aligned to spacing=10
        let result = ClmmConfig::new(make_pair(), fee(), 10, tick(0), vec![p]);
        assert!(matches!(result, Err(AmmError::InvalidTickRange(_))));
    }

    #[test]
    fn second_position_misaligned_rejected() {
        let good = pos(-100, 100, 500);
        let bad = pos(-10, 15, 100); // upper=15 not aligned
        let result = ClmmConfig::new(make_pair(), fee(), 10, tick(0), vec![good, bad]);
        assert!(matches!(result, Err(AmmError::InvalidTickRange(_))));
    }

    #[test]
    fn position_negative_ticks_not_aligned_rejected() {
        let p = pos(-7, 3, 100); // both misaligned to spacing=10
        let result = ClmmConfig::new(make_pair(), fee(), 10, tick(0), vec![p]);
        assert!(matches!(result, Err(AmmError::InvalidTickRange(_))));
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
        let p = pos(-60, 60, 1_000);
        let Ok(cfg) = ClmmConfig::new(pair, f, 60, tick(0), vec![p]) else {
            panic!("expected Ok");
        };
        assert_eq!(*cfg.token_pair(), pair);
        assert_eq!(cfg.fee_tier(), f);
        assert_eq!(cfg.tick_spacing(), 60);
        assert_eq!(cfg.current_tick(), tick(0));
        assert_eq!(cfg.positions().len(), 1);
        assert_eq!(cfg.positions()[0], p);
    }

    #[test]
    fn accessors_empty_positions() {
        let Ok(cfg) = ClmmConfig::new(make_pair(), fee(), 10, tick(0), vec![]) else {
            panic!("expected Ok");
        };
        assert!(cfg.positions().is_empty());
    }

    // -- Clone & PartialEq ---------------------------------------------------

    #[test]
    fn clone_equality() {
        let cfg = valid_cfg();
        let cloned = cfg.clone();
        assert_eq!(cfg, cloned);
    }

    #[test]
    fn different_tick_spacing_not_equal() {
        let Ok(a) = ClmmConfig::new(make_pair(), fee(), 10, tick(0), vec![]) else {
            panic!("expected Ok");
        };
        let Ok(b) = ClmmConfig::new(make_pair(), fee(), 60, tick(0), vec![]) else {
            panic!("expected Ok");
        };
        assert_ne!(a, b);
    }

    // -- Debug ----------------------------------------------------------------

    #[test]
    fn debug_format_contains_struct_name() {
        let cfg = valid_cfg();
        let dbg = format!("{cfg:?}");
        assert!(dbg.contains("ClmmConfig"));
    }
}
