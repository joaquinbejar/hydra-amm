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
/// - `tick_spacing` must be greater than zero.
/// - `current_tick` must be within the valid tick range.
/// - Each position must have `lower_tick < upper_tick` (enforced by
///   [`Position`] construction).
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
    /// Returns [`AmmError::InvalidConfiguration`] if `tick_spacing` is zero.
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
    /// Returns [`AmmError::InvalidConfiguration`] if `tick_spacing` is zero.
    pub fn validate(&self) -> Result<(), AmmError> {
        if self.tick_spacing == 0 {
            return Err(AmmError::InvalidConfiguration(
                "tick spacing must be greater than zero",
            ));
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
mod tests {
    use super::*;
    use crate::domain::{BasisPoints, Decimals, Liquidity, Token, TokenAddress};

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

    #[test]
    fn valid_config_no_positions() {
        let result = ClmmConfig::new(make_pair(), fee(), 10, tick(0), vec![]);
        assert!(result.is_ok());
    }

    #[test]
    fn valid_config_with_positions() {
        let Ok(pos) = Position::new(tick(-100), tick(100), Liquidity::new(1_000)) else {
            panic!("expected valid position");
        };
        let result = ClmmConfig::new(make_pair(), fee(), 10, tick(0), vec![pos]);
        assert!(result.is_ok());
    }

    #[test]
    fn zero_tick_spacing_rejected() {
        let result = ClmmConfig::new(make_pair(), fee(), 0, tick(0), vec![]);
        assert!(result.is_err());
    }

    #[test]
    fn accessors() {
        let pair = make_pair();
        let f = fee();
        let Ok(cfg) = ClmmConfig::new(pair, f, 60, tick(500), vec![]) else {
            panic!("expected Ok");
        };
        assert_eq!(*cfg.token_pair(), pair);
        assert_eq!(cfg.fee_tier(), f);
        assert_eq!(cfg.tick_spacing(), 60);
        assert_eq!(cfg.current_tick(), tick(500));
        assert!(cfg.positions().is_empty());
    }
}
