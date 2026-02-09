//! Concentrated Liquidity Market Maker pool implementation (Uniswap V3 style).
//!
//! Liquidity is concentrated within specific tick (price) ranges.
//! Full implementation will be added in a later issue.

use crate::config::ClmmConfig;
use crate::domain::{
    Amount, FeeTier, Liquidity, LiquidityChange, Position, Price, SwapResult, SwapSpec, Token,
    TokenPair,
};
use crate::error::AmmError;
use crate::traits::{FromConfig, LiquidityPool, SwapPool};

/// A Concentrated Liquidity Market Maker (CLMM) pool.
///
/// Created from a [`ClmmConfig`] via [`FromConfig`].  Liquidity providers
/// concentrate capital within specific tick ranges for higher capital
/// efficiency.
#[derive(Debug, Clone, PartialEq)]
pub struct ClmmPool {
    config: ClmmConfig,
}

impl FromConfig<ClmmConfig> for ClmmPool {
    /// Creates a new pool from the given configuration.
    ///
    /// # Errors
    ///
    /// Propagates any error from [`ClmmConfig::validate`].
    fn from_config(config: &ClmmConfig) -> Result<Self, AmmError> {
        config.validate()?;
        Ok(Self {
            config: config.clone(),
        })
    }
}

impl SwapPool for ClmmPool {
    fn swap(&mut self, _spec: SwapSpec, _token_in: Token) -> Result<SwapResult, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "clmm swap not yet implemented",
        ))
    }

    fn spot_price(&self, _base: &Token, _quote: &Token) -> Result<Price, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "clmm spot_price not yet implemented",
        ))
    }

    fn token_pair(&self) -> &TokenPair {
        self.config.token_pair()
    }

    fn fee_tier(&self) -> FeeTier {
        self.config.fee_tier()
    }
}

impl LiquidityPool for ClmmPool {
    fn add_liquidity(&mut self, _change: &LiquidityChange) -> Result<Amount, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "clmm add_liquidity not yet implemented",
        ))
    }

    fn remove_liquidity(&mut self, _change: &LiquidityChange) -> Result<Amount, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "clmm remove_liquidity not yet implemented",
        ))
    }

    fn collect_fees(&mut self, _position: &Position) -> Result<Amount, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "clmm collect_fees not yet implemented",
        ))
    }

    fn total_liquidity(&self) -> Liquidity {
        Liquidity::ZERO
    }
}
