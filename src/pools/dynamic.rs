//! Dynamic / Proactive Market Maker pool implementation (DODO style).
//!
//! Uses an external price oracle to concentrate liquidity around the
//! market price.  Full implementation will be added in a later issue.

use crate::config::DynamicConfig;
use crate::domain::{
    Amount, FeeTier, Liquidity, LiquidityChange, Position, Price, SwapResult, SwapSpec, Token,
    TokenPair,
};
use crate::error::AmmError;
use crate::traits::{FromConfig, LiquidityPool, SwapPool};

/// A Dynamic (Proactive Market Maker) pool.
///
/// Created from a [`DynamicConfig`] via [`FromConfig`].  Uses an oracle
/// price and slippage coefficient to concentrate liquidity near the
/// market price.
#[derive(Debug, Clone, PartialEq)]
pub struct DynamicPool {
    config: DynamicConfig,
}

impl FromConfig<DynamicConfig> for DynamicPool {
    /// Creates a new pool from the given configuration.
    ///
    /// # Errors
    ///
    /// Propagates any error from [`DynamicConfig::validate`].
    fn from_config(config: &DynamicConfig) -> Result<Self, AmmError> {
        config.validate()?;
        Ok(Self {
            config: config.clone(),
        })
    }
}

impl SwapPool for DynamicPool {
    fn swap(&mut self, _spec: SwapSpec, _token_in: Token) -> Result<SwapResult, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "dynamic swap not yet implemented",
        ))
    }

    fn spot_price(&self, _base: &Token, _quote: &Token) -> Result<Price, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "dynamic spot_price not yet implemented",
        ))
    }

    fn token_pair(&self) -> &TokenPair {
        self.config.token_pair()
    }

    fn fee_tier(&self) -> FeeTier {
        self.config.fee_tier()
    }
}

impl LiquidityPool for DynamicPool {
    fn add_liquidity(&mut self, _change: &LiquidityChange) -> Result<Amount, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "dynamic add_liquidity not yet implemented",
        ))
    }

    fn remove_liquidity(&mut self, _change: &LiquidityChange) -> Result<Amount, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "dynamic remove_liquidity not yet implemented",
        ))
    }

    fn collect_fees(&mut self, _position: &Position) -> Result<Amount, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "dynamic collect_fees not yet implemented",
        ))
    }

    fn total_liquidity(&self) -> Liquidity {
        Liquidity::ZERO
    }
}
