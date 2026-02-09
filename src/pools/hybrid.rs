//! Hybrid / StableSwap pool implementation (Curve style).
//!
//! Specialized for low-slippage swaps between similarly-priced assets.
//! Full implementation will be added in a later issue.

use crate::config::HybridConfig;
use crate::domain::{
    Amount, FeeTier, Liquidity, LiquidityChange, Position, Price, SwapResult, SwapSpec, Token,
    TokenPair,
};
use crate::error::AmmError;
use crate::traits::{FromConfig, LiquidityPool, SwapPool};

/// A Hybrid (StableSwap) AMM pool.
///
/// Created from a [`HybridConfig`] via [`FromConfig`].  Uses the Curve
/// StableSwap invariant to provide low-slippage swaps between pegged
/// assets.
#[derive(Debug, Clone, PartialEq)]
pub struct HybridPool {
    config: HybridConfig,
}

impl FromConfig<HybridConfig> for HybridPool {
    /// Creates a new pool from the given configuration.
    ///
    /// # Errors
    ///
    /// Propagates any error from [`HybridConfig::validate`].
    fn from_config(config: &HybridConfig) -> Result<Self, AmmError> {
        config.validate()?;
        Ok(Self {
            config: config.clone(),
        })
    }
}

impl SwapPool for HybridPool {
    fn swap(&mut self, _spec: SwapSpec, _token_in: Token) -> Result<SwapResult, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "hybrid swap not yet implemented",
        ))
    }

    fn spot_price(&self, _base: &Token, _quote: &Token) -> Result<Price, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "hybrid spot_price not yet implemented",
        ))
    }

    fn token_pair(&self) -> &TokenPair {
        self.config.token_pair()
    }

    fn fee_tier(&self) -> FeeTier {
        self.config.fee_tier()
    }
}

impl LiquidityPool for HybridPool {
    fn add_liquidity(&mut self, _change: &LiquidityChange) -> Result<Amount, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "hybrid add_liquidity not yet implemented",
        ))
    }

    fn remove_liquidity(&mut self, _change: &LiquidityChange) -> Result<Amount, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "hybrid remove_liquidity not yet implemented",
        ))
    }

    fn collect_fees(&mut self, _position: &Position) -> Result<Amount, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "hybrid collect_fees not yet implemented",
        ))
    }

    fn total_liquidity(&self) -> Liquidity {
        Liquidity::ZERO
    }
}
