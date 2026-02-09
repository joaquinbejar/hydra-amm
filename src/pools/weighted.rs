//! Weighted pool implementation (Balancer style).
//!
//! Supports N tokens with custom weight distributions.
//! Full implementation will be added in a later issue.

use crate::config::WeightedConfig;
use crate::domain::{
    Amount, FeeTier, Liquidity, LiquidityChange, Position, Price, SwapResult, SwapSpec, Token,
    TokenPair,
};
use crate::error::AmmError;
use crate::traits::{FromConfig, LiquidityPool, SwapPool};

/// A Weighted AMM pool (Balancer style).
///
/// Created from a [`WeightedConfig`] via [`FromConfig`].  Supports
/// arbitrary token weight distributions (e.g., 80/20, 50/50).
///
/// # Note
///
/// The `token_pair` accessor returns the first two tokens from the
/// weighted pool's token list as an ordered pair.  Full N-token swap
/// logic will be implemented in a later issue.
#[derive(Debug, Clone, PartialEq)]
pub struct WeightedPool {
    config: WeightedConfig,
    /// Canonical pair derived from the first two tokens for trait compat.
    token_pair: TokenPair,
}

impl FromConfig<WeightedConfig> for WeightedPool {
    /// Creates a new pool from the given configuration.
    ///
    /// # Errors
    ///
    /// - Propagates any error from [`WeightedConfig::validate`].
    /// - Returns [`AmmError::InvalidConfiguration`] if a [`TokenPair`]
    ///   cannot be constructed from the first two tokens.
    fn from_config(config: &WeightedConfig) -> Result<Self, AmmError> {
        config.validate()?;
        let tokens = config.tokens();
        let Some(first) = tokens.first() else {
            return Err(AmmError::InvalidConfiguration(
                "weighted pool requires at least 2 tokens",
            ));
        };
        let Some(second) = tokens.get(1) else {
            return Err(AmmError::InvalidConfiguration(
                "weighted pool requires at least 2 tokens",
            ));
        };
        let token_pair = TokenPair::new(*first, *second)?;
        Ok(Self {
            config: config.clone(),
            token_pair,
        })
    }
}

impl SwapPool for WeightedPool {
    fn swap(&mut self, _spec: SwapSpec, _token_in: Token) -> Result<SwapResult, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "weighted swap not yet implemented",
        ))
    }

    fn spot_price(&self, _base: &Token, _quote: &Token) -> Result<Price, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "weighted spot_price not yet implemented",
        ))
    }

    fn token_pair(&self) -> &TokenPair {
        &self.token_pair
    }

    fn fee_tier(&self) -> FeeTier {
        self.config.fee_tier()
    }
}

impl LiquidityPool for WeightedPool {
    fn add_liquidity(&mut self, _change: &LiquidityChange) -> Result<Amount, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "weighted add_liquidity not yet implemented",
        ))
    }

    fn remove_liquidity(&mut self, _change: &LiquidityChange) -> Result<Amount, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "weighted remove_liquidity not yet implemented",
        ))
    }

    fn collect_fees(&mut self, _position: &Position) -> Result<Amount, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "weighted collect_fees not yet implemented",
        ))
    }

    fn total_liquidity(&self) -> Liquidity {
        Liquidity::ZERO
    }
}
