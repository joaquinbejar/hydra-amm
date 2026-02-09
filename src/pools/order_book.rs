//! Order Book hybrid pool implementation (Phoenix style).
//!
//! Wraps the `orderbook-rs` crate for order book functionality.
//! Full implementation will be added in a later issue.

use crate::config::OrderBookConfig;
use crate::domain::{
    Amount, FeeTier, Liquidity, LiquidityChange, Position, Price, SwapResult, SwapSpec, Token,
    TokenPair,
};
use crate::error::AmmError;
use crate::traits::{FromConfig, LiquidityPool, SwapPool};

/// An Order Book hybrid AMM pool.
///
/// Created from an [`OrderBookConfig`] via [`FromConfig`].  Combines
/// order book mechanics with AMM liquidity, wrapping the `orderbook-rs`
/// engine internally.
#[derive(Debug, Clone, PartialEq)]
pub struct OrderBookPool {
    config: OrderBookConfig,
}

impl FromConfig<OrderBookConfig> for OrderBookPool {
    /// Creates a new pool from the given configuration.
    ///
    /// # Errors
    ///
    /// Propagates any error from [`OrderBookConfig::validate`].
    fn from_config(config: &OrderBookConfig) -> Result<Self, AmmError> {
        config.validate()?;
        Ok(Self {
            config: config.clone(),
        })
    }
}

impl SwapPool for OrderBookPool {
    fn swap(&mut self, _spec: SwapSpec, _token_in: Token) -> Result<SwapResult, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "order book swap not yet implemented",
        ))
    }

    fn spot_price(&self, _base: &Token, _quote: &Token) -> Result<Price, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "order book spot_price not yet implemented",
        ))
    }

    fn token_pair(&self) -> &TokenPair {
        self.config.token_pair()
    }

    fn fee_tier(&self) -> FeeTier {
        self.config.fee_tier()
    }
}

impl LiquidityPool for OrderBookPool {
    fn add_liquidity(&mut self, _change: &LiquidityChange) -> Result<Amount, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "order book add_liquidity not yet implemented",
        ))
    }

    fn remove_liquidity(&mut self, _change: &LiquidityChange) -> Result<Amount, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "order book remove_liquidity not yet implemented",
        ))
    }

    fn collect_fees(&mut self, _position: &Position) -> Result<Amount, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "order book collect_fees not yet implemented",
        ))
    }

    fn total_liquidity(&self) -> Liquidity {
        Liquidity::ZERO
    }
}
