//! Constant Product pool implementation (Uniswap V2 style).
//!
//! The swap invariant is `x × y = k` where `x` and `y` are the reserves
//! of the two tokens.  Full implementation will be added in a later issue.

use crate::config::ConstantProductConfig;
use crate::domain::{
    Amount, FeeTier, Liquidity, LiquidityChange, Position, Price, SwapResult, SwapSpec, Token,
    TokenPair,
};
use crate::error::AmmError;
use crate::traits::{FromConfig, LiquidityPool, SwapPool};

/// A Constant Product AMM pool (`x · y = k`).
///
/// Created from a [`ConstantProductConfig`] via [`FromConfig`].  The pool
/// validates the configuration on construction and is immediately ready
/// for swaps (once the swap logic is implemented).
#[derive(Debug, Clone, PartialEq)]
pub struct ConstantProductPool {
    config: ConstantProductConfig,
}

impl FromConfig<ConstantProductConfig> for ConstantProductPool {
    /// Creates a new pool from the given configuration.
    ///
    /// # Errors
    ///
    /// Propagates any error from [`ConstantProductConfig::validate`].
    fn from_config(config: &ConstantProductConfig) -> Result<Self, AmmError> {
        config.validate()?;
        Ok(Self {
            config: config.clone(),
        })
    }
}

impl SwapPool for ConstantProductPool {
    fn swap(&mut self, _spec: SwapSpec, _token_in: Token) -> Result<SwapResult, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "constant product swap not yet implemented",
        ))
    }

    fn spot_price(&self, _base: &Token, _quote: &Token) -> Result<Price, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "constant product spot_price not yet implemented",
        ))
    }

    fn token_pair(&self) -> &TokenPair {
        self.config.token_pair()
    }

    fn fee_tier(&self) -> FeeTier {
        self.config.fee_tier()
    }
}

impl LiquidityPool for ConstantProductPool {
    fn add_liquidity(&mut self, _change: &LiquidityChange) -> Result<Amount, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "constant product add_liquidity not yet implemented",
        ))
    }

    fn remove_liquidity(&mut self, _change: &LiquidityChange) -> Result<Amount, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "constant product remove_liquidity not yet implemented",
        ))
    }

    fn collect_fees(&mut self, _position: &Position) -> Result<Amount, AmmError> {
        Err(AmmError::InvalidConfiguration(
            "constant product collect_fees not yet implemented",
        ))
    }

    fn total_liquidity(&self) -> Liquidity {
        Liquidity::ZERO
    }
}
