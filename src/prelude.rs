//! Convenience re-exports for common types and traits.
//!
//! The prelude provides a single import to bring all commonly used items
//! into scope:
//!
//! ```rust
//! use hydra_amm::prelude::*;
//! ```
//!
//! This re-exports the most frequently used domain types, core traits,
//! configuration types, error types, and factory utilities so that
//! consumers don't need to import from individual submodules.

// Re-export domain types (types added incrementally as they are implemented)
pub use crate::domain::{
    Amount, BasisPoints, ChangeType, Decimals, FeeTier, Liquidity, LiquidityChange, Position,
    Price, Rounding, SwapResult, SwapSpec, SwapType, Tick, Token, TokenAddress, TokenPair,
};

// Re-export core traits
pub use crate::traits::{FromConfig, LiquidityPool, SwapPool};

// Re-export math utilities
pub use crate::math::CheckedArithmetic;
pub use crate::math::Precision;
pub use crate::math::div_round;
pub use crate::math::{price_at_tick, tick_at_price};

#[cfg(feature = "fixed-point")]
pub use crate::math::FixedPointArithmetic;
#[cfg(feature = "float")]
pub use crate::math::FloatArithmetic;

// Re-export configuration
pub use crate::config::{
    AmmConfig, ClmmConfig, ConstantProductConfig, DynamicConfig, HybridConfig, OrderBookConfig,
    WeightedConfig,
};

// Re-export error types
pub use crate::error::{AmmError, Result};

// Re-export factory
// pub use crate::factory::DefaultPoolFactory;

// Re-export pool dispatch
pub use crate::pools::PoolBox;

#[cfg(feature = "clmm")]
pub use crate::pools::ClmmPool;
#[cfg(feature = "constant-product")]
pub use crate::pools::ConstantProductPool;
#[cfg(feature = "dynamic")]
pub use crate::pools::DynamicPool;
#[cfg(feature = "hybrid")]
pub use crate::pools::HybridPool;
#[cfg(feature = "order-book")]
pub use crate::pools::OrderBookPool;
#[cfg(feature = "weighted")]
pub use crate::pools::WeightedPool;
