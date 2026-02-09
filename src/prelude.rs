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
// pub use crate::traits::{FromConfig, LiquidityPool, SwapPool};

// Re-export math utilities
pub use crate::math::Precision;
// pub use crate::math::CheckedArithmetic;

#[cfg(feature = "fixed-point")]
pub use crate::math::FixedPointArithmetic;
#[cfg(feature = "float")]
pub use crate::math::FloatArithmetic;

// Re-export configuration
// pub use crate::config::AmmConfig;

// Re-export error types
pub use crate::error::{AmmError, Result};

// Re-export factory
// pub use crate::factory::DefaultPoolFactory;

// Re-export pool dispatch
// pub use crate::pools::PoolBox;
