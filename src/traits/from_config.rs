//! Generic construction trait for pool instantiation from configuration.
//!
//! [`FromConfig`] provides a uniform interface for creating pool instances
//! from their respective configuration structs.  Each pool type implements
//! `FromConfig<C>` for its own config variant, enabling the factory to
//! dispatch construction without `dyn` trait objects.
//!
//! # Validation Contract
//!
//! Implementations **must** validate all configuration invariants during
//! construction.  A successfully constructed pool is guaranteed to be in
//! a valid initial state.  Common validations include:
//!
//! - Token pair has two distinct addresses
//! - Fee tier is within supported range
//! - Initial reserves are non-zero (where applicable)
//! - Pool-specific parameters are valid (e.g., tick spacing > 0 for CLMM,
//!   weights sum to 100% for weighted pools)
//!
//! # Factory Integration
//!
//! The [`DefaultPoolFactory`](crate::factory) uses `FromConfig` to
//! construct pools from [`AmmConfig`](crate::config) variants:
//!
//! ```text
//! AmmConfig::ConstantProduct(cfg) => ConstantProductPool::from_config(&cfg)
//! AmmConfig::Clmm(cfg)            => ConcentratedLiquidityPool::from_config(&cfg)
//! ```
//!
//! # No Generic Blanket Implementation
//!
//! There is no `impl<T> FromConfig<T>` blanket — each pool must
//! explicitly implement the trait for its specific config type.  This
//! ensures that every pool-config pairing is intentional and that
//! validation logic is pool-specific.

use crate::error::AmmError;

/// Generic construction trait for building a pool from a configuration.
///
/// Each pool type implements this trait for its own configuration struct,
/// enabling type-safe construction with full validation.
///
/// # Type Parameters
///
/// - `C` — the configuration type that fully describes the pool's
///   immutable parameters (token pair, fee tier, initial reserves, etc.).
///
/// # Implementors
///
/// - `impl FromConfig<ConstantProductConfig> for ConstantProductPool`
/// - `impl FromConfig<ClmmConfig> for ConcentratedLiquidityPool`
/// - `impl FromConfig<HybridConfig> for HybridPool`
/// - `impl FromConfig<WeightedConfig> for WeightedPool`
/// - `impl FromConfig<DynamicConfig> for DynamicPool`
/// - `impl FromConfig<OrderBookConfig> for OrderBookPool`
///
/// # Errors
///
/// Returns [`AmmError::InvalidConfiguration`] (or a more specific
/// variant) if the configuration is invalid.
pub trait FromConfig<C> {
    /// Creates a new pool instance from the given configuration.
    ///
    /// The implementation validates all configuration invariants and
    /// returns a fully initialized pool on success.  The configuration
    /// is taken by reference because it may be reused (e.g., for logging
    /// or retry).
    ///
    /// # Arguments
    ///
    /// - `config` — immutable reference to the pool configuration.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidConfiguration`] if any pool parameter is
    ///   out of range or inconsistent.
    /// - [`AmmError::InvalidToken`] if the token pair is invalid.
    /// - [`AmmError::InvalidFee`] if the fee tier is unsupported.
    fn from_config(config: &C) -> Result<Self, AmmError>
    where
        Self: Sized;
}
