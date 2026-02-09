//! Core trait abstractions for AMM pool operations.
//!
//! This module defines the primary traits that all pool implementations
//! must satisfy: [`SwapPool`] for executing swaps, [`LiquidityPool`]
//! for managing positions, and [`FromConfig`] for configuration-driven
//! pool construction.

mod from_config;
mod liquidity_pool;
mod swap_pool;

pub use from_config::FromConfig;
pub use liquidity_pool::LiquidityPool;
pub use swap_pool::SwapPool;
