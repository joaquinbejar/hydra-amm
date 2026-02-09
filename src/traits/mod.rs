//! Core trait abstractions for AMM pool operations.
//!
//! This module defines the primary traits that all pool implementations
//! must satisfy: [`SwapPool`] for executing swaps, `LiquidityPool`
//! for managing positions, and `FromConfig` for configuration-driven
//! pool construction.

mod swap_pool;

pub use swap_pool::SwapPool;
