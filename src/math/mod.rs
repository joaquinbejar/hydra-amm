//! Arithmetic and precision utilities for AMM calculations.
//!
//! This module provides the [`Precision`] trait for feature-gated numeric
//! backends, [`CheckedArithmetic`] for overflow-safe operations,
//! `Rounding` for explicit division rounding, and tick math helpers.
//!
//! # Feature-gated backends
//!
//! | Feature | Type | Use case |
//! |---------|------|----------|
//! | `float` | `FloatArithmetic` | Off-chain simulation |
//! | `fixed-point` | `FixedPointArithmetic` | On-chain (Solana BPF) |

mod checked;
mod precision;
mod rounding;
mod tick_math;

#[cfg(feature = "fixed-point")]
mod fixed_precision;
#[cfg(feature = "float")]
mod float_precision;

pub use checked::CheckedArithmetic;
pub use precision::Precision;
pub use rounding::div_round;
pub use tick_math::{price_at_tick, tick_at_price};

#[cfg(feature = "fixed-point")]
pub use fixed_precision::FixedPointArithmetic;
#[cfg(feature = "float")]
pub use float_precision::FloatArithmetic;
