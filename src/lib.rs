//! # Hydra AMM
//!
//! Universal AMM engine: build, configure, and operate any Automated Market
//! Maker through a unified interface.
//!
//! This crate provides domain types, core traits, configuration structures,
//! and feature-gated pool implementations for six AMM families:
//!
//! - **Constant Product** (Uniswap v2 style) — `constant-product` feature
//! - **Concentrated Liquidity** (Uniswap v3 style) — `clmm` feature
//! - **Hybrid / StableSwap** (Curve style) — `hybrid` feature
//! - **Weighted Pools** (Balancer style) — `weighted` feature
//! - **Dynamic / Proactive MM** (DODO style) — `dynamic` feature
//! - **Order Book Hybrid** (Phoenix style) — `order-book` feature
//!
//! # Feature Flags
//!
//! | Feature | Default | Description |
//! |---------|---------|-------------|
//! | `std` | yes | Standard library support |
//! | `fixed-point` | no | I80F48 fixed-point arithmetic |
//! | `float` | no | f64 floating-point (implies `std`) |
//! | `all-pools` | yes | Enables all six pool types |
//!
//! # Quick Start
//!
//! Add to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! hydra-amm = "0.1"
//! ```
//!
//! To use only specific pool types:
//!
//! ```toml
//! [dependencies]
//! hydra-amm = { version = "0.1", default-features = false, features = ["std", "constant-product"] }
//! ```

// Module declarations (always compiled)
pub mod config;
pub mod domain;
pub mod error;
pub mod factory;
pub mod math;
pub mod pools;
pub mod prelude;
pub mod traits;
