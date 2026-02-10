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
//!
//! ## Create a pool and execute a swap
//!
//! ```rust
//! use hydra_amm::config::{AmmConfig, ConstantProductConfig};
//! use hydra_amm::domain::{
//!     Amount, BasisPoints, Decimals, FeeTier, SwapSpec,
//!     Token, TokenAddress, TokenPair,
//! };
//! use hydra_amm::factory::DefaultPoolFactory;
//! use hydra_amm::traits::SwapPool;
//!
//! // 1. Define two tokens
//! let usdc = Token::new(
//!     TokenAddress::from_bytes([1u8; 32]),
//!     Decimals::new(6).expect("valid decimals"),
//! );
//! let weth = Token::new(
//!     TokenAddress::from_bytes([2u8; 32]),
//!     Decimals::new(18).expect("valid decimals"),
//! );
//!
//! // 2. Build a Constant Product pool configuration
//! let pair = TokenPair::new(usdc, weth).expect("distinct tokens");
//! let fee  = FeeTier::new(BasisPoints::new(30)); // 0.30%
//! let config = AmmConfig::ConstantProduct(
//!     ConstantProductConfig::new(pair, fee, Amount::new(1_000_000), Amount::new(1_000_000))
//!         .expect("valid config"),
//! );
//!
//! // 3. Create the pool via the factory
//! let mut pool = DefaultPoolFactory::create(&config).expect("pool created");
//!
//! // 4. Execute a swap (sell 10 000 units of token A for token B)
//! let spec = SwapSpec::exact_in(Amount::new(10_000)).expect("non-zero");
//! let result = pool.swap(spec, usdc).expect("swap succeeded");
//!
//! assert!(result.amount_out().get() > 0);
//! assert!(result.fee().get() > 0);
//! ```
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────┐
//! │   Consumer   │  uses AmmConfig + DefaultPoolFactory
//! └──────┬──────┘
//!        │ create(&config)
//!        ▼
//! ┌─────────────┐
//! │   Factory    │  validates config, dispatches to FromConfig
//! └──────┬──────┘
//!        │ PoolBox (enum dispatch)
//!        ▼
//! ┌─────────────┐
//! │    Pools     │  ConstantProduct, CLMM, Hybrid, Weighted, Dynamic, OrderBook
//! └──────┬──────┘
//!        │ SwapPool + LiquidityPool traits
//!        ▼
//! ┌─────────────┐
//! │   Domain     │  Amount, Price, Tick, Token, SwapResult, …
//! └─────────────┘
//! ```
//!
//! # Module Guide
//!
//! | Module | Purpose |
//! |--------|---------|
//! | [`domain`] | Newtype value types: [`Amount`](domain::Amount), [`Price`](domain::Price), [`Token`](domain::Token), etc. |
//! | [`traits`] | Core abstractions: [`SwapPool`](traits::SwapPool), [`LiquidityPool`](traits::LiquidityPool), [`FromConfig`](traits::FromConfig) |
//! | [`config`] | Declarative pool blueprints: [`AmmConfig`](config::AmmConfig) and per-pool config structs |
//! | [`pools`]  | Feature-gated pool implementations and [`PoolBox`](pools::PoolBox) dispatch enum |
//! | [`factory`] | [`DefaultPoolFactory`](factory::DefaultPoolFactory) for config-driven pool construction |
//! | [`math`]   | Checked arithmetic, precision backends, tick math |
//! | [`error`]  | [`AmmError`](error::AmmError) unified error enum |
//! | [`prelude`] | Convenience re-exports for common types and traits |

// Module declarations (always compiled)
pub mod config;
pub mod domain;
pub mod error;
pub mod factory;
pub mod math;
pub mod pools;
pub mod prelude;
pub mod traits;
