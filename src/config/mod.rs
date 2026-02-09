//! Pool configuration enums and structs.
//!
//! This module contains the [`AmmConfig`] enum — the top-level declarative
//! blueprint for creating any pool type — along with per-pool configuration
//! structs that define the parameters for each AMM family.

mod amm_config;
mod clmm;
mod constant_product;
mod dynamic;
mod hybrid;
mod order_book;
mod weighted;

pub use amm_config::AmmConfig;
pub use clmm::ClmmConfig;
pub use constant_product::ConstantProductConfig;
pub use dynamic::DynamicConfig;
pub use hybrid::HybridConfig;
pub use order_book::OrderBookConfig;
pub use weighted::WeightedConfig;
