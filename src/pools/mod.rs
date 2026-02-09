//! Feature-gated pool implementations and the [`PoolBox`] dispatch enum.
//!
//! Each pool type is behind its own Cargo feature flag.  The [`PoolBox`]
//! enum provides zero-cost static dispatch across all enabled pool types,
//! allowing heterogeneous collections without `dyn` trait objects.
//!
//! # Pool Types
//!
//! | Feature | Pool | Style |
//! |---------|------|-------|
//! | `constant-product` | [`ConstantProductPool`] | Uniswap V2 |
//! | `clmm` | [`ClmmPool`] | Uniswap V3 |
//! | `hybrid` | [`HybridPool`] | Curve StableSwap |
//! | `weighted` | [`WeightedPool`] | Balancer |
//! | `dynamic` | [`DynamicPool`] | DODO PMM |
//! | `order-book` | [`OrderBookPool`] | Phoenix |

#[cfg(feature = "clmm")]
pub mod clmm;
#[cfg(feature = "constant-product")]
pub mod constant_product;
#[cfg(feature = "dynamic")]
pub mod dynamic;
#[cfg(feature = "hybrid")]
pub mod hybrid;
#[cfg(feature = "order-book")]
pub mod order_book;
#[cfg(feature = "weighted")]
pub mod weighted;

mod pool_box;

#[cfg(feature = "clmm")]
pub use clmm::ClmmPool;
#[cfg(feature = "constant-product")]
pub use constant_product::ConstantProductPool;
#[cfg(feature = "dynamic")]
pub use dynamic::DynamicPool;
#[cfg(feature = "hybrid")]
pub use hybrid::HybridPool;
#[cfg(feature = "order-book")]
pub use order_book::OrderBookPool;
pub use pool_box::PoolBox;
#[cfg(feature = "weighted")]
pub use weighted::WeightedPool;
