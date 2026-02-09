//! Fundamental domain value types used throughout the AMM library.
//!
//! This module contains the core value types that model the AMM domain:
//! tokens, amounts, prices, ticks, positions, and swap specifications.
//! All types use newtypes with validated constructors to enforce invariants.

mod amount;
mod basis_points;
mod decimals;
mod fee_tier;
mod liquidity;
mod liquidity_change;
mod position;
mod price;
mod rounding;
mod swap_result;
mod swap_spec;
mod tick;
mod token;
mod token_address;
mod token_pair;

pub use amount::Amount;
pub use basis_points::BasisPoints;
pub use decimals::Decimals;
pub use fee_tier::FeeTier;
pub use liquidity::Liquidity;
pub use liquidity_change::{ChangeType, LiquidityChange};
pub use position::Position;
pub use price::Price;
pub use rounding::Rounding;
pub use swap_result::SwapResult;
pub use swap_spec::{SwapSpec, SwapType};
pub use tick::Tick;
pub use token::Token;
pub use token_address::TokenAddress;
pub use token_pair::TokenPair;
