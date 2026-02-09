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
mod rounding;
mod token;
mod token_address;
mod token_pair;

pub use amount::Amount;
pub use basis_points::BasisPoints;
pub use decimals::Decimals;
pub use fee_tier::FeeTier;
pub use liquidity::Liquidity;
pub use rounding::Rounding;
pub use token::Token;
pub use token_address::TokenAddress;
pub use token_pair::TokenPair;
