//! Core swap pool trait for executing swaps and querying pool state.
//!
//! [`SwapPool`] is the foundational abstraction that every AMM pool must
//! implement.  It provides four methods covering the full lifecycle of a
//! swap operation:
//!
//! 1. **Execute** — [`SwapPool::swap`] performs the actual token exchange.
//! 2. **Quote** — [`SwapPool::spot_price`] returns the current exchange
//!    rate between two tokens.
//! 3. **Inspect pair** — [`SwapPool::token_pair`] returns the ordered
//!    token pair managed by the pool.
//! 4. **Inspect fees** — [`SwapPool::fee_tier`] returns the pool's fee
//!    tier.
//!
//! # Fee Deduction Invariant
//!
//! All swap implementations **must** deduct fees from the input amount
//! before applying the pricing formula:
//!
//! ```text
//! fee_amount = amount_in × fee_bps / 10_000
//! net_input  = amount_in − fee_amount
//! amount_out = price_curve(net_input)
//! ```
//!
//! # Dispatch Model
//!
//! Pools are dispatched via enums (not `dyn` trait objects), enabling
//! static polymorphism and `no_std` compatibility.  See the `pools`
//! module for the `PoolBox` enum that wraps all pool variants.

use crate::domain::{FeeTier, Price, SwapResult, SwapSpec, Token, TokenPair};
use crate::error::AmmError;

/// Core trait for all AMM liquidity pools.
///
/// Every pool implementation must provide all four methods — there are no
/// default implementations.  This ensures that each pool type explicitly
/// handles swap execution, price calculation, and state queries.
///
/// # Implementors
///
/// Concrete implementations include:
///
/// - `ConstantProductPool` — Uniswap v2 style (`x · y = k`)
/// - `ConcentratedLiquidityPool` — Uniswap v3 style (tick-based)
/// - `HybridPool` — Curve-style StableSwap
/// - `WeightedPool` — Balancer-style weighted pools
/// - `DynamicPool` — DODO-style proactive market making
/// - `OrderBookPool` — Phoenix-style order book hybrid
///
/// # Errors
///
/// Methods that can fail return [`Result<T, AmmError>`].  Common error
/// variants include:
///
/// - [`AmmError::InsufficientLiquidity`] — reserves too low for the swap
/// - [`AmmError::ZeroReserve`] — one or both reserves are zero
/// - [`AmmError::InvalidToken`] — input token is not part of the pool pair
/// - [`AmmError::Overflow`] — arithmetic overflow during calculation
pub trait SwapPool {
    /// Executes a token swap on the pool.
    ///
    /// Fee is always deducted from the input amount **before** the pricing
    /// formula is applied.  Reserve updates are atomic — partial fills are
    /// forbidden; the swap either completes fully or returns an error.
    ///
    /// # Arguments
    ///
    /// - `spec` — the swap specification (exact-in or exact-out with amount).
    /// - `token_in` — the token being sold; the pool determines the output
    ///   token from its [`TokenPair`].
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidToken`] if `token_in` is not part of the pool's
    ///   token pair.
    /// - [`AmmError::InsufficientLiquidity`] if pool reserves cannot satisfy
    ///   the swap.
    /// - [`AmmError::Overflow`] if any intermediate arithmetic overflows.
    fn swap(&mut self, spec: SwapSpec, token_in: Token) -> Result<SwapResult, AmmError>;

    /// Returns the current spot price between two tokens.
    ///
    /// The price is expressed as *units of `quote` per unit of `base`*.
    /// Both `base` and `quote` must be members of the pool's
    /// [`TokenPair`].
    ///
    /// # Arguments
    ///
    /// - `base` — the base token (denominator of the price ratio).
    /// - `quote` — the quote token (numerator of the price ratio).
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidToken`] if either token is not part of the
    ///   pool's pair.
    /// - [`AmmError::ZeroReserve`] if either reserve is zero.
    fn spot_price(&self, base: &Token, quote: &Token) -> Result<Price, AmmError>;

    /// Returns the ordered token pair managed by this pool.
    ///
    /// The pair is canonically ordered: `first().address() < second().address()`.
    /// The ordering is immutable for the lifetime of the pool.
    #[must_use]
    fn token_pair(&self) -> &TokenPair;

    /// Returns the fee tier applied to swaps.
    ///
    /// The fee tier is constant for the lifetime of the pool.  It is used
    /// to calculate the fee deduction: `fee = amount_in × bps / 10_000`.
    #[must_use]
    fn fee_tier(&self) -> FeeTier;
}
