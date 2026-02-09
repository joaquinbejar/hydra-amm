//! Liquidity management trait extending [`SwapPool`].
//!
//! [`LiquidityPool`] adds position management and fee collection on top
//! of the core swap functionality provided by [`SwapPool`].  Every pool
//! that supports liquidity provision must implement this trait.
//!
//! # Liquidity Accounting Invariant
//!
//! The total liquidity reported by [`LiquidityPool::total_liquidity`]
//! **only** changes through [`LiquidityPool::add_liquidity`] and
//! [`LiquidityPool::remove_liquidity`].  No other operation (swaps,
//! fee collection, price queries) may alter the total.
//!
//! For a pool with `n` positions and total liquidity `L`:
//!
//! ```text
//! L = Σ position[i].liquidity   for all i
//! ```
//!
//! # Fee Collection Isolation
//!
//! Fee collection via [`LiquidityPool::collect_fees`] returns accrued
//! fees **without** altering pool reserves or the price curve.  Fees
//! accumulate per-position during swaps and are claimed explicitly.
//!
//! Calling `collect_fees` twice on the same position without
//! intermediate swaps returns zero the second time (idempotent).

use super::SwapPool;
use crate::domain::{Amount, Liquidity, LiquidityChange, Position};
use crate::error::AmmError;

/// Trait for pools that support liquidity provision and fee collection.
///
/// Extends [`SwapPool`] with methods to add/remove liquidity, query
/// total liquidity, and collect accrued trading fees.
///
/// # Implementors
///
/// All six pool types implement this trait:
///
/// - `ConstantProductPool` — uniform liquidity across full price range
/// - `ConcentratedLiquidityPool` — liquidity concentrated in tick ranges
/// - `HybridPool` — StableSwap with amplification factor
/// - `WeightedPool` — multi-weight liquidity provision
/// - `DynamicPool` — PMM-managed liquidity
/// - `OrderBookPool` — order book hybrid with maker liquidity
///
/// # Errors
///
/// Methods that can fail return [`Result<T, AmmError>`].  Common error
/// variants include:
///
/// - [`AmmError::InsufficientLiquidity`] — removing more than available
/// - [`AmmError::InvalidLiquidity`] — invalid liquidity parameters
/// - [`AmmError::PositionNotFound`] — position does not exist
/// - [`AmmError::Overflow`] — arithmetic overflow during calculation
pub trait LiquidityPool: SwapPool {
    /// Adds liquidity to the pool.
    ///
    /// The `change` parameter describes the tokens to deposit.  The pool
    /// computes the liquidity minted based on current reserves and the
    /// deposited amounts.
    ///
    /// # Arguments
    ///
    /// - `change` — an [`LiquidityChange::Add`] variant specifying the
    ///   amounts of token A and token B to deposit.
    ///
    /// # Returns
    ///
    /// The [`Amount`] of liquidity units minted for the deposited tokens.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidQuantity`] if both deposit amounts are zero.
    /// - [`AmmError::InvalidLiquidity`] if the change variant is not `Add`.
    /// - [`AmmError::Overflow`] if any intermediate arithmetic overflows.
    fn add_liquidity(&mut self, change: &LiquidityChange) -> Result<Amount, AmmError>;

    /// Removes liquidity from the pool.
    ///
    /// The `change` parameter specifies how much liquidity to withdraw.
    /// The pool computes the token amounts returned proportionally to
    /// the position's share of total liquidity.
    ///
    /// # Arguments
    ///
    /// - `change` — a [`LiquidityChange::Remove`] variant specifying the
    ///   amount of liquidity to withdraw.
    ///
    /// # Returns
    ///
    /// The [`Amount`] of tokens returned (combined value).
    ///
    /// # Errors
    ///
    /// - [`AmmError::InsufficientLiquidity`] if the requested amount
    ///   exceeds the position's balance.
    /// - [`AmmError::InvalidLiquidity`] if the change variant is not
    ///   `Remove` or liquidity is zero.
    /// - [`AmmError::Overflow`] if any intermediate arithmetic overflows.
    fn remove_liquidity(&mut self, change: &LiquidityChange) -> Result<Amount, AmmError>;

    /// Collects accrued trading fees for a position.
    ///
    /// Returns the total fees accumulated by the position since the last
    /// collection.  After collection, the position's fee counters are
    /// reset to zero.  Pool reserves and the price curve are **not**
    /// affected.
    ///
    /// # Idempotency
    ///
    /// Calling this method twice on the same position without
    /// intermediate swaps returns zero the second time.
    ///
    /// # Arguments
    ///
    /// - `position` — the position whose fees should be collected.
    ///
    /// # Returns
    ///
    /// The [`Amount`] of fees collected.
    ///
    /// # Errors
    ///
    /// - [`AmmError::PositionNotFound`] if the position does not exist
    ///   in this pool.
    fn collect_fees(&mut self, position: &Position) -> Result<Amount, AmmError>;

    /// Returns the total active liquidity in the pool.
    ///
    /// This is the sum of all liquidity units across all active
    /// positions.  It does not include withdrawn or inactive positions.
    ///
    /// Used for calculating an individual position's share:
    /// `position_liquidity / total_liquidity`.
    #[must_use]
    fn total_liquidity(&self) -> Liquidity;
}
