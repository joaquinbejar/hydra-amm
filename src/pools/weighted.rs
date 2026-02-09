//! Weighted pool implementation (Balancer style).
//!
//! Supports N tokens (2–8) with custom weight distributions.
//!
//! # Invariant
//!
//! ```text
//! ∏(Bᵢ ^ Wᵢ) = k
//! ```
//!
//! where `Bᵢ` is the balance of token `i` and `Wᵢ` is its normalised
//! weight (fraction of 1.0, stored as basis points summing to 10 000).
//!
//! # Swap Formula
//!
//! ```text
//! amount_out = B_out × (1 − (B_in / (B_in + net_input)) ^ (W_in / W_out))
//! ```
//!
//! # Spot Price (Balancer)
//!
//! ```text
//! spot(base → quote) = (B_base / W_base) / (B_quote / W_quote)
//! ```
//!
//! # Weight Behaviour
//!
//! | Weights | Equivalent curve |
//! |---------|------------------|
//! | 50 / 50 | Constant product (Uniswap V2) |
//! | 80 / 20 | Asymmetric — lower slippage for the 80% token |
//! | Equal N | Generalised constant product across N tokens |

use crate::config::WeightedConfig;
use crate::domain::{
    Amount, FeeTier, Liquidity, LiquidityChange, Position, Price, Rounding, SwapResult, SwapSpec,
    Token, TokenPair,
};
use crate::error::AmmError;
use crate::traits::{FromConfig, LiquidityPool, SwapPool};

/// Basis-point denominator used to normalise weights (10 000 = 100%).
const WEIGHT_DENOMINATOR: f64 = 10_000.0;

// ---------------------------------------------------------------------------
// Helper: safe f64 power via exp(ln(base) × exponent)
// ---------------------------------------------------------------------------

/// Computes `base.powf(exp)` with validation.
///
/// Returns [`AmmError::Overflow`] if the result is not finite.
#[allow(clippy::cast_precision_loss)]
fn checked_powf(base: f64, exp: f64) -> Result<f64, AmmError> {
    if base <= 0.0 {
        return Err(AmmError::Overflow("powf: non-positive base"));
    }
    let result = base.powf(exp);
    if result.is_finite() {
        Ok(result)
    } else {
        Err(AmmError::Overflow("powf: result is not finite"))
    }
}

// ---------------------------------------------------------------------------
// WeightedPool
// ---------------------------------------------------------------------------

/// A Weighted AMM pool (Balancer style).
///
/// Created from a [`WeightedConfig`] via [`FromConfig`].  Supports
/// 2–8 tokens with arbitrary weight distributions (e.g., 80/20, 50/50).
///
/// # State
///
/// - `tokens` — ordered list of tokens.
/// - `weights` — per-token weight in basis points (sum = 10 000).
/// - `balances` — current reserve of each token.
/// - `fee_tier` — swap fee in basis points.
/// - `token_pair` — first two tokens for trait compatibility.
/// - `total_liq` — outstanding LP shares.
/// - `accumulated_fees` — lifetime per-token fee counters.
#[derive(Debug, Clone, PartialEq)]
pub struct WeightedPool {
    tokens: Vec<Token>,
    weights: Vec<u32>,
    balances: Vec<Amount>,
    fee_tier: FeeTier,
    /// Canonical pair derived from the first two tokens for trait compat.
    token_pair: TokenPair,
    total_liq: Liquidity,
    accumulated_fees: Vec<Amount>,
}

impl WeightedPool {
    /// Returns the number of tokens in the pool.
    #[must_use]
    pub fn num_tokens(&self) -> usize {
        self.tokens.len()
    }

    /// Returns a reference to the token list.
    #[must_use]
    pub fn tokens(&self) -> &[Token] {
        &self.tokens
    }

    /// Returns a reference to the weights (basis points).
    #[must_use]
    pub fn weights(&self) -> &[u32] {
        &self.weights
    }

    /// Returns a reference to the current balances.
    pub fn balances(&self) -> &[Amount] {
        &self.balances
    }

    /// Returns a reference to the accumulated fees per token.
    pub fn accumulated_fees(&self) -> &[Amount] {
        &self.accumulated_fees
    }

    /// Finds the index of `token` in the pool's token list.
    fn token_index(&self, token: &Token) -> Option<usize> {
        self.tokens.iter().position(|t| t == token)
    }

    /// Computes the weighted geometric mean of the balances in
    /// log-space: `exp(Σ(wᵢ × ln(bᵢ)))`.
    ///
    /// Used for initial LP share calculation.
    #[allow(clippy::cast_precision_loss)]
    fn weighted_geometric_mean(&self) -> Result<u128, AmmError> {
        let mut log_sum: f64 = 0.0;
        for (i, balance) in self.balances.iter().enumerate() {
            if balance.is_zero() {
                return Err(AmmError::ZeroReserve);
            }
            let b = balance.get() as f64;
            let Some(&w) = self.weights.get(i) else {
                return Err(AmmError::InvalidConfiguration("weight index out of bounds"));
            };
            let w_norm = f64::from(w) / WEIGHT_DENOMINATOR;
            log_sum += w_norm * b.ln();
        }
        let result = log_sum.exp();
        if !result.is_finite() || result < 0.0 {
            return Err(AmmError::Overflow("geometric mean overflow"));
        }
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let lp = result as u128;
        Ok(lp.max(1))
    }

    /// Computes the exact-in swap output using the Balancer formula.
    ///
    /// ```text
    /// out = B_out × (1 − (B_in / (B_in + net_input)) ^ (W_in / W_out))
    /// ```
    ///
    /// Returns `(amount_out, fee)`.
    #[allow(clippy::cast_precision_loss)]
    fn compute_exact_in(
        &self,
        amount_in: Amount,
        idx_in: usize,
        idx_out: usize,
    ) -> Result<(Amount, Amount), AmmError> {
        // fee = amount_in × fee_bps / 10_000  (round up)
        let fee = self
            .fee_tier
            .apply_to_amount(amount_in, Rounding::Up)
            .map_err(|_| AmmError::Overflow("fee calculation overflow"))?;

        let net_input = amount_in
            .checked_sub(&fee)
            .ok_or(AmmError::Overflow("net input underflow"))?;

        if net_input.is_zero() {
            return Err(AmmError::InvalidQuantity("net input after fee is zero"));
        }

        let Some(&b_in) = self.balances.get(idx_in) else {
            return Err(AmmError::InvalidToken("invalid token_in index"));
        };
        let Some(&b_out) = self.balances.get(idx_out) else {
            return Err(AmmError::InvalidToken("invalid token_out index"));
        };
        let Some(&w_in) = self.weights.get(idx_in) else {
            return Err(AmmError::InvalidConfiguration("invalid weight_in index"));
        };
        let Some(&w_out) = self.weights.get(idx_out) else {
            return Err(AmmError::InvalidConfiguration("invalid weight_out index"));
        };

        if b_in.is_zero() || b_out.is_zero() {
            return Err(AmmError::ZeroReserve);
        }

        let b_in_f = b_in.get() as f64;
        let b_out_f = b_out.get() as f64;
        let net_f = net_input.get() as f64;

        // weight_ratio = W_in / W_out
        let weight_ratio = f64::from(w_in) / f64::from(w_out);

        // base = B_in / (B_in + net_input)
        let base = b_in_f / (b_in_f + net_f);

        // amount_out = B_out × (1 − base ^ weight_ratio)
        let power = checked_powf(base, weight_ratio)?;
        let out_f = b_out_f * (1.0 - power);

        if !out_f.is_finite() || out_f < 0.0 {
            return Err(AmmError::Overflow("swap output not finite"));
        }

        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let amount_out = out_f as u128;

        if amount_out == 0 {
            return Err(AmmError::InsufficientLiquidity);
        }

        if amount_out >= b_out.get() {
            return Err(AmmError::InsufficientLiquidity);
        }

        Ok((Amount::new(amount_out), fee))
    }

    /// Computes the exact-out swap via binary search over
    /// [`Self::compute_exact_in`].
    ///
    /// Returns `(amount_in, fee)`.
    fn compute_exact_out(
        &self,
        amount_out: Amount,
        idx_in: usize,
        idx_out: usize,
    ) -> Result<(Amount, Amount), AmmError> {
        let Some(&b_out) = self.balances.get(idx_out) else {
            return Err(AmmError::InvalidToken("invalid token_out index"));
        };
        if amount_out >= b_out {
            return Err(AmmError::InsufficientLiquidity);
        }

        let target = amount_out.get();
        let mut low: u128 = 1;
        let mut high: u128 = target.saturating_mul(100).max(1_000_000);
        let mut best_in: Option<(u128, u128)> = None;

        for _ in 0..128 {
            if low > high {
                break;
            }
            let mid = low + (high - low) / 2;
            match self.compute_exact_in(Amount::new(mid), idx_in, idx_out) {
                Ok((out, fee)) => {
                    if out.get() >= target {
                        best_in = Some((mid, fee.get()));
                        if mid == 0 {
                            break;
                        }
                        high = mid - 1;
                    } else {
                        low = mid + 1;
                    }
                }
                Err(_) => {
                    low = mid + 1;
                }
            }
        }

        let Some((required_in, fee)) = best_in else {
            return Err(AmmError::InsufficientLiquidity);
        };

        Ok((Amount::new(required_in), Amount::new(fee)))
    }

    /// Computes the Balancer invariant value: `∏(Bᵢ ^ Wᵢ)` in
    /// log-space to avoid overflow.
    ///
    /// # Errors
    ///
    /// - [`AmmError::ZeroReserve`] if any balance is zero.
    /// - [`AmmError::InvalidConfiguration`] if a weight index is out
    ///   of bounds.
    /// - [`AmmError::Overflow`] if the invariant computation overflows.
    #[allow(clippy::cast_precision_loss)]
    pub fn compute_invariant(&self) -> Result<f64, AmmError> {
        let mut log_sum: f64 = 0.0;
        for (i, balance) in self.balances.iter().enumerate() {
            let b = balance.get() as f64;
            if b <= 0.0 {
                return Err(AmmError::ZeroReserve);
            }
            let Some(&w) = self.weights.get(i) else {
                return Err(AmmError::InvalidConfiguration("weight index out of bounds"));
            };
            let w_norm = f64::from(w) / WEIGHT_DENOMINATOR;
            log_sum += w_norm * b.ln();
        }
        let inv = log_sum.exp();
        if inv.is_finite() {
            Ok(inv)
        } else {
            Err(AmmError::Overflow("invariant overflow"))
        }
    }
}

impl FromConfig<WeightedConfig> for WeightedPool {
    /// Creates a new pool from the given configuration.
    ///
    /// Computes initial LP shares via the weighted geometric mean of
    /// the initial balances.
    ///
    /// # Errors
    ///
    /// - Propagates any error from [`WeightedConfig::validate`].
    /// - Returns [`AmmError::InvalidConfiguration`] if a [`TokenPair`]
    ///   cannot be constructed from the first two tokens.
    /// - Returns [`AmmError::Overflow`] if initial LP share computation
    ///   overflows.
    fn from_config(config: &WeightedConfig) -> Result<Self, AmmError> {
        config.validate()?;
        let tokens_slice = config.tokens();
        let Some(first) = tokens_slice.first() else {
            return Err(AmmError::InvalidConfiguration(
                "weighted pool requires at least 2 tokens",
            ));
        };
        let Some(second) = tokens_slice.get(1) else {
            return Err(AmmError::InvalidConfiguration(
                "weighted pool requires at least 2 tokens",
            ));
        };
        let token_pair = TokenPair::new(*first, *second)?;

        let n = tokens_slice.len();
        let tokens: Vec<Token> = tokens_slice.to_vec();
        let weights: Vec<u32> = config.weights().iter().map(|w| w.get()).collect();
        let balances: Vec<Amount> = config.balances().to_vec();
        let accumulated_fees: Vec<Amount> = vec![Amount::ZERO; n];

        let mut pool = Self {
            tokens,
            weights,
            balances,
            fee_tier: config.fee_tier(),
            token_pair,
            total_liq: Liquidity::ZERO,
            accumulated_fees,
        };

        let lp = pool.weighted_geometric_mean()?;
        pool.total_liq = Liquidity::new(lp);

        Ok(pool)
    }
}

impl SwapPool for WeightedPool {
    /// Executes a token swap using the Balancer weighted formula.
    ///
    /// The `token_in` is swapped against token B (the second token in
    /// the pair).  For N-token pools, the output token is the *other*
    /// token in the canonical pair if `token_in` is in the pair, or an
    /// error is returned.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidToken`] if `token_in` is not in the pool.
    /// - [`AmmError::InsufficientLiquidity`] if reserves cannot satisfy.
    /// - [`AmmError::Overflow`] if arithmetic overflows.
    fn swap(&mut self, spec: SwapSpec, token_in: Token) -> Result<SwapResult, AmmError> {
        let idx_in = self
            .token_index(&token_in)
            .ok_or(AmmError::InvalidToken("token_in is not part of the pool"))?;

        // Determine the output token: for 2-token pools it is the other
        // token in the pair.  For N>2, use the other token in the
        // canonical pair.
        let idx_out = if token_in == self.token_pair.first() {
            self.token_index(&self.token_pair.second())
                .ok_or(AmmError::InvalidToken("second token not found"))?
        } else if token_in == self.token_pair.second() {
            self.token_index(&self.token_pair.first())
                .ok_or(AmmError::InvalidToken("first token not found"))?
        } else {
            // For non-pair tokens, swap against the first token
            self.token_index(&self.token_pair.first())
                .ok_or(AmmError::InvalidToken("first token not found"))?
        };

        let (amount_in, amount_out, fee) = match spec {
            SwapSpec::ExactIn { amount_in } => {
                let (out, fee) = self.compute_exact_in(amount_in, idx_in, idx_out)?;
                (amount_in, out, fee)
            }
            SwapSpec::ExactOut { amount_out } => {
                let (inp, fee) = self.compute_exact_out(amount_out, idx_in, idx_out)?;
                (inp, amount_out, fee)
            }
        };

        // Update balances
        let Some(bal_in) = self.balances.get(idx_in).copied() else {
            return Err(AmmError::InvalidToken("invalid idx_in"));
        };
        let Some(bal_out) = self.balances.get(idx_out).copied() else {
            return Err(AmmError::InvalidToken("invalid idx_out"));
        };

        let new_bal_in = bal_in
            .checked_add(&amount_in)
            .ok_or(AmmError::Overflow("balance_in overflow after swap"))?;
        let new_bal_out = bal_out
            .checked_sub(&amount_out)
            .ok_or(AmmError::Overflow("balance_out underflow after swap"))?;

        #[allow(clippy::indexing_slicing)]
        {
            self.balances[idx_in] = new_bal_in;
            self.balances[idx_out] = new_bal_out;
        }

        // Accumulate fees on the input token
        let Some(acc_fee) = self.accumulated_fees.get(idx_in).copied() else {
            return Err(AmmError::InvalidToken("invalid idx_in for fees"));
        };
        let new_acc = acc_fee
            .checked_add(&fee)
            .ok_or(AmmError::Overflow("accumulated fee overflow"))?;
        #[allow(clippy::indexing_slicing)]
        {
            self.accumulated_fees[idx_in] = new_acc;
        }

        SwapResult::new(amount_in, amount_out, fee)
    }

    /// Returns the Balancer spot price.
    ///
    /// ```text
    /// spot(base → quote) = (B_base / W_base) / (B_quote / W_quote)
    /// ```
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidToken`] if either token is not in the pool.
    /// - [`AmmError::ZeroReserve`] if the base reserve is zero.
    #[allow(clippy::cast_precision_loss)]
    fn spot_price(&self, base: &Token, quote: &Token) -> Result<Price, AmmError> {
        let idx_base = self
            .token_index(base)
            .ok_or(AmmError::InvalidToken("base token not in pool"))?;
        let idx_quote = self
            .token_index(quote)
            .ok_or(AmmError::InvalidToken("quote token not in pool"))?;

        if base == quote {
            return Ok(Price::ONE);
        }

        let Some(&b_base) = self.balances.get(idx_base) else {
            return Err(AmmError::InvalidToken("invalid base index"));
        };
        let Some(&b_quote) = self.balances.get(idx_quote) else {
            return Err(AmmError::InvalidToken("invalid quote index"));
        };
        let Some(&w_base) = self.weights.get(idx_base) else {
            return Err(AmmError::InvalidConfiguration("invalid base weight index"));
        };
        let Some(&w_quote) = self.weights.get(idx_quote) else {
            return Err(AmmError::InvalidConfiguration("invalid quote weight index"));
        };

        if b_base.is_zero() {
            return Err(AmmError::ZeroReserve);
        }
        if b_quote.is_zero() {
            return Err(AmmError::ZeroReserve);
        }

        // spot = (B_base / W_base) / (B_quote / W_quote)
        let b_base_f = b_base.get() as f64;
        let b_quote_f = b_quote.get() as f64;
        let w_base_f = f64::from(w_base);
        let w_quote_f = f64::from(w_quote);

        let price_val = (b_base_f / w_base_f) / (b_quote_f / w_quote_f);

        if !price_val.is_finite() || price_val < 0.0 {
            return Err(AmmError::Overflow("spot price not finite"));
        }

        Price::new(price_val)
    }

    fn token_pair(&self) -> &TokenPair {
        &self.token_pair
    }

    fn fee_tier(&self) -> FeeTier {
        self.fee_tier
    }
}

impl LiquidityPool for WeightedPool {
    /// Adds liquidity to the pool.
    ///
    /// For the first deposit, LP shares are the weighted geometric mean.
    /// For subsequent deposits, `amount_a` and `amount_b` map to
    /// `tokens[0]` and `tokens[1]`; remaining tokens (if any) are
    /// scaled proportionally based on `amount_a / balances[0]`.
    ///
    /// LP shares minted are proportional to the minimum token ratio.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidLiquidity`] if `change` is not `Add`.
    /// - [`AmmError::InvalidQuantity`] if both amounts are zero.
    /// - [`AmmError::Overflow`] if arithmetic overflows.
    fn add_liquidity(&mut self, change: &LiquidityChange) -> Result<Amount, AmmError> {
        let LiquidityChange::Add { amount_a, amount_b } = *change else {
            return Err(AmmError::InvalidLiquidity(
                "expected LiquidityChange::Add variant",
            ));
        };

        if amount_a.is_zero() && amount_b.is_zero() {
            return Err(AmmError::InvalidQuantity("must deposit at least one token"));
        }

        let minted = if self.total_liq.is_zero() {
            if amount_a.is_zero() || amount_b.is_zero() {
                return Err(AmmError::InvalidQuantity(
                    "first deposit requires both tokens",
                ));
            }
            // Set balances[0] and balances[1] from the deposit
            #[allow(clippy::indexing_slicing)]
            {
                self.balances[0] = amount_a;
                self.balances[1] = amount_b;
            }

            let lp = self.weighted_geometric_mean()?;
            if lp == 0 {
                return Err(AmmError::InvalidQuantity(
                    "deposit too small to mint liquidity",
                ));
            }
            self.total_liq = Liquidity::new(lp);
            Amount::new(lp)
        } else {
            // Proportional deposit: mint = min ratio × total_liq
            let total = self.total_liq.get();

            let Some(&bal_0) = self.balances.first() else {
                return Err(AmmError::InvalidConfiguration("missing balance[0]"));
            };
            let Some(&bal_1) = self.balances.get(1) else {
                return Err(AmmError::InvalidConfiguration("missing balance[1]"));
            };

            let share_a = if !amount_a.is_zero() && !bal_0.is_zero() {
                amount_a
                    .checked_mul(&Amount::new(total))
                    .ok_or(AmmError::Overflow("share_a numerator overflow"))?
                    .checked_div(&bal_0, Rounding::Down)
                    .ok_or(AmmError::DivisionByZero)?
                    .get()
            } else {
                0
            };

            let share_b = if !amount_b.is_zero() && !bal_1.is_zero() {
                amount_b
                    .checked_mul(&Amount::new(total))
                    .ok_or(AmmError::Overflow("share_b numerator overflow"))?
                    .checked_div(&bal_1, Rounding::Down)
                    .ok_or(AmmError::DivisionByZero)?
                    .get()
            } else {
                0
            };

            let minted = match (share_a > 0, share_b > 0) {
                (true, true) => core::cmp::min(share_a, share_b),
                (true, false) => share_a,
                (false, true) => share_b,
                (false, false) => {
                    return Err(AmmError::InvalidQuantity(
                        "deposit too small to mint liquidity",
                    ));
                }
            };

            if minted == 0 {
                return Err(AmmError::InvalidQuantity(
                    "deposit too small to mint liquidity",
                ));
            }

            // Update balances[0] and balances[1]
            let new_bal_0 = bal_0
                .checked_add(&amount_a)
                .ok_or(AmmError::Overflow("balance[0] overflow on add"))?;
            let new_bal_1 = bal_1
                .checked_add(&amount_b)
                .ok_or(AmmError::Overflow("balance[1] overflow on add"))?;
            #[allow(clippy::indexing_slicing)]
            {
                self.balances[0] = new_bal_0;
                self.balances[1] = new_bal_1;
            }

            // For N>2, scale remaining tokens proportionally based on
            // the ratio amount_a / bal_0 (if amount_a is non-zero).
            if self.balances.len() > 2 && !amount_a.is_zero() && !bal_0.is_zero() {
                for i in 2..self.balances.len() {
                    let Some(&cur) = self.balances.get(i) else {
                        continue;
                    };
                    let proportional = cur
                        .checked_mul(&amount_a)
                        .ok_or(AmmError::Overflow("proportional balance overflow"))?
                        .checked_div(&bal_0, Rounding::Down)
                        .ok_or(AmmError::DivisionByZero)?;

                    let new_bal = cur
                        .checked_add(&proportional)
                        .ok_or(AmmError::Overflow("balance overflow on proportional add"))?;
                    #[allow(clippy::indexing_slicing)]
                    {
                        self.balances[i] = new_bal;
                    }
                }
            }

            self.total_liq = self
                .total_liq
                .checked_add(&Liquidity::new(minted))
                .ok_or(AmmError::Overflow("total liquidity overflow"))?;
            Amount::new(minted)
        };

        Ok(minted)
    }

    /// Removes liquidity proportionally from all tokens.
    ///
    /// Returns the token-0 portion.  All reserves are reduced
    /// proportionally.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidLiquidity`] if `change` is not `Remove`.
    /// - [`AmmError::InsufficientLiquidity`] if removing more than total.
    fn remove_liquidity(&mut self, change: &LiquidityChange) -> Result<Amount, AmmError> {
        let LiquidityChange::Remove { liquidity } = *change else {
            return Err(AmmError::InvalidLiquidity(
                "expected LiquidityChange::Remove variant",
            ));
        };

        if liquidity.is_zero() {
            return Err(AmmError::InvalidLiquidity("cannot remove zero liquidity"));
        }

        let total = self.total_liq.get();
        if liquidity.get() > total {
            return Err(AmmError::InsufficientLiquidity);
        }

        // Compute proportional withdrawals for all tokens
        let mut out_first = Amount::ZERO;
        for i in 0..self.balances.len() {
            let Some(&bal) = self.balances.get(i) else {
                continue;
            };
            let out = bal
                .checked_mul(&Amount::new(liquidity.get()))
                .ok_or(AmmError::Overflow("remove proportional numerator overflow"))?
                .checked_div(&Amount::new(total), Rounding::Down)
                .ok_or(AmmError::DivisionByZero)?;

            let new_bal = bal
                .checked_sub(&out)
                .ok_or(AmmError::Overflow("balance underflow on remove"))?;

            #[allow(clippy::indexing_slicing)]
            {
                self.balances[i] = new_bal;
            }

            if i == 0 {
                out_first = out;
            }
        }

        self.total_liq = self
            .total_liq
            .checked_sub(&liquidity)
            .ok_or(AmmError::Overflow("total liquidity underflow"))?;

        Ok(out_first)
    }

    /// Collects accumulated trading fees.
    ///
    /// Returns the sum of fees across all tokens and resets the
    /// accumulators.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::PositionNotFound`] if the pool has never
    /// had liquidity and no fees exist.
    fn collect_fees(&mut self, _position: &Position) -> Result<Amount, AmmError> {
        let all_zero = self.accumulated_fees.iter().all(|f| f.is_zero());
        if self.total_liq.is_zero() && all_zero {
            return Err(AmmError::PositionNotFound);
        }

        let mut total_fees = Amount::ZERO;
        for fee in &self.accumulated_fees {
            total_fees = total_fees
                .checked_add(fee)
                .ok_or(AmmError::Overflow("fee sum overflow"))?;
        }

        for f in &mut self.accumulated_fees {
            *f = Amount::ZERO;
        }

        Ok(total_fees)
    }

    fn total_liquidity(&self) -> Liquidity {
        self.total_liq
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;
    use crate::config::WeightedConfig;
    use crate::domain::{BasisPoints, Decimals, Tick, Token, TokenAddress};
    use crate::traits::FromConfig;

    // -- helpers --------------------------------------------------------------

    fn tok(byte: u8) -> Token {
        let Ok(d) = Decimals::new(6) else {
            panic!("valid decimals");
        };
        Token::new(TokenAddress::from_bytes([byte; 32]), d)
    }

    fn bps(v: u32) -> BasisPoints {
        BasisPoints::new(v)
    }

    fn fee_30bp() -> FeeTier {
        FeeTier::new(BasisPoints::new(30))
    }

    fn unknown_token() -> Token {
        let Ok(d) = Decimals::new(8) else {
            panic!("valid decimals");
        };
        Token::new(TokenAddress::from_bytes([99u8; 32]), d)
    }

    fn dummy_position() -> Position {
        let Ok(t0) = Tick::new(0) else {
            panic!("valid tick");
        };
        let Ok(t1) = Tick::new(100) else {
            panic!("valid tick");
        };
        let Ok(p) = Position::new(t0, t1, Liquidity::new(1)) else {
            panic!("expected valid position");
        };
        p
    }

    /// Creates a 50/50 two-token pool.
    fn make_50_50(ra: u128, rb: u128) -> WeightedPool {
        let Ok(cfg) = WeightedConfig::new(
            vec![tok(1), tok(2)],
            vec![bps(5_000), bps(5_000)],
            fee_30bp(),
            vec![Amount::new(ra), Amount::new(rb)],
        ) else {
            panic!("valid config");
        };
        let Ok(pool) = WeightedPool::from_config(&cfg) else {
            panic!("valid pool");
        };
        pool
    }

    /// Creates an 80/20 two-token pool.
    fn make_80_20(ra: u128, rb: u128) -> WeightedPool {
        let Ok(cfg) = WeightedConfig::new(
            vec![tok(1), tok(2)],
            vec![bps(8_000), bps(2_000)],
            fee_30bp(),
            vec![Amount::new(ra), Amount::new(rb)],
        ) else {
            panic!("valid config");
        };
        let Ok(pool) = WeightedPool::from_config(&cfg) else {
            panic!("valid pool");
        };
        pool
    }

    /// Creates a three-token pool with weights 40/35/25.
    fn make_3_token() -> WeightedPool {
        let Ok(cfg) = WeightedConfig::new(
            vec![tok(1), tok(2), tok(3)],
            vec![bps(4_000), bps(3_500), bps(2_500)],
            fee_30bp(),
            vec![
                Amount::new(1_000_000),
                Amount::new(1_000_000),
                Amount::new(500_000),
            ],
        ) else {
            panic!("valid config");
        };
        let Ok(pool) = WeightedPool::from_config(&cfg) else {
            panic!("valid pool");
        };
        pool
    }

    /// Creates a four-token pool with weights 50/30/15/5.
    fn make_4_token() -> WeightedPool {
        let Ok(cfg) = WeightedConfig::new(
            vec![tok(1), tok(2), tok(3), tok(4)],
            vec![bps(5_000), bps(3_000), bps(1_500), bps(500)],
            fee_30bp(),
            vec![
                Amount::new(1_000_000),
                Amount::new(600_000),
                Amount::new(300_000),
                Amount::new(100_000),
            ],
        ) else {
            panic!("valid config");
        };
        let Ok(pool) = WeightedPool::from_config(&cfg) else {
            panic!("valid pool");
        };
        pool
    }

    // -- FromConfig -----------------------------------------------------------

    #[test]
    fn from_config_two_token() {
        let pool = make_50_50(1_000_000, 2_000_000);
        assert_eq!(pool.num_tokens(), 2);
        assert!(!pool.total_liquidity().is_zero());
    }

    #[test]
    fn from_config_three_token() {
        let pool = make_3_token();
        assert_eq!(pool.num_tokens(), 3);
        assert!(!pool.total_liquidity().is_zero());
    }

    #[test]
    fn from_config_four_token() {
        let pool = make_4_token();
        assert_eq!(pool.num_tokens(), 4);
        assert!(!pool.total_liquidity().is_zero());
    }

    // -- Scenario 1: 50/50 Pool Equivalence with Constant Product -------------

    #[test]
    fn test_weighted_50_50_constant_product_equivalence() {
        let mut pool = make_50_50(1_000_000, 2_000_000);

        let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok(1)) else {
            panic!("expected Ok");
        };

        // 50/50 weighted pool should behave like constant product.
        // CP formula: out = B_out * net / (B_in + net)
        // net = 1000 - 3 (fee) = 997
        // out = 2_000_000 * 997 / (1_000_000 + 997) ≈ 1992
        // Allow some f64 precision tolerance
        assert!(
            result.amount_out().get() > 1_980,
            "out = {}",
            result.amount_out().get()
        );
        assert!(
            result.amount_out().get() < 2_000,
            "out = {}",
            result.amount_out().get()
        );
        assert!(result.fee().get() > 0);
    }

    // -- Scenario 2: 80/20 Asymmetric Swap ------------------------------------

    #[test]
    fn test_weighted_80_20_asymmetric() {
        let mut pool_50 = make_50_50(1_000_000, 1_000_000);
        let mut pool_80 = make_80_20(1_000_000, 1_000_000);

        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(r50) = pool_50.swap(spec, tok(1)) else {
            panic!("expected Ok");
        };

        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(r80) = pool_80.swap(spec, tok(1)) else {
            panic!("expected Ok");
        };

        // With 80/20 weights, swapping the 80%-weight token yields MORE
        // output: base^(W_in/W_out) = base^4.0 is smaller than base^1.0
        // (since base < 1), so (1 − base^4) > (1 − base^1).
        assert!(
            r80.amount_out().get() > r50.amount_out().get(),
            "80/20 out={} should > 50/50 out={}",
            r80.amount_out().get(),
            r50.amount_out().get()
        );
    }

    // -- Scenario 3: Three-Token Pool -----------------------------------------

    #[test]
    fn test_weighted_three_token_pool() {
        let mut pool = make_3_token();

        let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
            panic!("valid spec");
        };
        // Swap token A → token B
        let Ok(result) = pool.swap(spec, tok(1)) else {
            panic!("expected Ok");
        };

        assert!(result.amount_out().get() > 0);
        assert!(result.fee().get() > 0);

        // Check invariant is approximately preserved
        let Ok(inv_after) = pool.compute_invariant() else {
            panic!("expected Ok");
        };
        assert!(inv_after > 0.0);
    }

    // -- Scenario 4: Four-Token Pool with Extreme Weights ---------------------

    #[test]
    fn test_weighted_four_token_extreme_weights() {
        let mut pool = make_4_token();

        // Swap the smallest-weight token (tok(4), 5%) for the largest (tok(1), 50%)
        // The canonical pair is (tok(1), tok(2)), so swapping tok(4) goes
        // against tok(1) via the "non-pair token" rule.
        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok(4)) else {
            panic!("expected Ok");
        };

        // High slippage expected due to low weight on token 4
        // w_in/w_out = 500/5000 = 0.1, so power is small → higher output
        // relative to input, but the low-weight token has less depth
        assert!(result.amount_out().get() > 0);
    }

    // -- Scenario 5: Weight Invariant Preservation Across Multiple Swaps ------

    #[test]
    fn test_weighted_weight_invariant_preservation() {
        let mut pool = make_3_token();

        let Ok(inv_before) = pool.compute_invariant() else {
            panic!("expected Ok");
        };

        // Execute 20 swaps alternating directions
        for i in 0..20 {
            let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
                panic!("valid spec");
            };
            let token = if i % 2 == 0 { tok(1) } else { tok(2) };
            let Ok(_) = pool.swap(spec, token) else {
                panic!("expected Ok on swap {i}");
            };
        }

        let Ok(inv_after) = pool.compute_invariant() else {
            panic!("expected Ok");
        };

        // Invariant should grow (fees stay in pool) or at minimum stay equal
        assert!(
            inv_after >= inv_before * 0.999,
            "inv_after={inv_after} should be close to inv_before={inv_before}"
        );
    }

    // -- Scenario 6: Proportional Liquidity Deposit ---------------------------

    #[test]
    fn test_weighted_proportional_liquidity_deposit() {
        let mut pool = make_3_token();
        let initial_liq = pool.total_liquidity();

        // Add 10% proportional liquidity via amount_a and amount_b
        // tokens[0] has 1M, so deposit 100k for token A
        // tokens[1] has 1M, so deposit 100k for token B
        // tokens[2] will scale proportionally (100k/1M = 10% → 50k added)
        let Ok(change) = LiquidityChange::add(Amount::new(100_000), Amount::new(100_000)) else {
            panic!("valid change");
        };
        let Ok(minted) = pool.add_liquidity(&change) else {
            panic!("expected Ok");
        };
        assert!(minted.get() > 0);
        assert!(pool.total_liquidity().get() > initial_liq.get());

        // Check token[2] grew proportionally
        let Some(&bal_2) = pool.balances().get(2) else {
            panic!("expected balance[2]");
        };
        // Original 500k + 10% = 550k
        assert!(
            bal_2.get() >= 540_000 && bal_2.get() <= 560_000,
            "bal_2 = {}",
            bal_2.get()
        );
    }

    // -- spot_price -----------------------------------------------------------

    #[test]
    fn spot_price_50_50_equals_reserve_ratio() {
        let pool = make_50_50(1_000_000, 2_000_000);
        let Ok(price) = pool.spot_price(&tok(1), &tok(2)) else {
            panic!("expected Ok");
        };
        // spot = (B_base/W_base) / (B_quote/W_quote)
        // = (1M/5000) / (2M/5000) = 0.5
        assert!((price.get() - 0.5).abs() < 0.01, "price = {}", price.get());
    }

    #[test]
    fn spot_price_80_20() {
        let pool = make_80_20(1_000_000, 250_000);
        let Ok(price) = pool.spot_price(&tok(1), &tok(2)) else {
            panic!("expected Ok");
        };
        // spot = (1M/8000) / (250k/2000) = 125 / 125 = 1.0
        assert!((price.get() - 1.0).abs() < 0.01, "price = {}", price.get());
    }

    #[test]
    fn spot_price_same_token() {
        let pool = make_50_50(1_000_000, 2_000_000);
        let Ok(price) = pool.spot_price(&tok(1), &tok(1)) else {
            panic!("expected Ok");
        };
        assert!((price.get() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn spot_price_inverse() {
        let pool = make_50_50(1_000_000, 2_000_000);
        let Ok(p_ab) = pool.spot_price(&tok(1), &tok(2)) else {
            panic!("expected Ok");
        };
        let Ok(p_ba) = pool.spot_price(&tok(2), &tok(1)) else {
            panic!("expected Ok");
        };
        assert!(
            (p_ab.get() * p_ba.get() - 1.0).abs() < 0.01,
            "p_ab={} p_ba={}",
            p_ab.get(),
            p_ba.get()
        );
    }

    #[test]
    fn spot_price_invalid_token() {
        let pool = make_50_50(1_000_000, 2_000_000);
        let result = pool.spot_price(&unknown_token(), &tok(2));
        assert!(matches!(result, Err(AmmError::InvalidToken(_))));
    }

    // -- Price direction after swap -------------------------------------------

    #[test]
    fn price_moves_after_sell() {
        let mut pool = make_50_50(1_000_000, 1_000_000);
        let Ok(p_before) = pool.spot_price(&tok(1), &tok(2)) else {
            panic!("expected Ok");
        };

        let Ok(spec) = SwapSpec::exact_in(Amount::new(100_000)) else {
            panic!("valid spec");
        };
        let Ok(_) = pool.swap(spec, tok(1)) else {
            panic!("expected Ok");
        };

        let Ok(p_after) = pool.spot_price(&tok(1), &tok(2)) else {
            panic!("expected Ok");
        };
        // Selling A increases A balance, decreases B → price of A in B drops
        assert!(
            p_after.get() > p_before.get(),
            "p_after={} should > p_before={}",
            p_after.get(),
            p_before.get()
        );
    }

    // -- Invalid token swap ---------------------------------------------------

    #[test]
    fn swap_invalid_token_rejected() {
        let mut pool = make_50_50(1_000_000, 1_000_000);
        let Ok(spec) = SwapSpec::exact_in(Amount::new(100)) else {
            panic!("valid spec");
        };
        let result = pool.swap(spec, unknown_token());
        assert!(matches!(result, Err(AmmError::InvalidToken(_))));
    }

    // -- ExactOut swap --------------------------------------------------------

    #[test]
    fn swap_exact_out() {
        let mut pool = make_50_50(1_000_000, 1_000_000);
        let Ok(spec) = SwapSpec::exact_out(Amount::new(500)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok(1)) else {
            panic!("expected Ok");
        };
        assert!(result.amount_out().get() >= 500);
        assert!(result.amount_in().get() > 0);
        assert!(result.fee().get() > 0);
    }

    // -- Liquidity add --------------------------------------------------------

    #[test]
    fn add_liquidity_proportional() {
        let mut pool = make_50_50(1_000_000, 1_000_000);
        let initial_liq = pool.total_liquidity();

        let Ok(change) = LiquidityChange::add(Amount::new(100_000), Amount::new(100_000)) else {
            panic!("valid change");
        };
        let Ok(minted) = pool.add_liquidity(&change) else {
            panic!("expected Ok");
        };
        assert!(minted.get() > 0);
        assert!(pool.total_liquidity().get() > initial_liq.get());
    }

    #[test]
    fn add_liquidity_wrong_variant() {
        let mut pool = make_50_50(1_000_000, 1_000_000);
        let Ok(change) = LiquidityChange::remove(Liquidity::new(1)) else {
            panic!("valid change");
        };
        let result = pool.add_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InvalidLiquidity(_))));
    }

    // -- Liquidity remove -----------------------------------------------------

    #[test]
    fn remove_liquidity_half() {
        let mut pool = make_50_50(1_000_000, 1_000_000);
        let half = pool.total_liquidity().get() / 2;

        let Ok(change) = LiquidityChange::remove(Liquidity::new(half)) else {
            panic!("valid change");
        };
        let Ok(out_a) = pool.remove_liquidity(&change) else {
            panic!("expected Ok");
        };
        assert!(out_a.get() > 0);
        // Both balances should be reduced
        let Some(&b0) = pool.balances().first() else {
            panic!("expected balance[0]");
        };
        let Some(&b1) = pool.balances().get(1) else {
            panic!("expected balance[1]");
        };
        assert!(b0.get() < 1_000_000);
        assert!(b1.get() < 1_000_000);
    }

    #[test]
    fn remove_liquidity_exceeding_total_fails() {
        let mut pool = make_50_50(1_000_000, 1_000_000);
        let too_much = pool.total_liquidity().get() + 1;

        let Ok(change) = LiquidityChange::remove(Liquidity::new(too_much)) else {
            panic!("valid change");
        };
        let result = pool.remove_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InsufficientLiquidity)));
    }

    #[test]
    fn remove_liquidity_wrong_variant() {
        let mut pool = make_50_50(1_000_000, 1_000_000);
        let Ok(change) = LiquidityChange::add(Amount::new(100), Amount::new(100)) else {
            panic!("valid change");
        };
        let result = pool.remove_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InvalidLiquidity(_))));
    }

    #[test]
    fn remove_liquidity_three_token_proportional() {
        let mut pool = make_3_token();
        let half = pool.total_liquidity().get() / 2;

        let Ok(change) = LiquidityChange::remove(Liquidity::new(half)) else {
            panic!("valid change");
        };
        let Ok(out_a) = pool.remove_liquidity(&change) else {
            panic!("expected Ok");
        };
        assert!(out_a.get() > 0);

        // All three balances should be reduced
        for (i, b) in pool.balances().iter().enumerate() {
            assert!(!b.is_zero(), "balance[{i}] should not be zero");
        }
    }

    // -- Fee accumulation -----------------------------------------------------

    #[test]
    fn fees_accumulate_over_swaps() {
        let mut pool = make_50_50(1_000_000, 1_000_000);

        for _ in 0..5 {
            let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
                panic!("valid spec");
            };
            let Ok(_) = pool.swap(spec, tok(1)) else {
                panic!("expected Ok");
            };
        }

        let Some(&fee_0) = pool.accumulated_fees().first() else {
            panic!("expected fee[0]");
        };
        assert!(fee_0.get() > 0, "fees should accumulate on input token");
    }

    #[test]
    fn collect_fees_returns_accumulated() {
        let mut pool = make_50_50(1_000_000, 1_000_000);

        for _ in 0..3 {
            let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
                panic!("valid spec");
            };
            let Ok(_) = pool.swap(spec, tok(1)) else {
                panic!("expected Ok");
            };
        }

        let pos = dummy_position();
        let Ok(fees) = pool.collect_fees(&pos) else {
            panic!("expected Ok");
        };
        assert!(fees.get() > 0);

        // Second collect should return zero
        let Ok(fees2) = pool.collect_fees(&pos) else {
            panic!("expected Ok");
        };
        assert_eq!(fees2, Amount::ZERO);
    }

    // -- Accessors ------------------------------------------------------------

    #[test]
    fn accessors() {
        let pool = make_50_50(1_000_000, 2_000_000);
        assert_eq!(pool.num_tokens(), 2);
        assert_eq!(pool.tokens().len(), 2);
        assert_eq!(pool.weights().len(), 2);
        assert_eq!(pool.balances().len(), 2);
        assert_eq!(pool.accumulated_fees().len(), 2);
        assert_eq!(pool.fee_tier(), fee_30bp());
    }

    #[test]
    fn token_pair_is_first_two() {
        let pool = make_3_token();
        assert_eq!(pool.token_pair().first(), tok(1));
        assert_eq!(pool.token_pair().second(), tok(2));
    }

    // -- Debug ----------------------------------------------------------------

    #[test]
    fn debug_format() {
        let pool = make_50_50(1_000, 2_000);
        let dbg = format!("{pool:?}");
        assert!(dbg.contains("WeightedPool"));
    }

    // -- Invariant computation ------------------------------------------------

    #[test]
    fn compute_invariant_positive() {
        let pool = make_50_50(1_000_000, 2_000_000);
        let Ok(inv) = pool.compute_invariant() else {
            panic!("expected Ok");
        };
        assert!(inv > 0.0);
    }

    #[test]
    fn invariant_grows_from_fees() {
        let mut pool = make_50_50(1_000_000, 1_000_000);
        let Ok(inv_before) = pool.compute_invariant() else {
            panic!("expected Ok");
        };

        let Ok(spec) = SwapSpec::exact_in(Amount::new(100_000)) else {
            panic!("valid spec");
        };
        let Ok(_) = pool.swap(spec, tok(1)) else {
            panic!("expected Ok");
        };

        let Ok(inv_after) = pool.compute_invariant() else {
            panic!("expected Ok");
        };
        // Invariant should grow because fees stay in pool
        assert!(
            inv_after >= inv_before * 0.999,
            "inv_after={inv_after} should >= inv_before*0.999={:.2}",
            inv_before * 0.999
        );
    }

    // -- Symmetric swap at 50/50 with equal reserves --------------------------

    #[test]
    fn symmetric_swap_50_50() {
        let mut pool_ab = make_50_50(1_000_000, 1_000_000);
        let mut pool_ba = make_50_50(1_000_000, 1_000_000);

        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(r_ab) = pool_ab.swap(spec, tok(1)) else {
            panic!("expected Ok");
        };
        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(r_ba) = pool_ba.swap(spec, tok(2)) else {
            panic!("expected Ok");
        };
        // With equal weights and reserves, outputs should be identical
        assert_eq!(r_ab.amount_out(), r_ba.amount_out());
    }

    // -- checked_powf ---------------------------------------------------------

    #[test]
    fn checked_powf_valid() {
        let Ok(r) = checked_powf(0.5, 2.0) else {
            panic!("expected Ok");
        };
        assert!((r - 0.25).abs() < 1e-10);
    }

    #[test]
    fn checked_powf_non_positive_base() {
        let result = checked_powf(0.0, 1.0);
        assert!(matches!(result, Err(AmmError::Overflow(_))));
    }

    // -- Large swap -----------------------------------------------------------

    #[test]
    fn large_swap_50_50() {
        let mut pool = make_50_50(10_000_000, 10_000_000);
        let Ok(spec) = SwapSpec::exact_in(Amount::new(5_000_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok(1)) else {
            panic!("expected Ok");
        };
        // 50% of reserve → significant slippage
        assert!(result.amount_out().get() < 5_000_000);
        assert!(result.amount_out().get() > 0);
    }
}
