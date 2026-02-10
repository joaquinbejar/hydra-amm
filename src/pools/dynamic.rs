//! Dynamic / Proactive Market Maker pool implementation (DODO style).
//!
//! Uses an external price oracle and a slippage coefficient `k` to blend
//! between oracle-only pricing and constant-product AMM pricing.
//!
//! # Pricing Model
//!
//! The effective output for a swap is computed as:
//!
//! ```text
//! output = (1 − k) × oracle_output + k × amm_output
//! ```
//!
//! where:
//! - `oracle_output` is the output at the oracle price (zero slippage)
//! - `amm_output` is the output from the constant-product formula
//! - `k ∈ [0, 1]` controls the blend
//!
//! | k     | Behaviour                                     |
//! |-------|-----------------------------------------------|
//! | k = 0 | Pure oracle pricing (infinite liquidity)      |
//! | k = 1 | Pure constant product (oracle ignored)        |
//!
//! # Swap Algorithm
//!
//! 1. Deduct fee from input → `net_input`
//! 2. Determine direction (sell base vs buy base)
//! 3. Compute oracle component and AMM component
//! 4. Blend: `output = (1 − k) × oracle_out + k × amm_out`
//! 5. Update reserves

use crate::config::DynamicConfig;
use crate::domain::{
    Amount, FeeTier, Liquidity, LiquidityChange, Position, Price, Rounding, SwapResult, SwapSpec,
    Token, TokenPair,
};
use crate::error::AmmError;
use crate::traits::{FromConfig, LiquidityPool, SwapPool};

/// A Dynamic (Proactive Market Maker) pool.
///
/// Created from a [`DynamicConfig`] via [`FromConfig`].  Uses an oracle
/// price and slippage coefficient `k` to blend between oracle pricing
/// and constant-product AMM pricing.
///
/// # State
///
/// - `base_reserve` / `quote_reserve` — current token balances
/// - `target_base` / `target_quote` — initial target inventory levels
/// - `oracle_price` — external reference price (updatable)
/// - `k` — slippage coefficient ∈ [0, 1]
/// - `total_liq` — outstanding LP shares
/// - `accumulated_fees_base` / `accumulated_fees_quote` — fee counters
#[derive(Debug, Clone, PartialEq)]
pub struct DynamicPool {
    token_pair: TokenPair,
    fee_tier: FeeTier,
    oracle_price: Price,
    k: f64,
    base_reserve: Amount,
    quote_reserve: Amount,
    target_base: Amount,
    target_quote: Amount,
    total_liq: Liquidity,
    accumulated_fees_base: Amount,
    accumulated_fees_quote: Amount,
}

impl DynamicPool {
    /// Returns the current base token reserve.
    pub const fn base_reserve(&self) -> Amount {
        self.base_reserve
    }

    /// Returns the current quote token reserve.
    pub const fn quote_reserve(&self) -> Amount {
        self.quote_reserve
    }

    /// Returns the target base reserve (initial inventory level).
    pub const fn target_base(&self) -> Amount {
        self.target_base
    }

    /// Returns the target quote reserve (initial inventory level).
    pub const fn target_quote(&self) -> Amount {
        self.target_quote
    }

    /// Returns the oracle reference price.
    pub const fn oracle_price(&self) -> Price {
        self.oracle_price
    }

    /// Returns the slippage coefficient `k` ∈ [0, 1].
    pub const fn slippage_coefficient(&self) -> f64 {
        self.k
    }

    /// Returns accumulated fees for the base token.
    pub const fn accumulated_fees_base(&self) -> Amount {
        self.accumulated_fees_base
    }

    /// Returns accumulated fees for the quote token.
    pub const fn accumulated_fees_quote(&self) -> Amount {
        self.accumulated_fees_quote
    }

    /// Updates the oracle reference price.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::InvalidPrice`] if the new price is zero or
    /// negative.
    pub fn set_oracle_price(&mut self, price: Price) -> Result<(), AmmError> {
        if price.get() <= 0.0 {
            return Err(AmmError::InvalidPrice("oracle price must be positive"));
        }
        self.oracle_price = price;
        Ok(())
    }

    /// Integer square root via Newton's method.
    ///
    /// Returns `None` only if the implementation overflows, which cannot
    /// happen for valid `u128` inputs.
    fn isqrt(n: u128) -> Option<u128> {
        if n == 0 {
            return Some(0);
        }
        let mut x = n;
        let mut y = x.div_ceil(2);
        while y < x {
            x = y;
            y = (x + n / x) / 2;
        }
        Some(x)
    }

    /// Computes exact-in swap for selling base (A → B).
    ///
    /// - `oracle_out = net_input × oracle_price`
    /// - `amm_out = quote_reserve × net_input / (base_reserve + net_input)`
    /// - `output = (1 − k) × oracle_out + k × amm_out`
    ///
    /// Returns `(amount_out, fee)`.
    #[allow(
        clippy::cast_precision_loss,
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss
    )]
    fn compute_sell_base_exact_in(&self, amount_in: Amount) -> Result<(Amount, Amount), AmmError> {
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

        let net_f64 = net_input.get() as f64;
        let oracle = self.oracle_price.get();

        // Oracle component: selling base at oracle price yields quote
        let oracle_out = net_f64 * oracle;

        // AMM component (constant product): Q × net / (B + net)
        let b = self.base_reserve.get() as f64;
        let q = self.quote_reserve.get() as f64;
        let amm_out = q * net_f64 / (b + net_f64);

        // Blend
        let blended = (1.0 - self.k) * oracle_out + self.k * amm_out;

        if !blended.is_finite() || blended < 0.0 {
            return Err(AmmError::Overflow("blended output not finite"));
        }

        let amount_out = blended as u128;
        if amount_out == 0 {
            return Err(AmmError::InsufficientLiquidity);
        }

        if amount_out >= self.quote_reserve.get() {
            return Err(AmmError::InsufficientLiquidity);
        }

        Ok((Amount::new(amount_out), fee))
    }

    /// Computes exact-in swap for buying base (B → A).
    ///
    /// - `oracle_out = net_input / oracle_price`
    /// - `amm_out = base_reserve × net_input / (quote_reserve + net_input)`
    /// - `output = (1 − k) × oracle_out + k × amm_out`
    ///
    /// Returns `(amount_out, fee)`.
    #[allow(
        clippy::cast_precision_loss,
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss
    )]
    fn compute_buy_base_exact_in(&self, amount_in: Amount) -> Result<(Amount, Amount), AmmError> {
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

        let net_f64 = net_input.get() as f64;
        let oracle = self.oracle_price.get();

        if oracle <= 0.0 {
            return Err(AmmError::InvalidPrice("oracle price must be positive"));
        }

        // Oracle component: buying base at oracle price
        let oracle_out = net_f64 / oracle;

        // AMM component (constant product): B × net / (Q + net)
        let b = self.base_reserve.get() as f64;
        let q = self.quote_reserve.get() as f64;
        let amm_out = b * net_f64 / (q + net_f64);

        // Blend
        let blended = (1.0 - self.k) * oracle_out + self.k * amm_out;

        if !blended.is_finite() || blended < 0.0 {
            return Err(AmmError::Overflow("blended output not finite"));
        }

        let amount_out = blended as u128;
        if amount_out == 0 {
            return Err(AmmError::InsufficientLiquidity);
        }

        if amount_out >= self.base_reserve.get() {
            return Err(AmmError::InsufficientLiquidity);
        }

        Ok((Amount::new(amount_out), fee))
    }

    /// Computes exact-out for selling base via binary search over
    /// [`Self::compute_sell_base_exact_in`].
    ///
    /// Returns `(amount_in, fee)`.
    fn compute_exact_out_sell_base(
        &self,
        amount_out: Amount,
    ) -> Result<(Amount, Amount), AmmError> {
        if amount_out.get() >= self.quote_reserve.get() {
            return Err(AmmError::InsufficientLiquidity);
        }

        let mut lo: u128 = 1;
        let mut hi: u128 = amount_out.get().saturating_mul(100).max(1_000_000);
        let mut best: Option<(u128, u128)> = None;

        for _ in 0..128 {
            if lo > hi {
                break;
            }
            let mid = lo + (hi - lo) / 2;
            if let Ok((out, fee)) = self.compute_sell_base_exact_in(Amount::new(mid)) {
                if out.get() >= amount_out.get() {
                    best = Some((mid, fee.get()));
                    hi = mid.saturating_sub(1);
                } else {
                    lo = mid.saturating_add(1);
                }
            } else {
                lo = mid.saturating_add(1);
            }
        }

        let Some((required_in, fee)) = best else {
            return Err(AmmError::InsufficientLiquidity);
        };

        Ok((Amount::new(required_in), Amount::new(fee)))
    }

    /// Computes exact-out for buying base via binary search over
    /// [`Self::compute_buy_base_exact_in`].
    ///
    /// Returns `(amount_in, fee)`.
    fn compute_exact_out_buy_base(&self, amount_out: Amount) -> Result<(Amount, Amount), AmmError> {
        if amount_out.get() >= self.base_reserve.get() {
            return Err(AmmError::InsufficientLiquidity);
        }

        let mut lo: u128 = 1;
        let mut hi: u128 = amount_out.get().saturating_mul(100).max(1_000_000);
        let mut best: Option<(u128, u128)> = None;

        for _ in 0..128 {
            if lo > hi {
                break;
            }
            let mid = lo + (hi - lo) / 2;
            if let Ok((out, fee)) = self.compute_buy_base_exact_in(Amount::new(mid)) {
                if out.get() >= amount_out.get() {
                    best = Some((mid, fee.get()));
                    hi = mid.saturating_sub(1);
                } else {
                    lo = mid.saturating_add(1);
                }
            } else {
                lo = mid.saturating_add(1);
            }
        }

        let Some((required_in, fee)) = best else {
            return Err(AmmError::InsufficientLiquidity);
        };

        Ok((Amount::new(required_in), Amount::new(fee)))
    }
}

impl FromConfig<DynamicConfig> for DynamicPool {
    /// Creates a new pool from the given configuration.
    ///
    /// Initial LP shares are set to `√(base_reserve × quote_reserve)`.
    /// Target reserves are set equal to the initial reserves.
    ///
    /// # Errors
    ///
    /// - Propagates any error from [`DynamicConfig::validate`].
    /// - Returns [`AmmError::Overflow`] if the initial invariant overflows.
    fn from_config(config: &DynamicConfig) -> Result<Self, AmmError> {
        config.validate()?;

        let ra = config.base_reserve();
        let rb = config.quote_reserve();

        // Initial LP shares = sqrt(base × quote)
        let product = ra
            .checked_mul(&rb)
            .ok_or(AmmError::Overflow("initial product overflow"))?;
        let lp = Self::isqrt(product.get()).ok_or(AmmError::Overflow("isqrt overflow"))?;

        Ok(Self {
            token_pair: *config.token_pair(),
            fee_tier: config.fee_tier(),
            oracle_price: config.oracle_price(),
            k: config.slippage_coefficient(),
            base_reserve: ra,
            quote_reserve: rb,
            target_base: ra,
            target_quote: rb,
            total_liq: Liquidity::new(lp),
            accumulated_fees_base: Amount::ZERO,
            accumulated_fees_quote: Amount::ZERO,
        })
    }
}

impl SwapPool for DynamicPool {
    /// Executes a token swap on the dynamic PMM pool.
    ///
    /// The output is a blend of oracle pricing and constant-product
    /// AMM pricing, controlled by the slippage coefficient `k`.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidToken`] if `token_in` is not in the pool pair.
    /// - [`AmmError::InsufficientLiquidity`] if reserves cannot satisfy
    ///   the swap.
    /// - [`AmmError::Overflow`] if any arithmetic overflows.
    fn swap(&mut self, spec: SwapSpec, token_in: Token) -> Result<SwapResult, AmmError> {
        if !self.token_pair.contains(&token_in) {
            return Err(AmmError::InvalidToken(
                "token_in is not part of the pool pair",
            ));
        }

        let is_sell_base = token_in == self.token_pair.first();

        let (amount_in, amount_out, fee) = match spec {
            SwapSpec::ExactIn { amount_in } => {
                let (out, fee) = if is_sell_base {
                    self.compute_sell_base_exact_in(amount_in)?
                } else {
                    self.compute_buy_base_exact_in(amount_in)?
                };
                (amount_in, out, fee)
            }
            SwapSpec::ExactOut { amount_out } => {
                let (inp, fee) = if is_sell_base {
                    self.compute_exact_out_sell_base(amount_out)?
                } else {
                    self.compute_exact_out_buy_base(amount_out)?
                };
                (inp, amount_out, fee)
            }
        };

        // Update reserves
        if is_sell_base {
            self.base_reserve = self
                .base_reserve
                .checked_add(&amount_in)
                .ok_or(AmmError::Overflow("base reserve overflow after swap"))?;
            self.quote_reserve = self
                .quote_reserve
                .checked_sub(&amount_out)
                .ok_or(AmmError::Overflow("quote reserve underflow after swap"))?;
            self.accumulated_fees_base = self
                .accumulated_fees_base
                .checked_add(&fee)
                .ok_or(AmmError::Overflow("accumulated fee overflow"))?;
        } else {
            self.quote_reserve = self
                .quote_reserve
                .checked_add(&amount_in)
                .ok_or(AmmError::Overflow("quote reserve overflow after swap"))?;
            self.base_reserve = self
                .base_reserve
                .checked_sub(&amount_out)
                .ok_or(AmmError::Overflow("base reserve underflow after swap"))?;
            self.accumulated_fees_quote = self
                .accumulated_fees_quote
                .checked_add(&fee)
                .ok_or(AmmError::Overflow("accumulated fee overflow"))?;
        }

        SwapResult::new(amount_in, amount_out, fee)
    }

    /// Returns the blended spot price.
    ///
    /// ```text
    /// spot(base, quote) = (1 − k) × oracle + k × (Q / B)
    /// ```
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidToken`] if either token is not in the pair.
    /// - [`AmmError::ZeroReserve`] if the base reserve is zero.
    #[allow(clippy::cast_precision_loss)]
    fn spot_price(&self, base: &Token, quote: &Token) -> Result<Price, AmmError> {
        if !self.token_pair.contains(base) {
            return Err(AmmError::InvalidToken("base token not in pool pair"));
        }
        if !self.token_pair.contains(quote) {
            return Err(AmmError::InvalidToken("quote token not in pool pair"));
        }
        if base == quote {
            return Ok(Price::ONE);
        }

        if self.base_reserve.is_zero() {
            return Err(AmmError::ZeroReserve);
        }

        let oracle = self.oracle_price.get();
        let amm_price = self.quote_reserve.get() as f64 / self.base_reserve.get() as f64;

        // Blended spot: price of first token in terms of second token
        let price_base_in_quote = (1.0 - self.k) * oracle + self.k * amm_price;

        if *base == self.token_pair.first() {
            Price::new(price_base_in_quote)
        } else {
            // Inverse: price of quote in base terms
            if price_base_in_quote <= 0.0 {
                return Err(AmmError::DivisionByZero);
            }
            Price::new(1.0 / price_base_in_quote)
        }
    }

    fn token_pair(&self) -> &TokenPair {
        &self.token_pair
    }

    fn fee_tier(&self) -> FeeTier {
        self.fee_tier
    }
}

impl LiquidityPool for DynamicPool {
    /// Adds liquidity to the pool.
    ///
    /// For the first deposit (total liquidity is zero), LP shares equal
    /// `√(amount_a × amount_b)`.  For subsequent deposits, shares are
    /// proportional to the smaller ratio `min(Δa/Ra, Δb/Rb) × L`.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidLiquidity`] if `change` is not an `Add`
    ///   variant.
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
            // First deposit: LP = sqrt(amount_a * amount_b)
            if amount_a.is_zero() || amount_b.is_zero() {
                return Err(AmmError::InvalidQuantity(
                    "first deposit requires both tokens",
                ));
            }
            let product = amount_a
                .checked_mul(&amount_b)
                .ok_or(AmmError::Overflow("initial product overflow"))?;
            let lp = Self::isqrt(product.get()).ok_or(AmmError::Overflow("isqrt overflow"))?;
            if lp == 0 {
                return Err(AmmError::InvalidQuantity(
                    "deposit too small to mint liquidity",
                ));
            }
            self.base_reserve = amount_a;
            self.quote_reserve = amount_b;
            self.target_base = amount_a;
            self.target_quote = amount_b;
            self.total_liq = Liquidity::new(lp);
            Amount::new(lp)
        } else {
            // Proportional deposit: mint = min(da/Ra, db/Rb) * L
            let total = self.total_liq.get();

            let share_a = if !amount_a.is_zero() && !self.base_reserve.is_zero() {
                let numer = amount_a
                    .checked_mul(&Amount::new(total))
                    .ok_or(AmmError::Overflow("share_a numerator overflow"))?;
                numer
                    .checked_div(&self.base_reserve, Rounding::Down)
                    .ok_or(AmmError::DivisionByZero)?
                    .get()
            } else {
                0
            };

            let share_b = if !amount_b.is_zero() && !self.quote_reserve.is_zero() {
                let numer = amount_b
                    .checked_mul(&Amount::new(total))
                    .ok_or(AmmError::Overflow("share_b numerator overflow"))?;
                numer
                    .checked_div(&self.quote_reserve, Rounding::Down)
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

            self.base_reserve = self
                .base_reserve
                .checked_add(&amount_a)
                .ok_or(AmmError::Overflow("base reserve overflow on add"))?;
            self.quote_reserve = self
                .quote_reserve
                .checked_add(&amount_b)
                .ok_or(AmmError::Overflow("quote reserve overflow on add"))?;
            self.total_liq = self
                .total_liq
                .checked_add(&Liquidity::new(minted))
                .ok_or(AmmError::Overflow("total liquidity overflow"))?;
            Amount::new(minted)
        };

        Ok(minted)
    }

    /// Removes liquidity from the pool.
    ///
    /// Returns the proportional share of the base token reserve:
    /// `amount_base = base_reserve × liquidity / total_liquidity`.
    /// The quote token is returned implicitly via the reserve update.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidLiquidity`] if `change` is not a `Remove`
    ///   variant or if `liquidity` exceeds the pool's total.
    /// - [`AmmError::Overflow`] if arithmetic overflows.
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

        // amount_base = base_reserve * liq / total  (round down)
        let out_a = self
            .base_reserve
            .checked_mul(&Amount::new(liquidity.get()))
            .ok_or(AmmError::Overflow("remove base numerator overflow"))?
            .checked_div(&Amount::new(total), Rounding::Down)
            .ok_or(AmmError::DivisionByZero)?;

        let out_b = self
            .quote_reserve
            .checked_mul(&Amount::new(liquidity.get()))
            .ok_or(AmmError::Overflow("remove quote numerator overflow"))?
            .checked_div(&Amount::new(total), Rounding::Down)
            .ok_or(AmmError::DivisionByZero)?;

        self.base_reserve = self
            .base_reserve
            .checked_sub(&out_a)
            .ok_or(AmmError::Overflow("base reserve underflow on remove"))?;
        self.quote_reserve = self
            .quote_reserve
            .checked_sub(&out_b)
            .ok_or(AmmError::Overflow("quote reserve underflow on remove"))?;
        self.total_liq = self
            .total_liq
            .checked_sub(&liquidity)
            .ok_or(AmmError::Overflow("total liquidity underflow"))?;

        Ok(out_a)
    }

    /// Collects accumulated fees across both tokens.
    ///
    /// Returns the sum of base and quote fees, then resets both
    /// accumulators to zero.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::Overflow`] if the fee sum overflows.
    fn collect_fees(&mut self, _position: &Position) -> Result<Amount, AmmError> {
        let total = self
            .accumulated_fees_base
            .checked_add(&self.accumulated_fees_quote)
            .ok_or(AmmError::Overflow("fee sum overflow"))?;

        self.accumulated_fees_base = Amount::ZERO;
        self.accumulated_fees_quote = Amount::ZERO;

        Ok(total)
    }

    fn total_liquidity(&self) -> Liquidity {
        self.total_liq
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;
    use crate::config::DynamicConfig;
    use crate::domain::{BasisPoints, Decimals, Tick, Token, TokenAddress};
    use crate::traits::FromConfig;

    // -- helpers --------------------------------------------------------------

    fn tok_a() -> Token {
        let Ok(d) = Decimals::new(6) else {
            panic!("valid decimals");
        };
        Token::new(TokenAddress::from_bytes([1u8; 32]), d)
    }

    fn tok_b() -> Token {
        let Ok(d) = Decimals::new(18) else {
            panic!("valid decimals");
        };
        Token::new(TokenAddress::from_bytes([2u8; 32]), d)
    }

    fn unknown_token() -> Token {
        let Ok(d) = Decimals::new(8) else {
            panic!("valid decimals");
        };
        Token::new(TokenAddress::from_bytes([99u8; 32]), d)
    }

    fn make_pair() -> TokenPair {
        let Ok(pair) = TokenPair::new(tok_a(), tok_b()) else {
            panic!("valid pair");
        };
        pair
    }

    fn zero_fee() -> FeeTier {
        FeeTier::new(BasisPoints::new(0))
    }

    fn fee_30bp() -> FeeTier {
        FeeTier::new(BasisPoints::new(30))
    }

    fn oracle(v: f64) -> Price {
        let Ok(p) = Price::new(v) else {
            panic!("valid price");
        };
        p
    }

    fn dummy_position() -> Position {
        let Ok(t0) = Tick::new(0) else {
            panic!("valid tick");
        };
        let Ok(t1) = Tick::new(100) else {
            panic!("valid tick");
        };
        let Ok(p) = Position::new(t0, t1, Liquidity::new(1)) else {
            panic!("valid position");
        };
        p
    }

    /// Creates a pool with given k, oracle, reserves, and fee tier.
    fn make_pool(k: f64, oracle_price: f64, base: u128, quote: u128, fee: FeeTier) -> DynamicPool {
        let Ok(cfg) = DynamicConfig::new(
            make_pair(),
            fee,
            oracle(oracle_price),
            k,
            Amount::new(base),
            Amount::new(quote),
        ) else {
            panic!("valid config");
        };
        let Ok(pool) = DynamicPool::from_config(&cfg) else {
            panic!("valid pool");
        };
        pool
    }

    // -- FromConfig -----------------------------------------------------------

    #[test]
    fn from_config_sets_state() {
        let pool = make_pool(0.5, 1.5, 1_000_000, 1_500_000, fee_30bp());
        assert_eq!(pool.base_reserve(), Amount::new(1_000_000));
        assert_eq!(pool.quote_reserve(), Amount::new(1_500_000));
        assert_eq!(pool.target_base(), Amount::new(1_000_000));
        assert_eq!(pool.target_quote(), Amount::new(1_500_000));
        assert!((pool.slippage_coefficient() - 0.5).abs() < f64::EPSILON);
        assert!(!pool.total_liquidity().is_zero());
    }

    // -- Scenario 1: Oracle-Only (k = 0) --------------------------------------

    #[test]
    fn test_dynamic_oracle_only_k_zero() {
        // k=0 means pure oracle pricing. Selling 1000 A at oracle=1.5
        // should yield ≈ 1500 B (zero slippage, no fee).
        let mut pool = make_pool(0.0, 1.5, 1_000_000, 2_000_000, zero_fee());

        let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };

        // With zero fee and k=0: output = net × oracle = 1000 × 1.5 = 1500
        assert_eq!(result.amount_out().get(), 1_500);
        assert_eq!(result.fee(), Amount::ZERO);
    }

    // -- Scenario 2: Constant Product (k = 1) ---------------------------------

    #[test]
    fn test_dynamic_constant_product_k_one() {
        // k=1 means pure AMM. Output should match constant product formula.
        let mut pool = make_pool(1.0, 1.5, 1_000_000, 1_500_000, zero_fee());

        let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };

        // CP formula: out = Q × net / (B + net) = 1_500_000 × 1000 / 1_001_000
        // = 1_498 (truncated)
        let expected_cp = 1_500_000u128 * 1_000 / 1_001_000;
        assert_eq!(result.amount_out().get(), expected_cp);
    }

    // -- Scenario 3: Blended (k = 0.5) ----------------------------------------

    #[test]
    fn test_dynamic_blended_k_half() {
        // k=0.5, oracle=1.5, reserves give AMM price=2.0 (Q/B = 2M/1M)
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 2_000_000, zero_fee());

        let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };

        // oracle_out = 1000 × 1.5 = 1500
        // amm_out = 2M × 1000 / (1M + 1000) ≈ 1998
        // blended = 0.5 × 1500 + 0.5 × 1998 = 750 + 999 = 1749
        let oracle_out = 1_500.0_f64;
        let amm_out = 2_000_000.0 * 1_000.0 / 1_001_000.0;
        let expected = (0.5 * oracle_out + 0.5 * amm_out) as u128;
        assert_eq!(result.amount_out().get(), expected);

        // Output should be between oracle and AMM outputs
        assert!(result.amount_out().get() >= 1_500);
        assert!(result.amount_out().get() <= 1_998);
    }

    // -- Scenario 4: Oracle Price Update Effect --------------------------------

    #[test]
    fn test_dynamic_oracle_price_update() {
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 2_000_000, zero_fee());

        let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
            panic!("valid spec");
        };
        let Ok(r1) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };

        // Reset pool and update oracle to 2.0
        let mut pool2 = make_pool(0.5, 1.5, 1_000_000, 2_000_000, zero_fee());
        let Ok(new_price) = Price::new(2.0) else {
            panic!("valid price");
        };
        let Ok(()) = pool2.set_oracle_price(new_price) else {
            panic!("expected Ok");
        };

        let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
            panic!("valid spec");
        };
        let Ok(r2) = pool2.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };

        // Higher oracle → higher oracle component → more output
        assert!(
            r2.amount_out().get() > r1.amount_out().get(),
            "r2={} should > r1={}",
            r2.amount_out().get(),
            r1.amount_out().get()
        );
    }

    // -- Scenario 5: Asymmetric Reserves (Away from Oracle) --------------------

    #[test]
    fn test_dynamic_asymmetric_reserves_away_from_oracle() {
        // Oracle = 1.5, but reserves imply AMM price = 3.0 (Q/B = 3M/1M)
        // k=0.3 → output pulled towards oracle
        let mut pool = make_pool(0.3, 1.5, 1_000_000, 3_000_000, zero_fee());

        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };

        // oracle_out = 10_000 × 1.5 = 15_000
        // amm_out ≈ 3M × 10k / (1M + 10k) ≈ 29_703
        // blended ≈ 0.7 × 15_000 + 0.3 × 29_703 = 10_500 + 8_911 ≈ 19_411
        let out = result.amount_out().get();
        // Output should be between oracle and AMM
        assert!(out >= 15_000, "out={out} >= 15000");
        assert!(out <= 30_000, "out={out} <= 30000");
    }

    // -- Scenario 6: Large Swap with Oracle Fallback ---------------------------

    #[test]
    fn test_dynamic_large_swap_oracle_fallback() {
        // k=0.2 (oracle-heavy), large swap
        let mut pool = make_pool(0.2, 1.5, 1_000_000, 2_000_000, zero_fee());

        let Ok(spec) = SwapSpec::exact_in(Amount::new(500_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };

        // AMM component has heavy slippage (50% of reserve), but
        // oracle component (80% weight) limits damage.
        let out = result.amount_out().get();
        // oracle_out = 500k × 1.5 = 750k
        // amm_out = 2M × 500k / 1.5M ≈ 666k
        // blended ≈ 0.8 × 750k + 0.2 × 666k ≈ 733k
        assert!(out > 600_000, "out={out} should > 600k");
        assert!(out < 800_000, "out={out} should < 800k");
    }

    // -- Swap with fees -------------------------------------------------------

    #[test]
    fn swap_with_fee_deducts_correctly() {
        let mut pool = make_pool(0.0, 1.5, 1_000_000, 2_000_000, fee_30bp());

        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };

        // fee = 10_000 × 30 / 10_000 = 3 (rounded up)
        assert!(result.fee().get() > 0);
        // net = 10_000 - fee, oracle_out = net × 1.5
        // output < 15_000 because fee is deducted
        assert!(result.amount_out().get() < 15_000);
    }

    // -- Buying base (B → A) --------------------------------------------------

    #[test]
    fn buy_base_k_zero() {
        // k=0: output = net / oracle_price
        let mut pool = make_pool(0.0, 2.0, 1_000_000, 2_000_000, zero_fee());

        let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_b()) else {
            panic!("expected Ok");
        };

        // oracle_out = 1000 / 2.0 = 500
        assert_eq!(result.amount_out().get(), 500);
    }

    #[test]
    fn buy_base_k_one() {
        // k=1: pure AMM output
        let mut pool = make_pool(1.0, 2.0, 1_000_000, 2_000_000, zero_fee());

        let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_b()) else {
            panic!("expected Ok");
        };

        // amm_out = B × net / (Q + net) = 1M × 1000 / (2M + 1000)
        let expected = 1_000_000u128 * 1_000 / 2_001_000;
        assert_eq!(result.amount_out().get(), expected);
    }

    // -- Spot price -----------------------------------------------------------

    #[test]
    fn spot_price_k_zero_equals_oracle() {
        let pool = make_pool(0.0, 1.5, 1_000_000, 2_000_000, zero_fee());
        let Ok(price) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };
        assert!((price.get() - 1.5).abs() < 0.01, "price={}", price.get());
    }

    #[test]
    fn spot_price_k_one_equals_amm() {
        let pool = make_pool(1.0, 1.5, 1_000_000, 2_000_000, zero_fee());
        let Ok(price) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };
        // AMM price = Q/B = 2.0
        assert!((price.get() - 2.0).abs() < 0.01, "price={}", price.get());
    }

    #[test]
    fn spot_price_blended() {
        let pool = make_pool(0.5, 1.5, 1_000_000, 2_000_000, zero_fee());
        let Ok(price) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };
        // blended = 0.5 × 1.5 + 0.5 × 2.0 = 1.75
        assert!((price.get() - 1.75).abs() < 0.01, "price={}", price.get());
    }

    #[test]
    fn spot_price_same_token() {
        let pool = make_pool(0.5, 1.5, 1_000_000, 2_000_000, zero_fee());
        let Ok(price) = pool.spot_price(&tok_a(), &tok_a()) else {
            panic!("expected Ok");
        };
        assert!((price.get() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn spot_price_inverse() {
        let pool = make_pool(0.5, 1.5, 1_000_000, 2_000_000, zero_fee());
        let Ok(p_ab) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };
        let Ok(p_ba) = pool.spot_price(&tok_b(), &tok_a()) else {
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
        let pool = make_pool(0.5, 1.5, 1_000_000, 2_000_000, zero_fee());
        let result = pool.spot_price(&unknown_token(), &tok_b());
        assert!(matches!(result, Err(AmmError::InvalidToken(_))));
    }

    // -- Price direction after swap -------------------------------------------

    #[test]
    fn price_moves_after_sell_base() {
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 2_000_000, zero_fee());
        let Ok(p_before) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };

        let Ok(spec) = SwapSpec::exact_in(Amount::new(100_000)) else {
            panic!("valid spec");
        };
        let Ok(_) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };

        let Ok(p_after) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };
        // Selling A → more A, less B → AMM price of A drops (Q/B decreases)
        // But blended price may still move depending on k.
        // With k>0 the AMM component changes.
        // The AMM price Q/B decreases, so blended price should decrease.
        assert!(
            p_after.get() < p_before.get(),
            "p_after={} should < p_before={}",
            p_after.get(),
            p_before.get()
        );
    }

    // -- Invalid token swap ---------------------------------------------------

    #[test]
    fn swap_invalid_token_rejected() {
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 2_000_000, zero_fee());
        let Ok(spec) = SwapSpec::exact_in(Amount::new(100)) else {
            panic!("valid spec");
        };
        let result = pool.swap(spec, unknown_token());
        assert!(matches!(result, Err(AmmError::InvalidToken(_))));
    }

    // -- ExactOut swap --------------------------------------------------------

    #[test]
    fn swap_exact_out_sell_base() {
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 2_000_000, fee_30bp());
        let Ok(spec) = SwapSpec::exact_out(Amount::new(500)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };
        assert!(result.amount_out().get() >= 500);
        assert!(result.amount_in().get() > 0);
        assert!(result.fee().get() > 0);
    }

    #[test]
    fn swap_exact_out_buy_base() {
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 2_000_000, fee_30bp());
        let Ok(spec) = SwapSpec::exact_out(Amount::new(500)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_b()) else {
            panic!("expected Ok");
        };
        assert!(result.amount_out().get() >= 500);
        assert!(result.amount_in().get() > 0);
    }

    // -- Oracle update --------------------------------------------------------

    #[test]
    fn set_oracle_price_updates_spot() {
        let mut pool = make_pool(0.0, 1.5, 1_000_000, 2_000_000, zero_fee());
        let Ok(p1) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };
        assert!((p1.get() - 1.5).abs() < 0.01);

        let Ok(new_price) = Price::new(3.0) else {
            panic!("valid price");
        };
        let Ok(()) = pool.set_oracle_price(new_price) else {
            panic!("expected Ok");
        };
        assert_eq!(pool.oracle_price(), new_price);

        let Ok(p2) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };
        assert!((p2.get() - 3.0).abs() < 0.01);
    }

    // -- Liquidity add --------------------------------------------------------

    #[test]
    fn add_liquidity_proportional() {
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 1_500_000, zero_fee());
        let initial_liq = pool.total_liquidity();

        let Ok(change) = LiquidityChange::add(Amount::new(100_000), Amount::new(150_000)) else {
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
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 1_500_000, zero_fee());
        let Ok(change) = LiquidityChange::remove(Liquidity::new(1)) else {
            panic!("valid change");
        };
        let result = pool.add_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InvalidLiquidity(_))));
    }

    // -- Liquidity remove -----------------------------------------------------

    #[test]
    fn remove_liquidity_half() {
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 1_500_000, zero_fee());
        let half = pool.total_liquidity().get() / 2;

        let Ok(change) = LiquidityChange::remove(Liquidity::new(half)) else {
            panic!("valid change");
        };
        let Ok(out_a) = pool.remove_liquidity(&change) else {
            panic!("expected Ok");
        };
        assert!(out_a.get() > 0);
        assert!(pool.base_reserve().get() < 1_000_000);
        assert!(pool.quote_reserve().get() < 1_500_000);
    }

    #[test]
    fn remove_liquidity_exceeding_total_fails() {
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 1_500_000, zero_fee());
        let too_much = pool.total_liquidity().get() + 1;

        let Ok(change) = LiquidityChange::remove(Liquidity::new(too_much)) else {
            panic!("valid change");
        };
        let result = pool.remove_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InsufficientLiquidity)));
    }

    #[test]
    fn remove_liquidity_wrong_variant() {
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 1_500_000, zero_fee());
        let Ok(change) = LiquidityChange::add(Amount::new(100), Amount::new(100)) else {
            panic!("valid change");
        };
        let result = pool.remove_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InvalidLiquidity(_))));
    }

    // -- Fee accumulation -----------------------------------------------------

    #[test]
    fn fees_accumulate_over_swaps() {
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 2_000_000, fee_30bp());

        for _ in 0..5 {
            let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
                panic!("valid spec");
            };
            let Ok(_) = pool.swap(spec, tok_a()) else {
                panic!("expected Ok");
            };
        }

        assert!(
            pool.accumulated_fees_base().get() > 0,
            "fees should accumulate on base (sell-base swaps)"
        );
    }

    #[test]
    fn collect_fees_returns_accumulated_and_resets() {
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 2_000_000, fee_30bp());

        for _ in 0..3 {
            let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
                panic!("valid spec");
            };
            let Ok(_) = pool.swap(spec, tok_a()) else {
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

    // -- k parameter sensitivity ----------------------------------------------

    #[test]
    fn k_sensitivity_output_varies_with_k() {
        // Same swap with different k values should give different outputs.
        let k_values = [0.0, 0.25, 0.5, 0.75, 1.0];
        let mut outputs = Vec::new();

        for &k in &k_values {
            let mut pool = make_pool(k, 1.5, 1_000_000, 2_000_000, zero_fee());
            let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
                panic!("valid spec");
            };
            let Ok(result) = pool.swap(spec, tok_a()) else {
                panic!("expected Ok for k={k}");
            };
            outputs.push(result.amount_out().get());
        }

        // k=0 (oracle=1.5): out=15000
        // k=1 (AMM Q/B=2.0): out ≈ 19800
        // Outputs should be monotonically increasing (oracle < AMM for this setup)
        for pair in outputs.windows(2) {
            let (&prev, &curr) = match (pair.first(), pair.get(1)) {
                (Some(a), Some(b)) => (a, b),
                _ => continue,
            };
            assert!(curr >= prev, "curr={curr} should >= prev={prev}");
        }
    }

    // -- Bid/ask spread verification ------------------------------------------

    #[test]
    fn bid_ask_spread_exists_when_k_nonzero() {
        let pool = make_pool(0.5, 1.5, 1_000_000, 2_000_000, zero_fee());

        // The "bid" and "ask" emerge from the blended pricing.
        // With k>0 and AMM price != oracle, there's an effective spread.
        let Ok(spot) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };
        // blended = 0.5 × 1.5 + 0.5 × 2.0 = 1.75
        // This differs from the oracle (1.5) showing the AMM influence
        assert!(spot.get() > 1.5 + 0.1);
        assert!(spot.get() < 2.0 - 0.1);
    }

    // -- Accessors and Debug --------------------------------------------------

    #[test]
    fn accessors() {
        let pool = make_pool(0.3, 1.5, 500, 750, fee_30bp());
        assert_eq!(pool.base_reserve(), Amount::new(500));
        assert_eq!(pool.quote_reserve(), Amount::new(750));
        assert_eq!(pool.target_base(), Amount::new(500));
        assert_eq!(pool.target_quote(), Amount::new(750));
        assert!((pool.slippage_coefficient() - 0.3).abs() < f64::EPSILON);
        assert_eq!(pool.oracle_price(), oracle(1.5));
        assert_eq!(pool.fee_tier(), fee_30bp());
        assert_eq!(pool.accumulated_fees_base(), Amount::ZERO);
        assert_eq!(pool.accumulated_fees_quote(), Amount::ZERO);
    }

    #[test]
    fn token_pair_is_correct() {
        let pool = make_pool(0.5, 1.5, 1_000, 1_500, zero_fee());
        assert_eq!(pool.token_pair().first(), tok_a());
        assert_eq!(pool.token_pair().second(), tok_b());
    }

    #[test]
    fn debug_format() {
        let pool = make_pool(0.5, 1.5, 1_000, 1_500, zero_fee());
        let dbg = format!("{pool:?}");
        assert!(dbg.contains("DynamicPool"));
    }

    // -- Reserve updates after swap -------------------------------------------

    #[test]
    fn reserves_update_after_sell_base() {
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 2_000_000, zero_fee());

        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };

        // Base increases, quote decreases
        assert_eq!(pool.base_reserve().get(), 1_000_000 + 10_000);
        assert_eq!(
            pool.quote_reserve().get(),
            2_000_000 - result.amount_out().get()
        );
    }

    #[test]
    fn reserves_update_after_buy_base() {
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 2_000_000, zero_fee());

        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_b()) else {
            panic!("expected Ok");
        };

        // Quote increases, base decreases
        assert_eq!(pool.quote_reserve().get(), 2_000_000 + 10_000);
        assert_eq!(
            pool.base_reserve().get(),
            1_000_000 - result.amount_out().get()
        );
    }

    // -- Remove zero liquidity ------------------------------------------------

    #[test]
    fn remove_zero_liquidity_rejected() {
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 1_500_000, zero_fee());
        let change = LiquidityChange::Remove {
            liquidity: Liquidity::ZERO,
        };
        let result = pool.remove_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InvalidLiquidity(_))));
    }

    // -- Add liquidity both zero ----------------------------------------------

    #[test]
    fn add_liquidity_both_zero_rejected() {
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 1_500_000, zero_fee());
        let change = LiquidityChange::Add {
            amount_a: Amount::ZERO,
            amount_b: Amount::ZERO,
        };
        let result = pool.add_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InvalidQuantity(_))));
    }

    // -- Set oracle price zero rejected ---------------------------------------

    #[test]
    fn set_oracle_price_zero_rejected() {
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 1_500_000, zero_fee());
        let Ok(zero_price) = Price::new(0.0) else {
            // Price::new(0.0) may itself reject zero — that's also valid
            return;
        };
        let result = pool.set_oracle_price(zero_price);
        assert!(matches!(result, Err(AmmError::InvalidPrice(_))));
    }

    // -- Set oracle price negative rejected -----------------------------------

    #[test]
    fn set_oracle_price_negative_rejected() {
        let mut pool = make_pool(0.5, 1.5, 1_000_000, 1_500_000, zero_fee());
        let Ok(neg_price) = Price::new(-1.0) else {
            // Price::new(-1.0) may itself reject negative — that's also valid
            return;
        };
        let result = pool.set_oracle_price(neg_price);
        assert!(matches!(result, Err(AmmError::InvalidPrice(_))));
    }
}
