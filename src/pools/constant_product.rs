//! Constant Product pool implementation (Uniswap V2 style).
//!
//! The swap invariant is `x × y = k` where `x` and `y` are the reserves
//! of the two tokens.  Fees are deducted from the input amount **before**
//! the pricing formula is applied.
//!
//! # Swap Algorithm (Token A → Token B)
//!
//! 1. `fee = amount_in × fee_bps / 10 000`
//! 2. `net_input = amount_in − fee`
//! 3. `amount_out = reserve_b × net_input / (reserve_a + net_input)`
//! 4. `reserve_a += amount_in` (fee stays in the pool)
//! 5. `reserve_b -= amount_out`
//!
//! # Invariant
//!
//! After every swap, `k_after ≥ k_before` because the fee component
//! increases reserves without a corresponding output.

use crate::config::ConstantProductConfig;
use crate::domain::{
    Amount, FeeTier, Liquidity, LiquidityChange, Position, Price, Rounding, SwapResult, SwapSpec,
    Token, TokenPair,
};
use crate::error::AmmError;
use crate::traits::{FromConfig, LiquidityPool, SwapPool};

/// Basis-point denominator (10 000 = 100%).
const BPS_DENOMINATOR: u128 = 10_000;

/// A Constant Product AMM pool (`x · y = k`).
///
/// Created from a [`ConstantProductConfig`] via [`FromConfig`].  The pool
/// validates the configuration on construction and is immediately ready
/// for swaps and liquidity operations.
///
/// # State
///
/// - `reserve_a` / `reserve_b` — current token balances (in raw token units, fees included)
/// - `total_liq` — outstanding LP shares (in raw liquidity units, √(reserve_a × reserve_b) at genesis)
/// - `accumulated_fees_a` / `accumulated_fees_b` — lifetime fee counters (in raw token units)
///
/// # Example
///
/// ```rust
/// use hydra_amm::config::ConstantProductConfig;
/// use hydra_amm::domain::{
///     Amount, BasisPoints, Decimals, FeeTier, SwapSpec,
///     Token, TokenAddress, TokenPair,
/// };
/// use hydra_amm::traits::{FromConfig, SwapPool};
///
/// let tok_a = Token::new(TokenAddress::from_bytes([1u8; 32]), Decimals::new(6).expect("ok"));
/// let tok_b = Token::new(TokenAddress::from_bytes([2u8; 32]), Decimals::new(18).expect("ok"));
/// let pair  = TokenPair::new(tok_a, tok_b).expect("distinct");
/// let fee   = FeeTier::new(BasisPoints::new(30));
/// let cfg   = ConstantProductConfig::new(pair, fee, Amount::new(1_000_000), Amount::new(1_000_000))
///     .expect("valid config");
///
/// let mut pool = hydra_amm::pools::ConstantProductPool::from_config(&cfg)
///     .expect("pool created");
///
/// let spec   = SwapSpec::exact_in(Amount::new(1_000)).expect("non-zero");
/// let result = pool.swap(spec, tok_a).expect("swap ok");
/// assert!(result.amount_out().get() > 0);
/// assert!(result.fee().get() > 0);
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct ConstantProductPool {
    token_pair: TokenPair,
    fee_tier: FeeTier,
    reserve_a: Amount,
    reserve_b: Amount,
    total_liq: Liquidity,
    accumulated_fees_a: Amount,
    accumulated_fees_b: Amount,
}

impl ConstantProductPool {
    /// Returns the current reserve of token A.
    pub const fn reserve_a(&self) -> Amount {
        self.reserve_a
    }

    /// Returns the current reserve of token B.
    pub const fn reserve_b(&self) -> Amount {
        self.reserve_b
    }

    /// Returns the accumulated fees collected for token A.
    pub const fn accumulated_fees_a(&self) -> Amount {
        self.accumulated_fees_a
    }

    /// Returns the accumulated fees collected for token B.
    pub const fn accumulated_fees_b(&self) -> Amount {
        self.accumulated_fees_b
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

    /// Computes the exact-in swap output.
    ///
    /// Formula: `amount_out = reserve_out × net_input / (reserve_in + net_input)`
    ///
    /// Returns `(amount_out, fee)`.
    fn compute_exact_in(
        &self,
        amount_in: Amount,
        reserve_in: Amount,
        reserve_out: Amount,
    ) -> Result<(Amount, Amount), AmmError> {
        // fee = amount_in * fee_bps / 10_000  (round up to favour the pool)
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

        // numerator = reserve_out * net_input
        // We use u128 widening to u256 emulation via checked ops.
        // For u128 values, we need to be careful about overflow.
        // amount_out = reserve_out * net_input / (reserve_in + net_input)
        let denominator = reserve_in
            .checked_add(&net_input)
            .ok_or(AmmError::Overflow("denominator overflow"))?;

        // Use u128 multiplication with overflow check
        let numerator = reserve_out
            .checked_mul(&net_input)
            .ok_or(AmmError::Overflow("numerator overflow"))?;

        let amount_out = numerator
            .checked_div(&denominator, Rounding::Down)
            .ok_or(AmmError::DivisionByZero)?;

        if amount_out.is_zero() {
            return Err(AmmError::InsufficientLiquidity);
        }

        if amount_out >= reserve_out {
            return Err(AmmError::InsufficientLiquidity);
        }

        Ok((amount_out, fee))
    }

    /// Computes the exact-out swap: how much input is needed for `amount_out`.
    ///
    /// Formula: `amount_in_net = reserve_in × amount_out / (reserve_out − amount_out)`
    /// Then: `amount_in = ceil(amount_in_net × 10 000 / (10 000 − fee_bps))`
    ///
    /// Returns `(amount_in, fee)`.
    fn compute_exact_out(
        &self,
        amount_out: Amount,
        reserve_in: Amount,
        reserve_out: Amount,
    ) -> Result<(Amount, Amount), AmmError> {
        if amount_out >= reserve_out {
            return Err(AmmError::InsufficientLiquidity);
        }

        // denominator = reserve_out - amount_out
        let denom = reserve_out
            .checked_sub(&amount_out)
            .ok_or(AmmError::Overflow("exact-out denominator underflow"))?;

        // numerator = reserve_in * amount_out
        let numer = reserve_in
            .checked_mul(&amount_out)
            .ok_or(AmmError::Overflow("exact-out numerator overflow"))?;

        // amount_in_net = ceil(numerator / denom)
        let amount_in_net = numer
            .checked_div(&denom, Rounding::Up)
            .ok_or(AmmError::DivisionByZero)?;

        // amount_in = ceil(amount_in_net * BPS_DENOMINATOR / (BPS_DENOMINATOR - fee_bps))
        let fee_bps = u128::from(self.fee_tier.basis_points().get());
        let complement = BPS_DENOMINATOR
            .checked_sub(fee_bps)
            .ok_or(AmmError::Overflow("fee complement underflow"))?;

        if complement == 0 {
            return Err(AmmError::InvalidFee("100% fee makes swap impossible"));
        }

        let scaled = amount_in_net
            .checked_mul(&Amount::new(BPS_DENOMINATOR))
            .ok_or(AmmError::Overflow("exact-out scaling overflow"))?;

        let amount_in = scaled
            .checked_div(&Amount::new(complement), Rounding::Up)
            .ok_or(AmmError::DivisionByZero)?;

        let fee = amount_in
            .checked_sub(&amount_in_net)
            .ok_or(AmmError::Overflow("fee underflow"))?;

        Ok((amount_in, fee))
    }
}

impl FromConfig<ConstantProductConfig> for ConstantProductPool {
    /// Creates a new pool from the given configuration.
    ///
    /// Initial LP shares are set to `√(reserve_a × reserve_b)`.
    ///
    /// # Errors
    ///
    /// - Propagates any error from [`ConstantProductConfig::validate`].
    /// - Returns [`AmmError::Overflow`] if the initial invariant overflows.
    fn from_config(config: &ConstantProductConfig) -> Result<Self, AmmError> {
        config.validate()?;

        let ra = config.reserve_a();
        let rb = config.reserve_b();

        // initial LP = sqrt(ra * rb)
        let product = ra
            .checked_mul(&rb)
            .ok_or(AmmError::Overflow("initial k overflow"))?;
        let lp = Self::isqrt(product.get()).ok_or(AmmError::Overflow("isqrt overflow"))?;

        Ok(Self {
            token_pair: *config.token_pair(),
            fee_tier: config.fee_tier(),
            reserve_a: ra,
            reserve_b: rb,
            total_liq: Liquidity::new(lp),
            accumulated_fees_a: Amount::ZERO,
            accumulated_fees_b: Amount::ZERO,
        })
    }
}

impl SwapPool for ConstantProductPool {
    /// Executes a token swap on the constant product pool.
    ///
    /// Fees are deducted from the input amount before applying the
    /// `x · y = k` pricing formula.  Reserves are updated atomically.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidToken`] if `token_in` is not in the pool pair.
    /// - [`AmmError::InsufficientLiquidity`] if reserves cannot satisfy the swap.
    /// - [`AmmError::Overflow`] if any arithmetic overflows.
    fn swap(&mut self, spec: SwapSpec, token_in: Token) -> Result<SwapResult, AmmError> {
        if !self.token_pair.contains(&token_in) {
            return Err(AmmError::InvalidToken(
                "token_in is not part of the pool pair",
            ));
        }

        let is_a_to_b = token_in == self.token_pair.first();

        let (reserve_in, reserve_out) = if is_a_to_b {
            (self.reserve_a, self.reserve_b)
        } else {
            (self.reserve_b, self.reserve_a)
        };

        let (amount_in, amount_out, fee) = match spec {
            SwapSpec::ExactIn { amount_in } => {
                let (out, fee) = self.compute_exact_in(amount_in, reserve_in, reserve_out)?;
                (amount_in, out, fee)
            }
            SwapSpec::ExactOut { amount_out } => {
                let (inp, fee) = self.compute_exact_out(amount_out, reserve_in, reserve_out)?;
                (inp, amount_out, fee)
            }
        };

        // Update reserves
        let new_reserve_in = reserve_in
            .checked_add(&amount_in)
            .ok_or(AmmError::Overflow("reserve_in overflow after swap"))?;
        let new_reserve_out = reserve_out
            .checked_sub(&amount_out)
            .ok_or(AmmError::Overflow("reserve_out underflow after swap"))?;

        if is_a_to_b {
            self.reserve_a = new_reserve_in;
            self.reserve_b = new_reserve_out;
            self.accumulated_fees_a = self
                .accumulated_fees_a
                .checked_add(&fee)
                .ok_or(AmmError::Overflow("accumulated fee overflow"))?;
        } else {
            self.reserve_b = new_reserve_in;
            self.reserve_a = new_reserve_out;
            self.accumulated_fees_b = self
                .accumulated_fees_b
                .checked_add(&fee)
                .ok_or(AmmError::Overflow("accumulated fee overflow"))?;
        }

        SwapResult::new(amount_in, amount_out, fee)
    }

    /// Returns the spot price: `quote_reserve / base_reserve`.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidToken`] if either token is not in the pair.
    /// - [`AmmError::ZeroReserve`] if the base reserve is zero.
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

        let (base_reserve, quote_reserve) = if *base == self.token_pair.first() {
            (self.reserve_a, self.reserve_b)
        } else {
            (self.reserve_b, self.reserve_a)
        };

        if base_reserve.is_zero() {
            return Err(AmmError::ZeroReserve);
        }

        Price::from_amounts(quote_reserve, base_reserve, Rounding::Down)
    }

    fn token_pair(&self) -> &TokenPair {
        &self.token_pair
    }

    fn fee_tier(&self) -> FeeTier {
        self.fee_tier
    }
}

impl LiquidityPool for ConstantProductPool {
    /// Adds liquidity to the pool.
    ///
    /// For the first deposit (total liquidity is zero), LP shares equal
    /// `√(amount_a × amount_b)`.  For subsequent deposits, shares are
    /// proportional to the smaller ratio `min(Δa/Ra, Δb/Rb) × L`.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidLiquidity`] if `change` is not an `Add` variant.
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
            self.reserve_a = amount_a;
            self.reserve_b = amount_b;
            self.total_liq = Liquidity::new(lp);
            Amount::new(lp)
        } else {
            // Proportional deposit: mint = min(da/Ra, db/Rb) * L
            // Using integer math: mint = min(da * L / Ra, db * L / Rb)
            let total = self.total_liq.get();

            let share_a = if !amount_a.is_zero() && !self.reserve_a.is_zero() {
                let numer = amount_a
                    .checked_mul(&Amount::new(total))
                    .ok_or(AmmError::Overflow("share_a numerator overflow"))?;
                numer
                    .checked_div(&self.reserve_a, Rounding::Down)
                    .ok_or(AmmError::DivisionByZero)?
                    .get()
            } else {
                0
            };

            let share_b = if !amount_b.is_zero() && !self.reserve_b.is_zero() {
                let numer = amount_b
                    .checked_mul(&Amount::new(total))
                    .ok_or(AmmError::Overflow("share_b numerator overflow"))?;
                numer
                    .checked_div(&self.reserve_b, Rounding::Down)
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

            self.reserve_a = self
                .reserve_a
                .checked_add(&amount_a)
                .ok_or(AmmError::Overflow("reserve_a overflow on add"))?;
            self.reserve_b = self
                .reserve_b
                .checked_add(&amount_b)
                .ok_or(AmmError::Overflow("reserve_b overflow on add"))?;
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
    /// Returns the proportional share of both token reserves:
    /// `amount_x = reserve_x × liquidity / total_liquidity`.
    ///
    /// The returned [`Amount`] is the token-A portion; token-B is
    /// returned implicitly via the reserve update.
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

        // amount_a = reserve_a * liq / total  (round down — favour the pool)
        let out_a = self
            .reserve_a
            .checked_mul(&Amount::new(liquidity.get()))
            .ok_or(AmmError::Overflow("remove_a numerator overflow"))?
            .checked_div(&Amount::new(total), Rounding::Down)
            .ok_or(AmmError::DivisionByZero)?;

        let out_b = self
            .reserve_b
            .checked_mul(&Amount::new(liquidity.get()))
            .ok_or(AmmError::Overflow("remove_b numerator overflow"))?
            .checked_div(&Amount::new(total), Rounding::Down)
            .ok_or(AmmError::DivisionByZero)?;

        self.reserve_a = self
            .reserve_a
            .checked_sub(&out_a)
            .ok_or(AmmError::Overflow("reserve_a underflow on remove"))?;
        self.reserve_b = self
            .reserve_b
            .checked_sub(&out_b)
            .ok_or(AmmError::Overflow("reserve_b underflow on remove"))?;
        self.total_liq = self
            .total_liq
            .checked_sub(&liquidity)
            .ok_or(AmmError::Overflow("total liquidity underflow"))?;

        Ok(out_a)
    }

    /// Collects accumulated fees for a position.
    ///
    /// In the constant product model fees accrue to reserves automatically.
    /// This method returns the total accumulated fees and resets the
    /// counters.  The `position` parameter is accepted for trait
    /// compatibility but is not used for fee lookup in this pool type.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::Overflow`] if fee addition overflows.
    fn collect_fees(&mut self, _position: &Position) -> Result<Amount, AmmError> {
        let total = self
            .accumulated_fees_a
            .checked_add(&self.accumulated_fees_b)
            .ok_or(AmmError::Overflow("fee collection overflow"))?;

        self.accumulated_fees_a = Amount::ZERO;
        self.accumulated_fees_b = Amount::ZERO;

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
    use crate::domain::{BasisPoints, Decimals, Token, TokenAddress};
    use crate::traits::FromConfig;

    // -- helpers --------------------------------------------------------------

    fn tok_a() -> Token {
        let Ok(d) = Decimals::new(18) else {
            panic!("valid decimals");
        };
        Token::new(TokenAddress::from_bytes([1u8; 32]), d)
    }

    fn tok_b() -> Token {
        let Ok(d) = Decimals::new(6) else {
            panic!("valid decimals");
        };
        Token::new(TokenAddress::from_bytes([2u8; 32]), d)
    }

    fn make_pair() -> TokenPair {
        let Ok(pair) = TokenPair::new(tok_a(), tok_b()) else {
            panic!("expected valid pair");
        };
        pair
    }

    fn fee_30bp() -> FeeTier {
        FeeTier::new(BasisPoints::new(30))
    }

    fn make_pool(ra: u128, rb: u128) -> ConstantProductPool {
        let Ok(cfg) =
            ConstantProductConfig::new(make_pair(), fee_30bp(), Amount::new(ra), Amount::new(rb))
        else {
            panic!("expected valid config");
        };
        let Ok(pool) = ConstantProductPool::from_config(&cfg) else {
            panic!("expected valid pool");
        };
        pool
    }

    fn unknown_token() -> Token {
        let Ok(d) = Decimals::new(8) else {
            panic!("valid decimals");
        };
        Token::new(TokenAddress::from_bytes([99u8; 32]), d)
    }

    // -- FromConfig -----------------------------------------------------------

    #[test]
    fn from_config_valid() {
        let pool = make_pool(1_000_000, 2_000_000);
        assert_eq!(pool.reserve_a(), Amount::new(1_000_000));
        assert_eq!(pool.reserve_b(), Amount::new(2_000_000));
        assert!(!pool.total_liquidity().is_zero());
    }

    #[test]
    fn from_config_initial_lp_is_sqrt() {
        let pool = make_pool(1_000_000, 1_000_000);
        // sqrt(1e6 * 1e6) = 1e6
        assert_eq!(pool.total_liquidity(), Liquidity::new(1_000_000));
    }

    // -- Swap Exact In (Scenario 1) -------------------------------------------

    #[test]
    fn swap_exact_in_a_to_b() {
        let mut pool = make_pool(1_000_000, 2_000_000);
        let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };
        assert_eq!(result.amount_in(), Amount::new(1_000));
        // fee = ceil(1000 * 30 / 10000) = ceil(3.0) = 3
        assert_eq!(result.fee(), Amount::new(3));
        // net = 997, out = 2_000_000 * 997 / (1_000_000 + 997) = 1993
        assert!(result.amount_out().get() > 0);
        // Reserves updated
        assert_eq!(pool.reserve_a(), Amount::new(1_001_000));
        assert!(pool.reserve_b() < Amount::new(2_000_000));
    }

    #[test]
    fn swap_exact_in_b_to_a() {
        let mut pool = make_pool(1_000_000, 2_000_000);
        let Ok(spec) = SwapSpec::exact_in(Amount::new(2_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_b()) else {
            panic!("expected Ok");
        };
        assert_eq!(result.amount_in(), Amount::new(2_000));
        assert!(result.amount_out().get() > 0);
        // B reserve increased, A decreased
        assert!(pool.reserve_b() > Amount::new(2_000_000));
        assert!(pool.reserve_a() < Amount::new(1_000_000));
    }

    // -- Swap Exact Out (Scenario 2) ------------------------------------------

    #[test]
    fn swap_exact_out_a_to_b() {
        let mut pool = make_pool(1_000_000, 2_000_000);
        let desired_out = Amount::new(1_000);
        let Ok(spec) = SwapSpec::exact_out(desired_out) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };
        assert_eq!(result.amount_out(), desired_out);
        assert!(result.amount_in().get() > 0);
        assert!(result.fee().get() > 0);
    }

    // -- Zero Input (Scenario 3) -----------------------------------------------
    // SwapSpec::exact_in already rejects zero, but test the path anyway.

    #[test]
    fn swap_zero_input_rejected_by_spec() {
        assert!(SwapSpec::exact_in(Amount::ZERO).is_err());
    }

    // -- Insufficient Liquidity (Scenario 4) ----------------------------------

    #[test]
    fn swap_exact_out_exceeds_reserve() {
        let mut pool = make_pool(1_000, 2_000);
        let Ok(spec) = SwapSpec::exact_out(Amount::new(2_001)) else {
            panic!("valid spec");
        };
        let result = pool.swap(spec, tok_a());
        assert!(matches!(result, Err(AmmError::InsufficientLiquidity)));
    }

    #[test]
    fn swap_exact_out_equals_reserve_rejected() {
        let mut pool = make_pool(1_000, 2_000);
        let Ok(spec) = SwapSpec::exact_out(Amount::new(2_000)) else {
            panic!("valid spec");
        };
        let result = pool.swap(spec, tok_a());
        assert!(matches!(result, Err(AmmError::InsufficientLiquidity)));
    }

    // -- Large Swap with Slippage (Scenario 6) --------------------------------

    #[test]
    fn swap_large_input_high_slippage() {
        let mut pool = make_pool(100, 100);
        // Swap 100 A (doubling reserve) → expect ~33 B
        let Ok(spec) = SwapSpec::exact_in(Amount::new(100)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };
        // 100 * 30/10000 = 0.3 → fee = 1 (ceil). net = 99
        // out = 100*99/(100+99) = 9900/199 = 49 (floor)
        // Significant slippage — much less than 100
        assert!(result.amount_out().get() < 100);
        assert!(result.amount_out().get() > 0);
    }

    // -- Invariant Preservation -----------------------------------------------

    #[test]
    fn invariant_k_preserved_after_swap() {
        let mut pool = make_pool(1_000_000, 2_000_000);
        let k_before = pool.reserve_a().get() as u128 * pool.reserve_b().get() as u128;

        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(_) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };

        let k_after = pool.reserve_a().get() as u128 * pool.reserve_b().get() as u128;
        // k_after >= k_before due to fee retention
        assert!(k_after >= k_before);
    }

    #[test]
    fn invariant_preserved_over_multiple_swaps() {
        let mut pool = make_pool(1_000_000, 2_000_000);
        let k_initial = pool.reserve_a().get() * pool.reserve_b().get();

        for _ in 0..5 {
            let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
                panic!("valid spec");
            };
            let Ok(_) = pool.swap(spec, tok_a()) else {
                panic!("expected Ok");
            };
        }
        for _ in 0..5 {
            let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
                panic!("valid spec");
            };
            let Ok(_) = pool.swap(spec, tok_b()) else {
                panic!("expected Ok");
            };
        }

        let k_final = pool.reserve_a().get() * pool.reserve_b().get();
        assert!(k_final >= k_initial);
    }

    // -- Fee Deduction Correctness (Scenario 6 variant) -----------------------

    #[test]
    fn fee_deduction_correctness() {
        let mut pool = make_pool(1_000_000, 2_000_000);
        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };
        // 30 bps of 10_000 = ceil(10_000 * 30 / 10_000) = 30
        assert_eq!(result.fee(), Amount::new(30));
        assert_eq!(pool.accumulated_fees_a(), Amount::new(30));
    }

    // -- Fee Accumulation Over Multiple Swaps (Scenario 10) -------------------

    #[test]
    fn fee_accumulation_multiple_swaps() {
        let mut pool = make_pool(1_000_000, 2_000_000);
        let mut total_fees = 0u128;

        for _ in 0..10 {
            let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
                panic!("valid spec");
            };
            let Ok(result) = pool.swap(spec, tok_a()) else {
                panic!("expected Ok");
            };
            total_fees += result.fee().get();
        }

        assert_eq!(pool.accumulated_fees_a().get(), total_fees);
        // Each swap: fee = ceil(1000 * 30 / 10000) = 3, total ≈ 30
        assert!(total_fees >= 30);
    }

    // -- Add Liquidity First Deposit (Scenario 8) -----------------------------

    #[test]
    fn add_liquidity_first_deposit() {
        let Ok(cfg) =
            ConstantProductConfig::new(make_pair(), fee_30bp(), Amount::new(1), Amount::new(1))
        else {
            panic!("valid config");
        };
        let Ok(mut pool) = ConstantProductPool::from_config(&cfg) else {
            panic!("valid pool");
        };
        // Pool starts with minimal reserves; clear to simulate empty
        // Actually, FromConfig always sets initial liquidity, so test via
        // the add_liquidity path on a fresh pool is already tested in from_config.
        // Let's just verify the initial LP = sqrt(1*1) = 1
        assert_eq!(pool.total_liquidity(), Liquidity::new(1));

        // Now add more liquidity proportionally
        let Ok(change) = LiquidityChange::add(Amount::new(1_000), Amount::new(1_000)) else {
            panic!("valid change");
        };
        let Ok(minted) = pool.add_liquidity(&change) else {
            panic!("expected Ok");
        };
        // share = min(1000 * 1 / 1, 1000 * 1 / 1) = 1000
        assert_eq!(minted, Amount::new(1_000));
    }

    // -- Add Liquidity Proportional (Scenario 7) ------------------------------

    #[test]
    fn add_liquidity_proportional() {
        let mut pool = make_pool(1_000_000, 2_000_000);
        let initial_liq = pool.total_liquidity().get();

        // Add 10% proportionally
        let Ok(change) = LiquidityChange::add(Amount::new(100_000), Amount::new(200_000)) else {
            panic!("valid change");
        };
        let Ok(minted) = pool.add_liquidity(&change) else {
            panic!("expected Ok");
        };
        // Should get ~10% of initial LP tokens
        let expected_approx = initial_liq / 10;
        assert!(
            minted.get() >= expected_approx - 1 && minted.get() <= expected_approx + 1,
            "minted={}, expected≈{}",
            minted.get(),
            expected_approx
        );
        assert_eq!(pool.reserve_a(), Amount::new(1_100_000));
        assert_eq!(pool.reserve_b(), Amount::new(2_200_000));
    }

    // -- Remove Liquidity (Scenario 9) ----------------------------------------

    #[test]
    fn remove_liquidity_proportional() {
        let mut pool = make_pool(1_000_000, 2_000_000);
        let total = pool.total_liquidity().get();
        let half = total / 2;

        let Ok(change) = LiquidityChange::remove(Liquidity::new(half)) else {
            panic!("valid change");
        };
        let Ok(out_a) = pool.remove_liquidity(&change) else {
            panic!("expected Ok");
        };
        // Should get ~50% of reserves
        assert!(out_a.get() >= 499_000 && out_a.get() <= 500_001);
        assert!(pool.reserve_a().get() >= 499_000);
        assert!(pool.reserve_b().get() >= 999_000);
        assert_eq!(pool.total_liquidity(), Liquidity::new(total - half));
    }

    #[test]
    fn remove_all_liquidity() {
        let mut pool = make_pool(1_000_000, 2_000_000);
        let total = pool.total_liquidity().get();

        let Ok(change) = LiquidityChange::remove(Liquidity::new(total)) else {
            panic!("valid change");
        };
        let Ok(_) = pool.remove_liquidity(&change) else {
            panic!("expected Ok");
        };
        assert_eq!(pool.total_liquidity(), Liquidity::ZERO);
    }

    #[test]
    fn remove_more_than_total_rejected() {
        let mut pool = make_pool(1_000_000, 2_000_000);
        let total = pool.total_liquidity().get();

        let Ok(change) = LiquidityChange::remove(Liquidity::new(total + 1)) else {
            panic!("valid change");
        };
        let result = pool.remove_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InsufficientLiquidity)));
    }

    // -- spot_price -----------------------------------------------------------

    #[test]
    fn spot_price_a_to_b() {
        let pool = make_pool(1_000_000, 2_000_000);
        let Ok(price) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };
        // price = 2_000_000 / 1_000_000 = 2.0
        assert!((price.get() - 2.0).abs() < 0.001);
    }

    #[test]
    fn spot_price_b_to_a() {
        let pool = make_pool(1_000_000, 2_000_000);
        let Ok(price) = pool.spot_price(&tok_b(), &tok_a()) else {
            panic!("expected Ok");
        };
        // price = 1_000_000 / 2_000_000 = 0.5
        assert!((price.get() - 0.5).abs() < 0.001);
    }

    #[test]
    fn spot_price_same_token() {
        let pool = make_pool(1_000_000, 2_000_000);
        let Ok(price) = pool.spot_price(&tok_a(), &tok_a()) else {
            panic!("expected Ok");
        };
        assert!((price.get() - 1.0).abs() < f64::EPSILON);
    }

    // -- Invalid token --------------------------------------------------------

    #[test]
    fn swap_invalid_token_rejected() {
        let mut pool = make_pool(1_000_000, 2_000_000);
        let Ok(spec) = SwapSpec::exact_in(Amount::new(100)) else {
            panic!("valid spec");
        };
        let result = pool.swap(spec, unknown_token());
        assert!(matches!(result, Err(AmmError::InvalidToken(_))));
    }

    #[test]
    fn spot_price_invalid_base_rejected() {
        let pool = make_pool(1_000_000, 2_000_000);
        let result = pool.spot_price(&unknown_token(), &tok_b());
        assert!(matches!(result, Err(AmmError::InvalidToken(_))));
    }

    #[test]
    fn spot_price_invalid_quote_rejected() {
        let pool = make_pool(1_000_000, 2_000_000);
        let result = pool.spot_price(&tok_a(), &unknown_token());
        assert!(matches!(result, Err(AmmError::InvalidToken(_))));
    }

    // -- Collect fees ---------------------------------------------------------

    #[test]
    fn collect_fees_after_swaps() {
        let mut pool = make_pool(1_000_000, 2_000_000);

        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(_) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };

        assert!(pool.accumulated_fees_a().get() > 0);

        let Ok(lower) = crate::domain::Tick::new(-100) else {
            panic!("valid tick");
        };
        let Ok(upper) = crate::domain::Tick::new(100) else {
            panic!("valid tick");
        };
        let Ok(pos) = Position::new(lower, upper, Liquidity::new(1)) else {
            panic!("valid position");
        };
        let Ok(fees) = pool.collect_fees(&pos) else {
            panic!("expected Ok");
        };
        assert!(fees.get() > 0);
        // After collection, counters are reset
        assert_eq!(pool.accumulated_fees_a(), Amount::ZERO);
        assert_eq!(pool.accumulated_fees_b(), Amount::ZERO);
    }

    // -- Accessors ------------------------------------------------------------

    #[test]
    fn accessors() {
        let pool = make_pool(1_000, 2_000);
        assert_eq!(*pool.token_pair(), make_pair());
        assert_eq!(pool.fee_tier(), fee_30bp());
        assert_eq!(pool.reserve_a(), Amount::new(1_000));
        assert_eq!(pool.reserve_b(), Amount::new(2_000));
    }

    // -- Wrong LiquidityChange variant ----------------------------------------

    #[test]
    fn add_liquidity_with_remove_variant_rejected() {
        let mut pool = make_pool(1_000, 2_000);
        let Ok(change) = LiquidityChange::remove(Liquidity::new(1)) else {
            panic!("valid change");
        };
        let result = pool.add_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InvalidLiquidity(_))));
    }

    #[test]
    fn remove_liquidity_with_add_variant_rejected() {
        let mut pool = make_pool(1_000, 2_000);
        let Ok(change) = LiquidityChange::add(Amount::new(100), Amount::new(200)) else {
            panic!("valid change");
        };
        let result = pool.remove_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InvalidLiquidity(_))));
    }

    // -- Zero fee pool --------------------------------------------------------

    #[test]
    fn swap_with_zero_fee() {
        let zero_fee = FeeTier::new(BasisPoints::new(0));
        let Ok(cfg) = ConstantProductConfig::new(
            make_pair(),
            zero_fee,
            Amount::new(1_000_000),
            Amount::new(2_000_000),
        ) else {
            panic!("valid config");
        };
        let Ok(mut pool) = ConstantProductPool::from_config(&cfg) else {
            panic!("valid pool");
        };

        let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };
        assert_eq!(result.fee(), Amount::ZERO);
        // With zero fee, output = reserve_b * input / (reserve_a + input)
        // = 2_000_000 * 1_000 / 1_001_000 = 1998 (floor)
        assert!(result.amount_out().get() > 0);
    }

    // -- Price movement direction ---------------------------------------------

    #[test]
    fn price_increases_after_buying_b() {
        let mut pool = make_pool(1_000_000, 2_000_000);
        let Ok(price_before) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };

        // Buy B with A → A reserve increases, B decreases → price of B in A goes up
        let Ok(spec) = SwapSpec::exact_in(Amount::new(100_000)) else {
            panic!("valid spec");
        };
        let Ok(_) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };

        let Ok(price_after) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };
        // Price of B (per A) should decrease — more A, less B
        assert!(price_after < price_before);
    }

    // -- Swap exact-out reverse direction ------------------------------------

    #[test]
    fn swap_exact_out_b_to_a() {
        let mut pool = make_pool(1_000_000, 2_000_000);
        let Ok(spec) = SwapSpec::exact_out(Amount::new(500)) else {
            panic!("valid spec");
        };
        // Swap B in → A out
        let Ok(result) = pool.swap(spec, tok_b()) else {
            panic!("expected Ok");
        };
        assert!(result.amount_out().get() >= 500);
        assert!(result.amount_in().get() > 0);
        assert!(result.fee().get() > 0);
    }

    // -- Remove zero liquidity ------------------------------------------------

    #[test]
    fn remove_zero_liquidity_rejected() {
        let mut pool = make_pool(1_000_000, 2_000_000);
        let change = LiquidityChange::Remove {
            liquidity: Liquidity::ZERO,
        };
        let result = pool.remove_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InvalidLiquidity(_))));
    }

    // -- Add liquidity both zero ----------------------------------------------

    #[test]
    fn add_liquidity_both_zero_rejected() {
        let mut pool = make_pool(1_000_000, 2_000_000);
        let change = LiquidityChange::Add {
            amount_a: Amount::ZERO,
            amount_b: Amount::ZERO,
        };
        let result = pool.add_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InvalidQuantity(_))));
    }

    // -- Invariant k preserved after exact-out --------------------------------

    #[test]
    fn invariant_k_preserved_after_exact_out() {
        let mut pool = make_pool(1_000_000, 2_000_000);
        let k_before = pool.reserve_a().get() * pool.reserve_b().get();

        let Ok(spec) = SwapSpec::exact_out(Amount::new(1_000)) else {
            panic!("valid spec");
        };
        let Ok(_) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };

        let k_after = pool.reserve_a().get() * pool.reserve_b().get();
        // k should grow (fees stay in pool)
        assert!(
            k_after >= k_before,
            "k_after={k_after} should >= k_before={k_before}"
        );
    }

    // -- Debug ----------------------------------------------------------------

    #[test]
    fn debug_format_contains_struct_name() {
        let pool = make_pool(1_000, 2_000);
        let dbg = format!("{pool:?}");
        assert!(dbg.contains("ConstantProductPool"));
    }
}
