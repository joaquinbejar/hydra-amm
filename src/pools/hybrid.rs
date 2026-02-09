//! Hybrid / StableSwap pool implementation (Curve style).
//!
//! Specialised for low-slippage swaps between similarly-priced
//! (pegged) assets such as stablecoins.
//!
//! # Invariant (n = 2 tokens)
//!
//! ```text
//! A · 2 · (x + y) + D = A · D · 2 + D³ / (4 · x · y)
//! ```
//!
//! where:
//! - `A` — amplification coefficient (1–10 000).
//! - `D` — invariant parameter (≈ total reserves when at peg).
//! - `x`, `y` — balances of the two tokens.
//!
//! # Swap Algorithm
//!
//! 1. Deduct fee from the input amount.
//! 2. Compute `x_new = reserve_in + net_input`.
//! 3. Use Newton-Raphson to find `y_new` satisfying the invariant.
//! 4. `amount_out = reserve_out − y_new`.
//! 5. Update reserves atomically.
//!
//! # Amplification Behaviour
//!
//! | A | Curve |
//! |---|-------|
//! | 1 | Constant product (`x · y = k`) |
//! | 50–5 000 | Hybrid — low slippage near peg |
//! | → ∞ | Constant sum (1:1 swaps) |

use crate::config::HybridConfig;
use crate::domain::{
    Amount, FeeTier, Liquidity, LiquidityChange, Position, Price, Rounding, SwapResult, SwapSpec,
    Token, TokenPair,
};
use crate::error::AmmError;
use crate::traits::{FromConfig, LiquidityPool, SwapPool};

/// Number of tokens in a StableSwap pair.
const N: u128 = 2;

/// Maximum Newton-Raphson iterations before declaring non-convergence.
const MAX_ITERATIONS: u32 = 256;

/// Convergence threshold for Newton-Raphson (absolute difference in
/// consecutive iterates, in raw token units).
const CONVERGENCE_THRESHOLD: u128 = 1;

// ---------------------------------------------------------------------------
// StableSwap math helpers
// ---------------------------------------------------------------------------

/// Computes the StableSwap invariant `D` for two reserves via
/// Newton-Raphson iteration.
///
/// The invariant equation for n = 2:
/// ```text
/// A·n·S + D = A·D·n + D^(n+1) / (n^n · P)
/// ```
/// where `S = x + y`, `P = x · y`, `n = 2`.
///
/// Rearranged for Newton-Raphson iteration:
/// ```text
/// D_next = (A·n·S + n·D_P) · D / ((A·n − 1)·D + (n+1)·D_P)
/// ```
/// where `D_P = D^3 / (n^n · P)`.
///
/// # Errors
///
/// Returns [`AmmError::NewtonRaphsonNonConvergence`] if the iteration
/// does not converge within [`MAX_ITERATIONS`] steps.
fn compute_d(x: u128, y: u128, amp: u128) -> Result<u128, AmmError> {
    let s = x
        .checked_add(y)
        .ok_or(AmmError::Overflow("D: S overflow"))?;
    if s == 0 {
        return Ok(0);
    }

    let ann = amp
        .checked_mul(N)
        .ok_or(AmmError::Overflow("D: A·n overflow"))?;

    let mut d = s;
    for _ in 0..MAX_ITERATIONS {
        // D_P = D^3 / (n^n · x · y) = D * D * D / (4 * x * y)
        // We compute step by step to avoid overflow where possible.
        // d_p = d
        // d_p = d_p * d / (n * x)
        // d_p = d_p * d / (n * y)
        let mut d_p = d;

        // d_p = d_p * d / (2 * x)
        let nx = N
            .checked_mul(x)
            .ok_or(AmmError::Overflow("D: n·x overflow"))?;
        if nx == 0 {
            return Err(AmmError::DivisionByZero);
        }
        d_p = d_p
            .checked_mul(d)
            .ok_or(AmmError::Overflow("D: d_p·d overflow"))?
            / nx;

        // d_p = d_p * d / (2 * y)
        let ny = N
            .checked_mul(y)
            .ok_or(AmmError::Overflow("D: n·y overflow"))?;
        if ny == 0 {
            return Err(AmmError::DivisionByZero);
        }
        d_p = d_p
            .checked_mul(d)
            .ok_or(AmmError::Overflow("D: d_p·d overflow"))?
            / ny;

        let d_prev = d;

        // numerator = (A·n·S + n·D_P) · D
        // = (ann * s + N * d_p) * d
        let ann_s = ann
            .checked_mul(s)
            .ok_or(AmmError::Overflow("D: ann·S overflow"))?;
        let n_dp = N
            .checked_mul(d_p)
            .ok_or(AmmError::Overflow("D: n·D_P overflow"))?;
        let num_inner = ann_s
            .checked_add(n_dp)
            .ok_or(AmmError::Overflow("D: num inner overflow"))?;
        let numerator = num_inner
            .checked_mul(d)
            .ok_or(AmmError::Overflow("D: numerator overflow"))?;

        // denominator = (A·n − 1)·D + (n+1)·D_P
        let ann_minus_1 = ann.saturating_sub(1);
        let denom_left = ann_minus_1
            .checked_mul(d)
            .ok_or(AmmError::Overflow("D: denom left overflow"))?;
        let n_plus_1 = N + 1;
        let denom_right = n_plus_1
            .checked_mul(d_p)
            .ok_or(AmmError::Overflow("D: denom right overflow"))?;
        let denominator = denom_left
            .checked_add(denom_right)
            .ok_or(AmmError::Overflow("D: denominator overflow"))?;

        if denominator == 0 {
            return Err(AmmError::DivisionByZero);
        }

        d = numerator / denominator;

        // Check convergence
        let diff = d.abs_diff(d_prev);
        if diff <= CONVERGENCE_THRESHOLD {
            return Ok(d);
        }
    }

    Err(AmmError::NewtonRaphsonNonConvergence(
        "D computation did not converge within 256 iterations",
    ))
}

/// Computes the output reserve `y` given the new input reserve `x_new`,
/// the invariant `D`, and the amplification `A`, using Newton-Raphson.
///
/// For n = 2, the equation solved for y is:
/// ```text
/// y² + (D/(A·n) + D − x_new − D²/(2·A·n·x_new)) · y = D³ / (4·A·n²·x_new)
/// ```
///
/// Simplified as: y² + b·y = c, iterate:
/// ```text
/// y_next = (y² + c) / (2·y + b)
/// ```
///
/// # Errors
///
/// Returns [`AmmError::NewtonRaphsonNonConvergence`] if iteration does
/// not converge within [`MAX_ITERATIONS`] steps.
fn compute_y(x_new: u128, d: u128, amp: u128) -> Result<u128, AmmError> {
    // ann = A * n
    let ann = amp
        .checked_mul(N)
        .ok_or(AmmError::Overflow("y: A·n overflow"))?;

    if ann == 0 {
        return Err(AmmError::DivisionByZero);
    }

    // c = D^3 / (4 * x_new * ann)    [for n=2: n^n = 4, ann = A·n]
    // We compute: c = D * D / (x_new * 2) * D / (ann * 2)
    let nn = N
        .checked_mul(N)
        .ok_or(AmmError::Overflow("y: n² overflow"))?; // 4
    let c_denom = nn
        .checked_mul(x_new)
        .ok_or(AmmError::Overflow("y: c denom overflow"))?
        .checked_mul(ann)
        .ok_or(AmmError::Overflow("y: c denom·ann overflow"))?;
    if c_denom == 0 {
        return Err(AmmError::DivisionByZero);
    }
    // c = D^3 / c_denom
    // To avoid overflow: c = (D * D / c_denom_part1) * D / c_denom_part2
    // Use a safer decomposition:
    let d_sq = d
        .checked_mul(d)
        .ok_or(AmmError::Overflow("y: D² overflow"))?;
    // c = D² * D / c_denom
    // Split c_denom = (2 * x_new) * (2 * ann)
    let two_x = 2u128
        .checked_mul(x_new)
        .ok_or(AmmError::Overflow("y: 2x overflow"))?;
    if two_x == 0 {
        return Err(AmmError::DivisionByZero);
    }
    let c_part = d_sq / two_x;
    let two_ann = 2u128
        .checked_mul(ann)
        .ok_or(AmmError::Overflow("y: 2·ann overflow"))?;
    if two_ann == 0 {
        return Err(AmmError::DivisionByZero);
    }
    let c = c_part
        .checked_mul(d)
        .ok_or(AmmError::Overflow("y: c final overflow"))?
        / two_ann;

    // b = x_new + D / ann  (note: actual b in y² + b·y = c formulation
    // includes subtracting D, but we handle the sign in the iteration)
    // Standard Curve formulation: b = S + D/ann  where S = x_new (single other token)
    // but the full b also subtracts D for the iteration formula below.
    let d_div_ann = d / ann;
    let b = x_new
        .checked_add(d_div_ann)
        .ok_or(AmmError::Overflow("y: b overflow"))?;

    // Initial guess: y = D (generous upper bound)
    let mut y = d;

    for _ in 0..MAX_ITERATIONS {
        let y_prev = y;

        // y_next = (y² + c) / (2·y + b - D)
        let y_sq = y
            .checked_mul(y)
            .ok_or(AmmError::Overflow("y: y² overflow"))?;
        let numerator = y_sq
            .checked_add(c)
            .ok_or(AmmError::Overflow("y: num overflow"))?;

        let two_y = 2u128
            .checked_mul(y)
            .ok_or(AmmError::Overflow("y: 2y overflow"))?;
        let denom_sum = two_y
            .checked_add(b)
            .ok_or(AmmError::Overflow("y: denom sum overflow"))?;
        // denominator = 2y + b - D  (b already includes D/ann + x_new,
        // and we subtract D to get the correct Curve formulation)
        let denominator = denom_sum.saturating_sub(d);

        if denominator == 0 {
            return Err(AmmError::DivisionByZero);
        }

        y = numerator / denominator;

        let diff = y.abs_diff(y_prev);
        if diff <= CONVERGENCE_THRESHOLD {
            return Ok(y);
        }
    }

    Err(AmmError::NewtonRaphsonNonConvergence(
        "y computation did not converge within 256 iterations",
    ))
}

// ---------------------------------------------------------------------------
// HybridPool
// ---------------------------------------------------------------------------

/// A Hybrid (StableSwap) AMM pool.
///
/// Created from a [`HybridConfig`] via [`FromConfig`].  Uses the Curve
/// StableSwap invariant to provide low-slippage swaps between pegged
/// assets.
///
/// # State
///
/// - `reserve_a` / `reserve_b` — current token balances.
/// - `amplification` — the `A` parameter controlling curve shape.
/// - `total_liq` — outstanding LP shares.
/// - `accumulated_fees_a` / `accumulated_fees_b` — lifetime fee
///   counters.
/// - `invariant_d` — cached StableSwap `D` value.
#[derive(Debug, Clone, PartialEq)]
pub struct HybridPool {
    token_pair: TokenPair,
    fee_tier: FeeTier,
    amplification: u128,
    reserve_a: Amount,
    reserve_b: Amount,
    total_liq: Liquidity,
    accumulated_fees_a: Amount,
    accumulated_fees_b: Amount,
    invariant_d: u128,
}

impl HybridPool {
    /// Returns the current reserve of token A.
    pub const fn reserve_a(&self) -> Amount {
        self.reserve_a
    }

    /// Returns the current reserve of token B.
    pub const fn reserve_b(&self) -> Amount {
        self.reserve_b
    }

    /// Returns the amplification coefficient.
    pub const fn amplification(&self) -> u128 {
        self.amplification
    }

    /// Returns the accumulated fees for token A.
    pub const fn accumulated_fees_a(&self) -> Amount {
        self.accumulated_fees_a
    }

    /// Returns the accumulated fees for token B.
    pub const fn accumulated_fees_b(&self) -> Amount {
        self.accumulated_fees_b
    }

    /// Returns the cached StableSwap invariant `D`.
    pub const fn invariant_d(&self) -> u128 {
        self.invariant_d
    }

    /// Integer square root via Newton's method.
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

    /// Computes the exact-in swap output using the StableSwap invariant.
    ///
    /// Returns `(amount_out, fee)`.
    fn compute_exact_in(
        &self,
        amount_in: Amount,
        reserve_in: Amount,
        reserve_out: Amount,
    ) -> Result<(Amount, Amount), AmmError> {
        // fee = amount_in * fee_bps / 10_000  (round up)
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

        let x_new = reserve_in
            .checked_add(&net_input)
            .ok_or(AmmError::Overflow("x_new overflow"))?;

        // Compute y_new via Newton-Raphson
        let y_new = compute_y(x_new.get(), self.invariant_d, self.amplification)?;

        let amount_out = reserve_out
            .get()
            .checked_sub(y_new)
            .ok_or(AmmError::Overflow("amount_out underflow"))?;

        if amount_out == 0 {
            return Err(AmmError::InsufficientLiquidity);
        }

        Ok((Amount::new(amount_out), fee))
    }

    /// Computes the exact-out swap: how much input is needed for
    /// `amount_out` using binary search over `compute_exact_in`.
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

        // Binary search for the input that produces at least amount_out
        let target = amount_out.get();
        let mut low: u128 = 1;
        let mut high: u128 = target.saturating_mul(100).max(1_000_000);
        let mut best_in: Option<(u128, u128)> = None;

        for _ in 0..128 {
            if low > high {
                break;
            }
            let mid = low + (high - low) / 2;
            match self.compute_exact_in(Amount::new(mid), reserve_in, reserve_out) {
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
}

impl FromConfig<HybridConfig> for HybridPool {
    /// Creates a new pool from the given configuration.
    ///
    /// Computes the initial invariant `D` and LP shares `√(ra × rb)`.
    ///
    /// # Errors
    ///
    /// - Propagates any error from [`HybridConfig::validate`].
    /// - Returns [`AmmError::Overflow`] if initial computations overflow.
    /// - Returns [`AmmError::NewtonRaphsonNonConvergence`] if `D`
    ///   computation does not converge.
    fn from_config(config: &HybridConfig) -> Result<Self, AmmError> {
        config.validate()?;

        let ra = config.reserve_a();
        let rb = config.reserve_b();
        let amp = u128::from(config.amplification());

        let d = compute_d(ra.get(), rb.get(), amp)?;

        // Initial LP shares = sqrt(ra * rb)
        let product = ra
            .checked_mul(&rb)
            .ok_or(AmmError::Overflow("initial product overflow"))?;
        let lp = Self::isqrt(product.get()).ok_or(AmmError::Overflow("isqrt overflow"))?;

        Ok(Self {
            token_pair: *config.token_pair(),
            fee_tier: config.fee_tier(),
            amplification: amp,
            reserve_a: ra,
            reserve_b: rb,
            total_liq: Liquidity::new(lp),
            accumulated_fees_a: Amount::ZERO,
            accumulated_fees_b: Amount::ZERO,
            invariant_d: d,
        })
    }
}

impl SwapPool for HybridPool {
    /// Executes a token swap using the StableSwap invariant.
    ///
    /// Fees are deducted from the input amount before Newton-Raphson
    /// iteration computes the new output reserve.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidToken`] if `token_in` is not in the pair.
    /// - [`AmmError::InsufficientLiquidity`] if reserves cannot satisfy.
    /// - [`AmmError::Overflow`] if arithmetic overflows.
    /// - [`AmmError::NewtonRaphsonNonConvergence`] if iteration fails.
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

        // Recompute D after the swap (reserves changed, but fees stay in pool
        // so D grows slightly — this is by design for StableSwap).
        self.invariant_d = compute_d(
            self.reserve_a.get(),
            self.reserve_b.get(),
            self.amplification,
        )?;

        SwapResult::new(amount_in, amount_out, fee)
    }

    /// Returns the spot price: `reserve_quote / reserve_base`.
    ///
    /// For a StableSwap near the peg, the price is approximately 1:1.
    /// Away from peg, it follows the StableSwap curve derivative.
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

        // Analytical derivative of the StableSwap invariant.
        //
        // For the 2-token case the implicit invariant is:
        //   F(x,y) = A·n²·(x+y) + D − A·n²·D − D³/(4xy) = 0
        //
        // By implicit differentiation:
        //   dy/dx = −(∂F/∂x) / (∂F/∂y)
        //         = −(A·n² + D³/(4·x²·y)) / (A·n² + D³/(4·x·y²))
        //
        // The spot price (units of quote per unit of base) is |dy/dx|.
        let (x, y) = if *base == self.token_pair.first() {
            (self.reserve_a, self.reserve_b)
        } else {
            (self.reserve_b, self.reserve_a)
        };

        if x.is_zero() || y.is_zero() {
            return Err(AmmError::ZeroReserve);
        }

        #[allow(clippy::cast_precision_loss)]
        let xf = x.get() as f64;
        #[allow(clippy::cast_precision_loss)]
        let yf = y.get() as f64;
        #[allow(clippy::cast_precision_loss)]
        let df = self.invariant_d as f64;
        #[allow(clippy::cast_precision_loss)]
        let ann = (self.amplification as f64) * (N as f64);

        let d_cubed = df * df * df;
        let four = 4.0;

        // numerator   = A·n + D³/(4·x²·y)
        let num = ann + d_cubed / (four * xf * xf * yf);
        // denominator = A·n + D³/(4·x·y²)
        let den = ann + d_cubed / (four * xf * yf * yf);

        if den == 0.0 {
            return Err(AmmError::DivisionByZero);
        }

        let price_val = num / den;
        Price::new(price_val)
    }

    fn token_pair(&self) -> &TokenPair {
        &self.token_pair
    }

    fn fee_tier(&self) -> FeeTier {
        self.fee_tier
    }
}

impl LiquidityPool for HybridPool {
    /// Adds liquidity to the pool proportionally.
    ///
    /// For the first deposit, LP shares = `√(amount_a × amount_b)`.
    /// Subsequent deposits mint shares proportional to the smaller
    /// ratio `min(Δa/Ra, Δb/Rb) × L`.
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
            let total = self.total_liq.get();

            let share_a = if !amount_a.is_zero() && !self.reserve_a.is_zero() {
                amount_a
                    .checked_mul(&Amount::new(total))
                    .ok_or(AmmError::Overflow("share_a numerator overflow"))?
                    .checked_div(&self.reserve_a, Rounding::Down)
                    .ok_or(AmmError::DivisionByZero)?
                    .get()
            } else {
                0
            };

            let share_b = if !amount_b.is_zero() && !self.reserve_b.is_zero() {
                amount_b
                    .checked_mul(&Amount::new(total))
                    .ok_or(AmmError::Overflow("share_b numerator overflow"))?
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

        // Recompute D with updated reserves
        self.invariant_d = compute_d(
            self.reserve_a.get(),
            self.reserve_b.get(),
            self.amplification,
        )?;

        Ok(minted)
    }

    /// Removes liquidity proportionally from the pool.
    ///
    /// Returns the token-A portion.  Reserves and LP shares are
    /// reduced proportionally.
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

        // Recompute D
        self.invariant_d = compute_d(
            self.reserve_a.get(),
            self.reserve_b.get(),
            self.amplification,
        )?;

        Ok(out_a)
    }

    /// Collects accumulated trading fees.
    ///
    /// Returns the sum of fees for both tokens and resets the
    /// accumulators.  Position tick range is ignored since this pool
    /// has uniform liquidity.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::PositionNotFound`] only if the pool has
    /// never had any liquidity.
    fn collect_fees(&mut self, _position: &Position) -> Result<Amount, AmmError> {
        if self.total_liq.is_zero()
            && self.accumulated_fees_a.is_zero()
            && self.accumulated_fees_b.is_zero()
        {
            return Err(AmmError::PositionNotFound);
        }

        let total_fees = self
            .accumulated_fees_a
            .checked_add(&self.accumulated_fees_b)
            .ok_or(AmmError::Overflow("fee sum overflow"))?;

        self.accumulated_fees_a = Amount::ZERO;
        self.accumulated_fees_b = Amount::ZERO;

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

    /// Creates a balanced pool at peg with the given amplification.
    fn make_pool(amp: u32, reserve: u128) -> HybridPool {
        let Ok(cfg) = HybridConfig::new(
            make_pair(),
            fee_30bp(),
            amp,
            Amount::new(reserve),
            Amount::new(reserve),
        ) else {
            panic!("valid config");
        };
        let Ok(pool) = HybridPool::from_config(&cfg) else {
            panic!("valid pool");
        };
        pool
    }

    /// Creates an unbalanced pool with given reserves and amplification.
    fn make_pool_unbalanced(amp: u32, ra: u128, rb: u128) -> HybridPool {
        let Ok(cfg) = HybridConfig::new(
            make_pair(),
            fee_30bp(),
            amp,
            Amount::new(ra),
            Amount::new(rb),
        ) else {
            panic!("valid config");
        };
        let Ok(pool) = HybridPool::from_config(&cfg) else {
            panic!("valid pool");
        };
        pool
    }

    // -- FromConfig -----------------------------------------------------------

    #[test]
    fn from_config_balanced() {
        let pool = make_pool(100, 1_000_000);
        assert_eq!(pool.reserve_a(), Amount::new(1_000_000));
        assert_eq!(pool.reserve_b(), Amount::new(1_000_000));
        assert_eq!(pool.amplification(), 100);
        assert!(pool.invariant_d() > 0);
        assert!(!pool.total_liquidity().is_zero());
    }

    #[test]
    fn from_config_unbalanced() {
        let pool = make_pool_unbalanced(50, 1_000_000, 1_500_000);
        assert_eq!(pool.reserve_a(), Amount::new(1_000_000));
        assert_eq!(pool.reserve_b(), Amount::new(1_500_000));
    }

    #[test]
    fn invariant_d_at_peg() {
        // At peg (equal reserves), D ≈ 2 × reserve for high amplification
        let pool = make_pool(100, 1_000_000);
        let d = pool.invariant_d();
        // D should be close to 2_000_000
        assert!((1_900_000..=2_100_000).contains(&d), "D = {d}");
    }

    // -- Scenario 1: At Peg, High Amplification (A=100) -----------------------

    #[test]
    fn at_peg_high_amplification() {
        let mut pool = make_pool(100, 1_000_000);
        let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };
        // With A=100 at peg, output ≈ 997 (1000 - 3 fee ≈ 997 net → ≈997 out)
        // StableSwap should have very low slippage near peg
        assert!(
            result.amount_out().get() > 990,
            "out = {}",
            result.amount_out().get()
        );
        assert!(
            result.amount_out().get() <= 997,
            "out = {}",
            result.amount_out().get()
        );
        assert!(result.fee().get() > 0);
    }

    // -- Scenario 2: At Peg, Low Amplification (A=1) --------------------------

    #[test]
    fn at_peg_low_amplification() {
        let mut pool = make_pool(1, 1_000_000);
        let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };
        // With A=1, behaves closer to constant product → more slippage
        // Output should be lower than the A=100 case
        assert!(
            result.amount_out().get() > 900,
            "out = {}",
            result.amount_out().get()
        );
        assert!(
            result.amount_out().get() < 998,
            "out = {}",
            result.amount_out().get()
        );
    }

    #[test]
    fn low_amp_has_more_slippage_than_high_amp() {
        let mut pool_low = make_pool(1, 1_000_000);
        let mut pool_high = make_pool(100, 1_000_000);

        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(result_low) = pool_low.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };
        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(result_high) = pool_high.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };
        // Higher amplification → less slippage → more output
        assert!(
            result_high.amount_out().get() > result_low.amount_out().get(),
            "high_amp_out={} should > low_amp_out={}",
            result_high.amount_out().get(),
            result_low.amount_out().get()
        );
    }

    // -- Scenario 3: Away From Peg (Depeg) ------------------------------------

    #[test]
    fn depeg_scenario() {
        let mut pool = make_pool_unbalanced(50, 1_000_000, 1_500_000);
        let Ok(spec) = SwapSpec::exact_in(Amount::new(100_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };
        // Away from peg, output < 150k (higher slippage)
        assert!(result.amount_out().get() < 150_000);
        assert!(result.amount_out().get() > 0);
    }

    // -- Scenario 4: Extreme Amplification (A=1000) ---------------------------

    #[test]
    fn extreme_amplification() {
        let mut pool = make_pool(1000, 1_000_000);
        let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };
        // With A=1000, nearly 1:1 → output very close to 997 (after fee)
        assert!(
            result.amount_out().get() >= 996,
            "out = {}",
            result.amount_out().get()
        );
    }

    // -- Scenario 5: Newton-Raphson Convergence Limit -------------------------

    #[test]
    fn large_swap_converges() {
        // Swap 10M with A=500 — should still converge
        let mut pool = make_pool(500, 100_000_000);
        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };
        assert!(result.amount_out().get() > 0);
    }

    // -- Scenario 6: Large Unbalanced Swap ------------------------------------

    #[test]
    fn large_unbalanced_swap() {
        let mut pool = make_pool(100, 1_000_000);
        // Swap 50% of reserve
        let Ok(spec) = SwapSpec::exact_in(Amount::new(500_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };
        // Output < 500k due to slippage
        assert!(result.amount_out().get() < 500_000);
        assert!(result.amount_out().get() > 0);
    }

    // -- spot_price -----------------------------------------------------------

    #[test]
    fn spot_price_near_one_at_peg() {
        let pool = make_pool(100, 1_000_000);
        let Ok(price) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };
        // At peg with high amplification, price ≈ 1.0
        assert!((price.get() - 1.0).abs() < 0.05, "price = {}", price.get());
    }

    #[test]
    fn spot_price_inverse() {
        let pool = make_pool(100, 1_000_000);
        let Ok(p_ab) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };
        let Ok(p_ba) = pool.spot_price(&tok_b(), &tok_a()) else {
            panic!("expected Ok");
        };
        assert!((p_ab.get() * p_ba.get() - 1.0).abs() < 0.05);
    }

    #[test]
    fn spot_price_same_token() {
        let pool = make_pool(100, 1_000_000);
        let Ok(price) = pool.spot_price(&tok_a(), &tok_a()) else {
            panic!("expected Ok");
        };
        assert!((price.get() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn spot_price_invalid_token() {
        let pool = make_pool(100, 1_000_000);
        let result = pool.spot_price(&unknown_token(), &tok_b());
        assert!(matches!(result, Err(AmmError::InvalidToken(_))));
    }

    // -- Invalid token swap ---------------------------------------------------

    #[test]
    fn swap_invalid_token_rejected() {
        let mut pool = make_pool(100, 1_000_000);
        let Ok(spec) = SwapSpec::exact_in(Amount::new(100)) else {
            panic!("valid spec");
        };
        let result = pool.swap(spec, unknown_token());
        assert!(matches!(result, Err(AmmError::InvalidToken(_))));
    }

    // -- Price direction ------------------------------------------------------

    #[test]
    fn price_moves_down_when_selling_a() {
        let mut pool = make_pool(100, 1_000_000);
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
        assert!(p_after.get() < p_before.get());
    }

    #[test]
    fn price_moves_up_when_selling_b() {
        let mut pool = make_pool(100, 1_000_000);
        let Ok(p_before) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };

        let Ok(spec) = SwapSpec::exact_in(Amount::new(100_000)) else {
            panic!("valid spec");
        };
        let Ok(_) = pool.swap(spec, tok_b()) else {
            panic!("expected Ok");
        };

        let Ok(p_after) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };
        assert!(p_after.get() > p_before.get());
    }

    // -- ExactOut swap --------------------------------------------------------

    #[test]
    fn swap_exact_out() {
        let mut pool = make_pool(100, 1_000_000);
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

    // -- Liquidity add --------------------------------------------------------

    #[test]
    fn add_liquidity_proportional() {
        let mut pool = make_pool(100, 1_000_000);
        let initial_liq = pool.total_liquidity();

        let Ok(change) = LiquidityChange::add(Amount::new(100_000), Amount::new(100_000)) else {
            panic!("valid change");
        };
        let Ok(minted) = pool.add_liquidity(&change) else {
            panic!("expected Ok");
        };
        assert!(minted.get() > 0);
        assert!(pool.total_liquidity().get() > initial_liq.get());
        // D should increase after adding liquidity
        assert!(pool.invariant_d() > 0);
    }

    #[test]
    fn add_liquidity_wrong_variant() {
        let mut pool = make_pool(100, 1_000_000);
        let Ok(change) = LiquidityChange::remove(Liquidity::new(1)) else {
            panic!("valid change");
        };
        let result = pool.add_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InvalidLiquidity(_))));
    }

    // -- Liquidity remove -----------------------------------------------------

    #[test]
    fn remove_liquidity_half() {
        let mut pool = make_pool(100, 1_000_000);
        let half = pool.total_liquidity().get() / 2;

        let Ok(change) = LiquidityChange::remove(Liquidity::new(half)) else {
            panic!("valid change");
        };
        let Ok(out_a) = pool.remove_liquidity(&change) else {
            panic!("expected Ok");
        };
        assert!(out_a.get() > 0);
        // Reserves should be reduced
        assert!(pool.reserve_a().get() < 1_000_000);
        assert!(pool.reserve_b().get() < 1_000_000);
    }

    #[test]
    fn remove_liquidity_exceeding_total_fails() {
        let mut pool = make_pool(100, 1_000_000);
        let too_much = pool.total_liquidity().get() + 1;

        let Ok(change) = LiquidityChange::remove(Liquidity::new(too_much)) else {
            panic!("valid change");
        };
        let result = pool.remove_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InsufficientLiquidity)));
    }

    #[test]
    fn remove_liquidity_wrong_variant() {
        let mut pool = make_pool(100, 1_000_000);
        let Ok(change) = LiquidityChange::add(Amount::new(100), Amount::new(100)) else {
            panic!("valid change");
        };
        let result = pool.remove_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InvalidLiquidity(_))));
    }

    // -- Fee accumulation -----------------------------------------------------

    #[test]
    fn fees_accumulate_over_swaps() {
        let mut pool = make_pool(100, 1_000_000);
        assert_eq!(pool.accumulated_fees_a(), Amount::ZERO);

        for _ in 0..5 {
            let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
                panic!("valid spec");
            };
            let Ok(_) = pool.swap(spec, tok_a()) else {
                panic!("expected Ok");
            };
        }
        assert!(pool.accumulated_fees_a().get() > 0);
    }

    #[test]
    fn collect_fees_returns_accumulated() {
        let mut pool = make_pool(100, 1_000_000);

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

    // -- Monotonic amplification effect ---------------------------------------

    #[test]
    fn higher_amp_means_less_slippage() {
        let amps = [1u32, 10, 50, 100, 500, 1000];
        let mut prev_out = 0u128;

        for amp in amps {
            let mut pool = make_pool(amp, 1_000_000);
            let Ok(spec) = SwapSpec::exact_in(Amount::new(50_000)) else {
                panic!("valid spec");
            };
            let Ok(result) = pool.swap(spec, tok_a()) else {
                panic!("expected Ok for amp={amp}");
            };
            let out = result.amount_out().get();
            assert!(
                out >= prev_out,
                "amp={amp}: out={out} should be >= prev_out={prev_out}"
            );
            prev_out = out;
        }
    }

    // -- Accessors ------------------------------------------------------------

    #[test]
    fn accessors() {
        let pool = make_pool(100, 1_000_000);
        assert_eq!(*pool.token_pair(), make_pair());
        assert_eq!(pool.fee_tier(), fee_30bp());
        assert_eq!(pool.amplification(), 100);
    }

    // -- Debug ----------------------------------------------------------------

    #[test]
    fn debug_format() {
        let pool = make_pool(100, 1_000);
        let dbg = format!("{pool:?}");
        assert!(dbg.contains("HybridPool"));
    }

    // -- compute_d direct tests -----------------------------------------------

    #[test]
    fn compute_d_zero_reserves() {
        let Ok(d) = compute_d(0, 0, 100) else {
            panic!("expected Ok");
        };
        assert_eq!(d, 0);
    }

    #[test]
    fn compute_d_balanced() {
        let Ok(d) = compute_d(1_000_000, 1_000_000, 100) else {
            panic!("expected Ok");
        };
        // For balanced reserves with A=100, D ≈ 2_000_000
        assert!((1_990_000..=2_010_000).contains(&d), "D = {d}");
    }

    // -- compute_y direct tests -----------------------------------------------

    #[test]
    fn compute_y_round_trip() {
        // If x = y = 1M and D matches, then compute_y(x, D, A) ≈ y
        let Ok(d) = compute_d(1_000_000, 1_000_000, 100) else {
            panic!("expected Ok");
        };
        let Ok(y) = compute_y(1_000_000, d, 100) else {
            panic!("expected Ok");
        };
        // Should be close to 1_000_000
        let diff = y.abs_diff(1_000_000);
        assert!(diff <= 2, "y = {y}, diff = {diff}");
    }

    // -- D invariant preserved after swap (approximately) ---------------------

    #[test]
    fn d_grows_after_swap_due_to_fees() {
        let mut pool = make_pool(100, 1_000_000);
        let d_before = pool.invariant_d();

        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(_) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };

        // D should grow slightly because fees stay in pool
        assert!(pool.invariant_d() >= d_before);
    }

    // -- Symmetric swap -------------------------------------------------------

    #[test]
    fn symmetric_swap_at_peg() {
        // At peg, swapping A→B and B→A with same amount should give
        // approximately the same output
        let mut pool_ab = make_pool(100, 1_000_000);
        let mut pool_ba = make_pool(100, 1_000_000);

        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(r_ab) = pool_ab.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };
        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(r_ba) = pool_ba.swap(spec, tok_b()) else {
            panic!("expected Ok");
        };
        // Output should be identical at peg
        assert_eq!(r_ab.amount_out(), r_ba.amount_out());
    }
}
