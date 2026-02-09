//! Concentrated Liquidity Market Maker pool implementation (Uniswap V3 style).
//!
//! Liquidity is concentrated within specific tick (price) ranges.
//! Within a single tick range the pool behaves as a constant product AMM
//! parameterised by `√P` (sqrt-price) and `L` (liquidity).
//!
//! # Price Convention
//!
//! `price = 1.0001^tick` — each tick step is ~0.01%.
//! `sqrt_price = 1.0001^(tick/2)`.
//!
//! # Swap Algorithm
//!
//! 1. Deduct fee from remaining input.
//! 2. Compute how much input the current tick range can absorb before
//!    crossing the next initialised tick boundary.
//! 3. If the remaining input exceeds that capacity, consume the tick,
//!    cross the boundary, update active liquidity, and repeat.
//! 4. Accumulate output from each sub-step.
//!
//! # Fee Tracking
//!
//! Global `fee_growth_global_{a,b}` counters track fees per unit of
//! liquidity.  Per-tick `fee_growth_outside` values and per-position
//! `fee_growth_inside_last` snapshots enable efficient per-position
//! fee accounting.

use std::collections::BTreeMap;

use crate::config::ClmmConfig;
use crate::domain::{
    Amount, FeeTier, Liquidity, LiquidityChange, Position, Price, SwapResult, SwapSpec, Token,
    TokenPair,
};
use crate::error::AmmError;
use crate::traits::{FromConfig, LiquidityPool, SwapPool};

/// Basis-point denominator (10 000 = 100%).
const BPS_DENOMINATOR: f64 = 10_000.0;

/// Base of the tick-price exponential.
const BASE: f64 = 1.0001;

// ---------------------------------------------------------------------------
// Internal data structures
// ---------------------------------------------------------------------------

/// Per-tick state stored in the tick map.
///
/// Tracks the net liquidity change when the tick is crossed and
/// fee-growth values accumulated outside this tick's range.
#[derive(Debug, Clone, PartialEq, Default)]
struct TickState {
    /// Net liquidity change when crossing this tick left-to-right.
    /// Positive when entering a position's range, negative when leaving.
    liquidity_net: i128,
    /// Accumulated fee growth (token A) outside this tick, scaled by 2^64.
    fee_growth_outside_a: u128,
    /// Accumulated fee growth (token B) outside this tick, scaled by 2^64.
    fee_growth_outside_b: u128,
}

/// A liquidity position within the CLMM pool.
///
/// Tracks the tick range, liquidity amount, and fee-growth snapshots
/// for computing owed fees upon withdrawal.
#[derive(Debug, Clone, PartialEq)]
struct ClmmPosition {
    /// Lower tick boundary (inclusive).
    lower_tick: i32,
    /// Upper tick boundary (exclusive).
    upper_tick: i32,
    /// Amount of liquidity in this position.
    liquidity: u128,
    /// Snapshot of fee_growth_inside for token A when last updated.
    fee_growth_inside_last_a: u128,
    /// Snapshot of fee_growth_inside for token B when last updated.
    fee_growth_inside_last_b: u128,
}

// ---------------------------------------------------------------------------
// ClmmPool
// ---------------------------------------------------------------------------

/// A Concentrated Liquidity Market Maker (CLMM) pool.
///
/// Created from a [`ClmmConfig`] via [`FromConfig`].  Liquidity providers
/// concentrate capital within specific tick ranges for higher capital
/// efficiency.
///
/// # State
///
/// - `current_tick` — the tick index corresponding to the current price.
/// - `sqrt_price` — `√(1.0001^current_tick)`, the authoritative price.
/// - `current_liquidity` — sum of all position liquidities active at
///   `current_tick`.
/// - `fee_growth_global_a` / `fee_growth_global_b` — cumulative fees
///   per unit of liquidity (scaled by 2^64).
/// - `tick_states` — `BTreeMap<i32, TickState>` of initialised ticks.
/// - `positions` — all LP positions.
#[derive(Debug, Clone, PartialEq)]
pub struct ClmmPool {
    token_pair: TokenPair,
    fee_tier: FeeTier,
    tick_spacing: u32,
    current_tick: i32,
    sqrt_price: f64,
    current_liquidity: u128,
    fee_growth_global_a: u128,
    fee_growth_global_b: u128,
    tick_states: BTreeMap<i32, TickState>,
    positions: Vec<ClmmPosition>,
}

impl ClmmPool {
    /// Returns the current tick index.
    pub const fn current_tick_index(&self) -> i32 {
        self.current_tick
    }

    /// Returns the current sqrt-price.
    pub fn sqrt_price(&self) -> f64 {
        self.sqrt_price
    }

    /// Returns the current active liquidity.
    pub const fn current_liquidity(&self) -> u128 {
        self.current_liquidity
    }

    /// Returns the number of LP positions.
    pub fn position_count(&self) -> usize {
        self.positions.len()
    }

    /// Returns the global accumulated fee growth for token A.
    pub const fn fee_growth_global_a(&self) -> u128 {
        self.fee_growth_global_a
    }

    /// Returns the global accumulated fee growth for token B.
    pub const fn fee_growth_global_b(&self) -> u128 {
        self.fee_growth_global_b
    }

    /// Computes `sqrt(1.0001^tick)` = `1.0001^(tick/2)`.
    fn sqrt_price_at_tick(tick: i32) -> f64 {
        #[allow(clippy::cast_lossless)]
        BASE.powf(tick as f64 / 2.0)
    }

    /// Finds the next initialised tick in the given direction.
    ///
    /// `direction_up` = `true` means searching towards higher ticks (A→B
    /// swaps decrease price, so we look for lower ticks; B→A increases).
    ///
    /// Returns `None` if no further initialised tick exists.
    fn next_initialized_tick(&self, from_tick: i32, direction_up: bool) -> Option<i32> {
        if direction_up {
            // Search for the first initialised tick strictly above from_tick
            self.tick_states
                .range((
                    std::ops::Bound::Excluded(from_tick),
                    std::ops::Bound::Unbounded,
                ))
                .next()
                .map(|(&t, _)| t)
        } else {
            // Search for the first initialised tick at or below from_tick
            self.tick_states
                .range(..=from_tick)
                .next_back()
                .map(|(&t, _)| t)
        }
    }

    /// Computes fee_growth_inside for a position's tick range.
    fn fee_growth_inside(&self, lower_tick: i32, upper_tick: i32) -> (u128, u128) {
        let lower_state = self.tick_states.get(&lower_tick);
        let upper_state = self.tick_states.get(&upper_tick);

        let (fg_below_a, fg_below_b) = if self.current_tick >= lower_tick {
            (
                lower_state.map_or(0, |s| s.fee_growth_outside_a),
                lower_state.map_or(0, |s| s.fee_growth_outside_b),
            )
        } else {
            (
                self.fee_growth_global_a
                    .wrapping_sub(lower_state.map_or(0, |s| s.fee_growth_outside_a)),
                self.fee_growth_global_b
                    .wrapping_sub(lower_state.map_or(0, |s| s.fee_growth_outside_b)),
            )
        };

        let (fg_above_a, fg_above_b) = if self.current_tick < upper_tick {
            (
                upper_state.map_or(0, |s| s.fee_growth_outside_a),
                upper_state.map_or(0, |s| s.fee_growth_outside_b),
            )
        } else {
            (
                self.fee_growth_global_a
                    .wrapping_sub(upper_state.map_or(0, |s| s.fee_growth_outside_a)),
                self.fee_growth_global_b
                    .wrapping_sub(upper_state.map_or(0, |s| s.fee_growth_outside_b)),
            )
        };

        let inside_a = self
            .fee_growth_global_a
            .wrapping_sub(fg_below_a)
            .wrapping_sub(fg_above_a);
        let inside_b = self
            .fee_growth_global_b
            .wrapping_sub(fg_below_b)
            .wrapping_sub(fg_above_b);

        (inside_a, inside_b)
    }

    /// Crosses a tick boundary, updating `current_liquidity` by applying
    /// the tick's `liquidity_net` delta and flipping fee-growth-outside.
    fn cross_tick(&mut self, tick: i32, left_to_right: bool) {
        if let Some(state) = self.tick_states.get_mut(&tick) {
            // Flip fee_growth_outside when crossing
            state.fee_growth_outside_a = self
                .fee_growth_global_a
                .wrapping_sub(state.fee_growth_outside_a);
            state.fee_growth_outside_b = self
                .fee_growth_global_b
                .wrapping_sub(state.fee_growth_outside_b);

            if left_to_right {
                // Moving up: add the delta
                self.current_liquidity =
                    (self.current_liquidity as i128 + state.liquidity_net) as u128;
            } else {
                // Moving down: subtract the delta
                self.current_liquidity =
                    (self.current_liquidity as i128 - state.liquidity_net) as u128;
            }
        }
    }

    /// Executes an exact-in swap.
    ///
    /// `a_to_b`: if `true`, selling token A for token B (price decreases,
    /// sqrt_price decreases, tick decreases).
    fn execute_swap_exact_in(
        &mut self,
        amount_in: u128,
        a_to_b: bool,
    ) -> Result<(u128, u128), AmmError> {
        let fee_bps = f64::from(self.fee_tier.basis_points().get());
        let mut remaining_in = amount_in as f64;
        let mut total_out: f64 = 0.0;
        let mut total_fee: f64 = 0.0;

        // Maximum iterations to prevent infinite loops
        let mut iterations = 0u32;
        let max_iterations = 1000;

        while remaining_in > 0.5 && iterations < max_iterations {
            iterations += 1;

            if self.current_liquidity == 0 {
                // Try to find next tick with liquidity
                let next = if a_to_b {
                    self.next_initialized_tick(self.current_tick - 1, false)
                } else {
                    self.next_initialized_tick(self.current_tick, true)
                };
                match next {
                    Some(t) => {
                        self.current_tick = t;
                        self.sqrt_price = Self::sqrt_price_at_tick(self.current_tick);
                        self.cross_tick(t, !a_to_b);
                        continue;
                    }
                    None => break,
                }
            }

            let l = self.current_liquidity as f64;
            let sp = self.sqrt_price;

            // Find next tick boundary
            let next_tick = if a_to_b {
                // Price decreasing: look for the next lower initialised tick
                self.next_initialized_tick(self.current_tick - 1, false)
            } else {
                // Price increasing: look for the next higher initialised tick
                self.next_initialized_tick(self.current_tick, true)
            };

            let target_sqrt_price = match next_tick {
                Some(t) => Self::sqrt_price_at_tick(t),
                None => {
                    if a_to_b {
                        Self::sqrt_price_at_tick(-887_272)
                    } else {
                        Self::sqrt_price_at_tick(887_272)
                    }
                }
            };

            // Compute max input consumable in this range
            let (max_amount_in, amount_out_for_max, new_sp) = if a_to_b {
                // Selling A for B: sqrt_price decreases
                // amount_a = L * (1/sp_new - 1/sp_old) = L * (sp_old - sp_new) / (sp_old * sp_new)
                // amount_b = L * (sp_old - sp_new)
                if target_sqrt_price >= sp {
                    // Target is not lower — no room to move
                    break;
                }
                let delta_inv_sp = 1.0 / target_sqrt_price - 1.0 / sp;
                let max_a_in = l * delta_inv_sp;
                let max_b_out = l * (sp - target_sqrt_price);
                (max_a_in, max_b_out, target_sqrt_price)
            } else {
                // Selling B for A: sqrt_price increases
                // amount_b = L * (sp_new - sp_old)
                // amount_a = L * (1/sp_old - 1/sp_new)
                if target_sqrt_price <= sp {
                    break;
                }
                let delta_sp = target_sqrt_price - sp;
                let max_b_in = l * delta_sp;
                let max_a_out = l * (1.0 / sp - 1.0 / target_sqrt_price);
                (max_b_in, max_a_out, target_sqrt_price)
            };

            // Deduct fee from remaining
            let fee_for_step = remaining_in * fee_bps / BPS_DENOMINATOR;
            let net_remaining = remaining_in - fee_for_step;

            if net_remaining <= max_amount_in {
                // Fully consumed within this tick range
                let fraction = if max_amount_in > 0.0 {
                    net_remaining / max_amount_in
                } else {
                    0.0
                };
                let step_out = amount_out_for_max * fraction;
                // Update sqrt_price proportionally
                if a_to_b {
                    // 1/sp_new = 1/sp + net_remaining/L
                    let new_inv_sp = 1.0 / sp + net_remaining / l;
                    if new_inv_sp > 0.0 {
                        self.sqrt_price = 1.0 / new_inv_sp;
                    }
                } else {
                    self.sqrt_price = sp + net_remaining / l;
                }
                total_out += step_out;
                total_fee += fee_for_step;

                // Update fee growth
                let fee_per_liq = if l > 0.0 {
                    (fee_for_step / l * (1u128 << 64) as f64) as u128
                } else {
                    0
                };
                if a_to_b {
                    self.fee_growth_global_a = self.fee_growth_global_a.wrapping_add(fee_per_liq);
                } else {
                    self.fee_growth_global_b = self.fee_growth_global_b.wrapping_add(fee_per_liq);
                }

                remaining_in = 0.0;
            } else {
                // Consume entire tick range, then cross
                let fee_for_max = max_amount_in * fee_bps / (BPS_DENOMINATOR - fee_bps);
                let consumed = max_amount_in + fee_for_max;
                let actual_consumed = consumed.min(remaining_in);
                let actual_fee = actual_consumed * fee_bps / BPS_DENOMINATOR;
                let actual_net = actual_consumed - actual_fee;
                let fraction = if max_amount_in > 0.0 {
                    actual_net / max_amount_in
                } else {
                    0.0
                };
                let step_out = amount_out_for_max * fraction;

                total_out += step_out;
                total_fee += actual_fee;
                remaining_in -= actual_consumed;

                // Update fee growth
                let fee_per_liq = if l > 0.0 {
                    (actual_fee / l * (1u128 << 64) as f64) as u128
                } else {
                    0
                };
                if a_to_b {
                    self.fee_growth_global_a = self.fee_growth_global_a.wrapping_add(fee_per_liq);
                } else {
                    self.fee_growth_global_b = self.fee_growth_global_b.wrapping_add(fee_per_liq);
                }

                // Move to boundary and cross
                self.sqrt_price = new_sp;
                if let Some(t) = next_tick {
                    if a_to_b {
                        self.current_tick = t - 1;
                        self.cross_tick(t, false);
                    } else {
                        self.current_tick = t;
                        self.cross_tick(t, true);
                    }
                } else {
                    break;
                }
            }
        }

        let actual_in = amount_in as f64 - remaining_in;
        if actual_in < 1.0 || total_out < 1.0 {
            return Err(AmmError::InsufficientLiquidity);
        }

        // Update current_tick from sqrt_price
        #[allow(clippy::cast_possible_truncation)]
        let new_tick = (self.sqrt_price.powi(2).ln() / BASE.ln()).floor() as i32;
        self.current_tick = new_tick;

        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        Ok((total_out.floor() as u128, total_fee.ceil() as u128))
    }
}

impl FromConfig<ClmmConfig> for ClmmPool {
    /// Creates a new pool from the given configuration.
    ///
    /// Positions from the config are loaded into the tick map and
    /// `current_liquidity` is computed as the sum of all positions
    /// that straddle `current_tick`.
    ///
    /// # Errors
    ///
    /// - Propagates any error from [`ClmmConfig::validate`].
    fn from_config(config: &ClmmConfig) -> Result<Self, AmmError> {
        config.validate()?;

        let current_tick = config.current_tick().get();
        let sqrt_price = Self::sqrt_price_at_tick(current_tick);

        let mut pool = Self {
            token_pair: *config.token_pair(),
            fee_tier: config.fee_tier(),
            tick_spacing: config.tick_spacing(),
            current_tick,
            sqrt_price,
            current_liquidity: 0,
            fee_growth_global_a: 0,
            fee_growth_global_b: 0,
            tick_states: BTreeMap::new(),
            positions: Vec::new(),
        };

        // Load initial positions from config
        for pos in config.positions() {
            let lower = pos.lower_tick().get();
            let upper = pos.upper_tick().get();
            let liq = pos.liquidity().get();

            if liq == 0 {
                continue;
            }

            // Update tick states
            pool.tick_states.entry(lower).or_default().liquidity_net += liq as i128;
            pool.tick_states.entry(upper).or_default().liquidity_net -= liq as i128;

            // If position straddles current_tick, add to active liquidity
            if lower <= current_tick && current_tick < upper {
                pool.current_liquidity += liq;
            }

            pool.positions.push(ClmmPosition {
                lower_tick: lower,
                upper_tick: upper,
                liquidity: liq,
                fee_growth_inside_last_a: 0,
                fee_growth_inside_last_b: 0,
            });
        }

        Ok(pool)
    }
}

impl SwapPool for ClmmPool {
    /// Executes a token swap using tick-by-tick traversal.
    ///
    /// Fees are deducted from the input at each tick step before
    /// computing the output.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidToken`] if `token_in` is not in the pool pair.
    /// - [`AmmError::InsufficientLiquidity`] if no liquidity is available.
    /// - [`AmmError::Overflow`] if arithmetic overflows.
    fn swap(&mut self, spec: SwapSpec, token_in: Token) -> Result<SwapResult, AmmError> {
        if !self.token_pair.contains(&token_in) {
            return Err(AmmError::InvalidToken(
                "token_in is not part of the pool pair",
            ));
        }

        let a_to_b = token_in == self.token_pair.first();

        match spec {
            SwapSpec::ExactIn { amount_in } => {
                let (amount_out, fee) = self.execute_swap_exact_in(amount_in.get(), a_to_b)?;
                SwapResult::new(amount_in, Amount::new(amount_out), Amount::new(fee))
            }
            SwapSpec::ExactOut { amount_out } => {
                // Binary search for the required input
                let target_out = amount_out.get();
                let mut low: u128 = 1;
                let mut high: u128 = target_out.saturating_mul(100).max(1_000_000);

                // Save pool state for rollback during search
                let saved = self.clone();
                let mut best_in: Option<u128> = None;

                for _ in 0..128 {
                    if low > high {
                        break;
                    }
                    let mid = low + (high - low) / 2;
                    *self = saved.clone();

                    match self.execute_swap_exact_in(mid, a_to_b) {
                        Ok((out, _)) => {
                            if out >= target_out {
                                best_in = Some(mid);
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

                let Some(required_in) = best_in else {
                    *self = saved;
                    return Err(AmmError::InsufficientLiquidity);
                };

                // Execute with the found input
                *self = saved;
                let (actual_out, fee) = self.execute_swap_exact_in(required_in, a_to_b)?;

                if actual_out < target_out {
                    return Err(AmmError::InsufficientLiquidity);
                }

                SwapResult::new(
                    Amount::new(required_in),
                    Amount::new(actual_out),
                    Amount::new(fee),
                )
            }
        }
    }

    /// Returns the spot price at the current tick: `1.0001^current_tick`.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidToken`] if either token is not in the pair.
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

        // price = 1.0001^current_tick = sqrt_price^2
        let price_val = self.sqrt_price * self.sqrt_price;
        let is_base_a = *base == self.token_pair.first();

        if is_base_a {
            // price(A→B) = P
            Price::new(price_val)
        } else {
            // price(B→A) = 1/P
            if price_val == 0.0 {
                return Err(AmmError::DivisionByZero);
            }
            Price::new(1.0 / price_val)
        }
    }

    fn token_pair(&self) -> &TokenPair {
        &self.token_pair
    }

    fn fee_tier(&self) -> FeeTier {
        self.fee_tier
    }
}

impl LiquidityPool for ClmmPool {
    /// Adds liquidity to a tick range.
    ///
    /// The `change` must be a [`LiquidityChange::Add`] variant.  The
    /// `amount_a` field is interpreted as the liquidity amount (in
    /// liquidity units, not token amounts) and `amount_b` encodes the
    /// tick range via `lower_tick * 1_000_000 + upper_tick` (offset by
    /// 1_000_000 to handle negative ticks).
    ///
    /// **Simplified encoding**: for a library that normally receives
    /// structured parameters, we use `amount_a` as the liquidity amount
    /// and `amount_b` as an encoded tick-range key:
    /// `amount_b = (lower_tick + 1_000_000) * 10_000_000 + (upper_tick + 1_000_000)`.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidLiquidity`] if `change` is not `Add`.
    /// - [`AmmError::InvalidQuantity`] if liquidity is zero.
    /// - [`AmmError::InvalidTickRange`] if ticks are not aligned.
    fn add_liquidity(&mut self, change: &LiquidityChange) -> Result<Amount, AmmError> {
        let LiquidityChange::Add { amount_a, amount_b } = *change else {
            return Err(AmmError::InvalidLiquidity(
                "expected LiquidityChange::Add variant",
            ));
        };

        let liq = amount_a.get();
        if liq == 0 {
            return Err(AmmError::InvalidQuantity(
                "liquidity amount must be non-zero",
            ));
        }

        // Decode tick range from amount_b
        let encoded = amount_b.get();
        let offset = 1_000_000u128;
        let scale = 10_000_000u128;
        let lower_encoded = encoded / scale;
        let upper_encoded = encoded % scale;

        #[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
        let lower_tick = (lower_encoded as i64 - offset as i64) as i32;
        #[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
        let upper_tick = (upper_encoded as i64 - offset as i64) as i32;

        if lower_tick >= upper_tick {
            return Err(AmmError::InvalidTickRange(
                "lower tick must be less than upper tick",
            ));
        }

        let spacing = self.tick_spacing as i32;
        if spacing > 0 && (lower_tick % spacing != 0 || upper_tick % spacing != 0) {
            return Err(AmmError::InvalidTickRange(
                "ticks must be aligned to tick spacing",
            ));
        }

        // Update tick states
        self.tick_states
            .entry(lower_tick)
            .or_default()
            .liquidity_net += liq as i128;
        self.tick_states
            .entry(upper_tick)
            .or_default()
            .liquidity_net -= liq as i128;

        // If position straddles current_tick, update active liquidity
        if lower_tick <= self.current_tick && self.current_tick < upper_tick {
            self.current_liquidity += liq;
        }

        // Record fee growth snapshots
        let (fg_inside_a, fg_inside_b) = self.fee_growth_inside(lower_tick, upper_tick);

        self.positions.push(ClmmPosition {
            lower_tick,
            upper_tick,
            liquidity: liq,
            fee_growth_inside_last_a: fg_inside_a,
            fee_growth_inside_last_b: fg_inside_b,
        });

        Ok(Amount::new(liq))
    }

    /// Removes liquidity from a position.
    ///
    /// The `change` must be a [`LiquidityChange::Remove`] variant.
    /// Removes from the most recently added position that matches the
    /// requested liquidity amount.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidLiquidity`] if `change` is not `Remove`.
    /// - [`AmmError::InsufficientLiquidity`] if no matching position.
    fn remove_liquidity(&mut self, change: &LiquidityChange) -> Result<Amount, AmmError> {
        let LiquidityChange::Remove { liquidity } = *change else {
            return Err(AmmError::InvalidLiquidity(
                "expected LiquidityChange::Remove variant",
            ));
        };

        let liq_to_remove = liquidity.get();
        if liq_to_remove == 0 {
            return Err(AmmError::InvalidLiquidity("cannot remove zero liquidity"));
        }

        // Find a position with enough liquidity
        let pos_idx = self
            .positions
            .iter()
            .position(|p| p.liquidity >= liq_to_remove)
            .ok_or(AmmError::InsufficientLiquidity)?;

        #[allow(clippy::indexing_slicing)]
        let pos = &self.positions[pos_idx];
        let lower = pos.lower_tick;
        let upper = pos.upper_tick;

        // Compute fees owed
        let (fg_inside_a, fg_inside_b) = self.fee_growth_inside(lower, upper);
        let fees_a = liq_to_remove
            .checked_mul(fg_inside_a.wrapping_sub(pos.fee_growth_inside_last_a))
            .unwrap_or(0)
            >> 64;
        let fees_b = liq_to_remove
            .checked_mul(fg_inside_b.wrapping_sub(pos.fee_growth_inside_last_b))
            .unwrap_or(0)
            >> 64;

        // Update tick states
        if let Some(state) = self.tick_states.get_mut(&lower) {
            state.liquidity_net -= liq_to_remove as i128;
        }
        if let Some(state) = self.tick_states.get_mut(&upper) {
            state.liquidity_net += liq_to_remove as i128;
        }

        // Update active liquidity if position straddles current_tick
        if lower <= self.current_tick && self.current_tick < upper {
            self.current_liquidity = self.current_liquidity.saturating_sub(liq_to_remove);
        }

        // Update or remove position
        #[allow(clippy::indexing_slicing)]
        if self.positions[pos_idx].liquidity == liq_to_remove {
            self.positions.remove(pos_idx);
        } else {
            #[allow(clippy::indexing_slicing)]
            {
                self.positions[pos_idx].liquidity -= liq_to_remove;
                self.positions[pos_idx].fee_growth_inside_last_a = fg_inside_a;
                self.positions[pos_idx].fee_growth_inside_last_b = fg_inside_b;
            }
        }

        // Return total withdrawn value (fees_a + fees_b as proxy)
        Ok(Amount::new(liq_to_remove + fees_a + fees_b))
    }

    /// Collects accumulated fees for a position.
    ///
    /// Uses the position's tick range to compute fee_growth_inside and
    /// returns fees earned since the last snapshot.
    ///
    /// # Errors
    ///
    /// - Returns [`AmmError::PositionNotFound`] if no matching position.
    fn collect_fees(&mut self, position: &Position) -> Result<Amount, AmmError> {
        let lower = position.lower_tick().get();
        let upper = position.upper_tick().get();

        let pos_idx = self
            .positions
            .iter()
            .position(|p| p.lower_tick == lower && p.upper_tick == upper)
            .ok_or(AmmError::PositionNotFound)?;

        let (fg_inside_a, fg_inside_b) = self.fee_growth_inside(lower, upper);

        #[allow(clippy::indexing_slicing)]
        let pos = &self.positions[pos_idx];
        let fees_a = pos
            .liquidity
            .checked_mul(fg_inside_a.wrapping_sub(pos.fee_growth_inside_last_a))
            .unwrap_or(0)
            >> 64;
        let fees_b = pos
            .liquidity
            .checked_mul(fg_inside_b.wrapping_sub(pos.fee_growth_inside_last_b))
            .unwrap_or(0)
            >> 64;

        // Update snapshots
        #[allow(clippy::indexing_slicing)]
        {
            self.positions[pos_idx].fee_growth_inside_last_a = fg_inside_a;
            self.positions[pos_idx].fee_growth_inside_last_b = fg_inside_b;
        }

        Ok(Amount::new(fees_a + fees_b))
    }

    fn total_liquidity(&self) -> Liquidity {
        let total: u128 = self.positions.iter().map(|p| p.liquidity).sum();
        Liquidity::new(total)
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

    fn tick(v: i32) -> Tick {
        let Ok(t) = Tick::new(v) else {
            panic!("valid tick expected");
        };
        t
    }

    fn pos(lower: i32, upper: i32, liq: u128) -> Position {
        let Ok(p) = Position::new(tick(lower), tick(upper), Liquidity::new(liq)) else {
            panic!("expected valid position");
        };
        p
    }

    /// Encodes a tick range into the `amount_b` field for `add_liquidity`.
    fn encode_ticks(lower: i32, upper: i32) -> Amount {
        let offset = 1_000_000u128;
        let scale = 10_000_000u128;
        let encoded =
            (lower as i64 + offset as i64) as u128 * scale + (upper as i64 + offset as i64) as u128;
        Amount::new(encoded)
    }

    fn unknown_token() -> Token {
        let Ok(d) = Decimals::new(8) else {
            panic!("valid decimals");
        };
        Token::new(TokenAddress::from_bytes([99u8; 32]), d)
    }

    /// Creates a pool with a single wide position straddling tick 0.
    fn make_pool_with_position(lower: i32, upper: i32, liq: u128) -> ClmmPool {
        let Ok(cfg) = ClmmConfig::new(
            make_pair(),
            fee_30bp(),
            10,
            tick(0),
            vec![pos(lower, upper, liq)],
        ) else {
            panic!("valid config");
        };
        let Ok(pool) = ClmmPool::from_config(&cfg) else {
            panic!("valid pool");
        };
        pool
    }

    // -- FromConfig -----------------------------------------------------------

    #[test]
    fn from_config_empty_positions() {
        let Ok(cfg) = ClmmConfig::new(make_pair(), fee_30bp(), 10, tick(0), vec![]) else {
            panic!("valid config");
        };
        let Ok(pool) = ClmmPool::from_config(&cfg) else {
            panic!("valid pool");
        };
        assert_eq!(pool.current_tick_index(), 0);
        assert_eq!(pool.current_liquidity(), 0);
        assert_eq!(pool.position_count(), 0);
        assert_eq!(pool.total_liquidity(), Liquidity::ZERO);
    }

    #[test]
    fn from_config_with_positions() {
        let pool = make_pool_with_position(-100, 100, 1_000_000);
        assert_eq!(pool.current_tick_index(), 0);
        assert_eq!(pool.current_liquidity(), 1_000_000);
        assert_eq!(pool.position_count(), 1);
        assert_eq!(pool.total_liquidity(), Liquidity::new(1_000_000));
    }

    #[test]
    fn from_config_position_not_straddling() {
        // Position entirely above current tick → not active
        let Ok(cfg) = ClmmConfig::new(
            make_pair(),
            fee_30bp(),
            10,
            tick(0),
            vec![pos(100, 200, 500)],
        ) else {
            panic!("valid config");
        };
        let Ok(pool) = ClmmPool::from_config(&cfg) else {
            panic!("valid pool");
        };
        assert_eq!(pool.current_liquidity(), 0);
        assert_eq!(pool.total_liquidity(), Liquidity::new(500));
    }

    // -- spot_price -----------------------------------------------------------

    #[test]
    fn spot_price_at_tick_zero() {
        let pool = make_pool_with_position(-100, 100, 1_000_000);
        let Ok(price) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };
        // At tick 0, price = 1.0001^0 = 1.0
        assert!((price.get() - 1.0).abs() < 0.01);
    }

    #[test]
    fn spot_price_inverse() {
        let pool = make_pool_with_position(-100, 100, 1_000_000);
        let Ok(p_ab) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };
        let Ok(p_ba) = pool.spot_price(&tok_b(), &tok_a()) else {
            panic!("expected Ok");
        };
        assert!((p_ab.get() * p_ba.get() - 1.0).abs() < 0.01);
    }

    #[test]
    fn spot_price_same_token() {
        let pool = make_pool_with_position(-100, 100, 1_000_000);
        let Ok(price) = pool.spot_price(&tok_a(), &tok_a()) else {
            panic!("expected Ok");
        };
        assert!((price.get() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn spot_price_invalid_token_rejected() {
        let pool = make_pool_with_position(-100, 100, 1_000_000);
        let result = pool.spot_price(&unknown_token(), &tok_b());
        assert!(matches!(result, Err(AmmError::InvalidToken(_))));
    }

    // -- Scenario 1: Swap Within Single Tick Range ----------------------------

    #[test]
    fn swap_within_single_tick_range() {
        let mut pool = make_pool_with_position(-1000, 1000, 10_000_000);
        let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("expected Ok");
        };
        assert_eq!(result.amount_in(), Amount::new(1_000));
        assert!(result.amount_out().get() > 0);
        assert!(result.fee().get() > 0);
        // Price should still be near 1.0 for small swap
        let Ok(price) = pool.spot_price(&tok_a(), &tok_b()) else {
            panic!("expected Ok");
        };
        assert!((price.get() - 1.0).abs() < 0.1);
    }

    // -- Scenario 2: Swap Crossing Single Tick Boundary -----------------------

    #[test]
    fn swap_crossing_one_tick() {
        // Two adjacent positions
        let Ok(cfg) = ClmmConfig::new(
            make_pair(),
            fee_30bp(),
            10,
            tick(0),
            vec![pos(-100, 10, 1_000_000), pos(10, 200, 2_000_000)],
        ) else {
            panic!("valid config");
        };
        let Ok(mut pool) = ClmmPool::from_config(&cfg) else {
            panic!("valid pool");
        };
        // Pool should have liquidity from first position at tick 0
        assert_eq!(pool.current_liquidity(), 1_000_000);

        // Large swap B→A to push price up past tick 10
        let Ok(spec) = SwapSpec::exact_in(Amount::new(100_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_b()) else {
            panic!("expected Ok");
        };
        assert!(result.amount_out().get() > 0);
        // After crossing tick 10, liquidity should change
    }

    // -- Scenario 3: Swap Crossing Multiple Ticks -----------------------------

    #[test]
    fn swap_crossing_multiple_ticks() {
        let Ok(cfg) = ClmmConfig::new(
            make_pair(),
            fee_30bp(),
            10,
            tick(0),
            vec![
                pos(-200, -100, 500_000),
                pos(-100, 0, 1_000_000),
                pos(0, 100, 1_500_000),
                pos(100, 200, 800_000),
            ],
        ) else {
            panic!("valid config");
        };
        let Ok(mut pool) = ClmmPool::from_config(&cfg) else {
            panic!("valid pool");
        };

        // Large swap to cross multiple ticks
        let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_b()) else {
            panic!("expected Ok");
        };
        assert!(result.amount_out().get() > 0);
        // Price should have moved up
        assert!(pool.current_tick_index() > 0);
    }

    // -- Scenario 4: Add Position Below Current Price -------------------------

    #[test]
    fn position_below_current_price() {
        let Ok(cfg) = ClmmConfig::new(
            make_pair(),
            fee_30bp(),
            10,
            tick(100),
            vec![pos(-200, -100, 500_000)],
        ) else {
            panic!("valid config");
        };
        let Ok(pool) = ClmmPool::from_config(&cfg) else {
            panic!("valid pool");
        };
        // Position is below current tick → not active
        assert_eq!(pool.current_liquidity(), 0);
        assert_eq!(pool.total_liquidity(), Liquidity::new(500_000));
    }

    // -- Scenario 5: Add Position Above Current Price -------------------------

    #[test]
    fn position_above_current_price() {
        let Ok(cfg) = ClmmConfig::new(
            make_pair(),
            fee_30bp(),
            10,
            tick(0),
            vec![pos(500, 600, 300_000)],
        ) else {
            panic!("valid config");
        };
        let Ok(pool) = ClmmPool::from_config(&cfg) else {
            panic!("valid pool");
        };
        // Position is above current tick → not active
        assert_eq!(pool.current_liquidity(), 0);
        assert_eq!(pool.total_liquidity(), Liquidity::new(300_000));
    }

    // -- Scenario 6: Add Position Spanning Current Price ----------------------

    #[test]
    fn position_spanning_current_price() {
        let pool = make_pool_with_position(-500, 500, 2_000_000);
        assert_eq!(pool.current_liquidity(), 2_000_000);
    }

    // -- Scenario 7: Multiple Overlapping Positions ---------------------------

    #[test]
    fn multiple_overlapping_positions() {
        let Ok(cfg) = ClmmConfig::new(
            make_pair(),
            fee_30bp(),
            10,
            tick(0),
            vec![
                pos(-100, 200, 1_000_000),
                pos(-50, 250, 500_000),
                pos(-50, 200, 300_000),
            ],
        ) else {
            panic!("valid config");
        };
        let Ok(pool) = ClmmPool::from_config(&cfg) else {
            panic!("valid pool");
        };
        // All three straddle tick 0 → all active
        assert_eq!(pool.current_liquidity(), 1_800_000);
        assert_eq!(pool.position_count(), 3);
    }

    // -- Scenario 8: Position Removal -----------------------------------------

    #[test]
    fn remove_liquidity_full() {
        let mut pool = make_pool_with_position(-100, 100, 1_000_000);
        assert_eq!(pool.current_liquidity(), 1_000_000);

        let Ok(change) = LiquidityChange::remove(Liquidity::new(1_000_000)) else {
            panic!("valid change");
        };
        let Ok(returned) = pool.remove_liquidity(&change) else {
            panic!("expected Ok");
        };
        assert!(returned.get() >= 1_000_000);
        assert_eq!(pool.current_liquidity(), 0);
        assert_eq!(pool.position_count(), 0);
    }

    #[test]
    fn remove_liquidity_partial() {
        let mut pool = make_pool_with_position(-100, 100, 1_000_000);

        let Ok(change) = LiquidityChange::remove(Liquidity::new(400_000)) else {
            panic!("valid change");
        };
        let Ok(_) = pool.remove_liquidity(&change) else {
            panic!("expected Ok");
        };
        assert_eq!(pool.current_liquidity(), 600_000);
        assert_eq!(pool.position_count(), 1);
    }

    // -- Scenario 9: Swap Exactly at Tick Boundary ----------------------------

    #[test]
    fn swap_at_tick_boundary() {
        // Pool with position exactly at [0, 10]
        let Ok(cfg) = ClmmConfig::new(
            make_pair(),
            fee_30bp(),
            10,
            tick(0),
            vec![pos(0, 10, 5_000_000)],
        ) else {
            panic!("valid config");
        };
        let Ok(mut pool) = ClmmPool::from_config(&cfg) else {
            panic!("valid pool");
        };
        assert_eq!(pool.current_liquidity(), 5_000_000);

        // Small swap should work
        let Ok(spec) = SwapSpec::exact_in(Amount::new(100)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_b()) else {
            panic!("expected Ok");
        };
        assert!(result.amount_out().get() > 0);
    }

    // -- Scenario 10: Empty Liquidity at Current Price ------------------------

    #[test]
    fn empty_liquidity_jumps_to_next_tick() {
        // Gap in liquidity at current tick
        let Ok(cfg) = ClmmConfig::new(
            make_pair(),
            fee_30bp(),
            10,
            tick(0),
            vec![pos(100, 200, 1_000_000)],
        ) else {
            panic!("valid config");
        };
        let Ok(mut pool) = ClmmPool::from_config(&cfg) else {
            panic!("valid pool");
        };
        assert_eq!(pool.current_liquidity(), 0);

        // Swap B→A: price increases, should jump to tick 100 where liquidity is
        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_b()) else {
            panic!("expected Ok");
        };
        assert!(result.amount_out().get() > 0);
    }

    // -- Scenario 11: Fee Growth Accumulation ---------------------------------

    #[test]
    fn fee_growth_increases_monotonically() {
        let mut pool = make_pool_with_position(-1000, 1000, 10_000_000);

        let mut prev_fg_a = pool.fee_growth_global_a();

        for _ in 0..10 {
            let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
                panic!("valid spec");
            };
            let Ok(_) = pool.swap(spec, tok_a()) else {
                panic!("expected Ok");
            };
            assert!(pool.fee_growth_global_a() >= prev_fg_a);
            prev_fg_a = pool.fee_growth_global_a();
        }
        // Fee growth should be positive after swaps
        assert!(pool.fee_growth_global_a() > 0);
    }

    // -- Scenario 12: Collect Fees After Swaps --------------------------------

    #[test]
    fn collect_fees_after_swaps() {
        let mut pool = make_pool_with_position(-1000, 1000, 10_000_000);

        // Perform several swaps
        for _ in 0..5 {
            let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
                panic!("valid spec");
            };
            let Ok(_) = pool.swap(spec, tok_a()) else {
                panic!("expected Ok");
            };
        }

        // Collect fees for the position
        let position = pos(-1000, 1000, 10_000_000);
        let Ok(fees) = pool.collect_fees(&position) else {
            panic!("expected Ok");
        };
        // Fees should be positive
        assert!(fees.get() > 0);

        // Collecting again immediately should yield zero
        let Ok(fees2) = pool.collect_fees(&position) else {
            panic!("expected Ok");
        };
        assert_eq!(fees2, Amount::ZERO);
    }

    // -- Add Liquidity via trait -----------------------------------------------

    #[test]
    fn add_liquidity_via_trait() {
        let mut pool = make_pool_with_position(-100, 100, 1_000_000);
        assert_eq!(pool.position_count(), 1);

        let encoded = encode_ticks(-200, 200);
        let Ok(change) = LiquidityChange::add(Amount::new(500_000), encoded) else {
            panic!("valid change");
        };
        let Ok(minted) = pool.add_liquidity(&change) else {
            panic!("expected Ok");
        };
        assert_eq!(minted, Amount::new(500_000));
        assert_eq!(pool.position_count(), 2);
        // New position straddles current_tick → active
        assert_eq!(pool.current_liquidity(), 1_500_000);
    }

    #[test]
    fn add_liquidity_misaligned_ticks_rejected() {
        let mut pool = make_pool_with_position(-100, 100, 1_000_000);

        // Ticks -5 and 15 are not aligned to spacing=10
        let encoded = encode_ticks(-5, 15);
        let Ok(change) = LiquidityChange::add(Amount::new(100), encoded) else {
            panic!("valid change");
        };
        let result = pool.add_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InvalidTickRange(_))));
    }

    // -- Invalid token --------------------------------------------------------

    #[test]
    fn swap_invalid_token_rejected() {
        let mut pool = make_pool_with_position(-100, 100, 1_000_000);
        let Ok(spec) = SwapSpec::exact_in(Amount::new(100)) else {
            panic!("valid spec");
        };
        let result = pool.swap(spec, unknown_token());
        assert!(matches!(result, Err(AmmError::InvalidToken(_))));
    }

    // -- No liquidity swap fails ----------------------------------------------

    #[test]
    fn swap_no_liquidity_fails() {
        let Ok(cfg) = ClmmConfig::new(make_pair(), fee_30bp(), 10, tick(0), vec![]) else {
            panic!("valid config");
        };
        let Ok(mut pool) = ClmmPool::from_config(&cfg) else {
            panic!("valid pool");
        };
        let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
            panic!("valid spec");
        };
        let result = pool.swap(spec, tok_a());
        assert!(matches!(result, Err(AmmError::InsufficientLiquidity)));
    }

    // -- Wrong variant for add/remove -----------------------------------------

    #[test]
    fn add_liquidity_with_remove_variant_rejected() {
        let mut pool = make_pool_with_position(-100, 100, 1_000_000);
        let Ok(change) = LiquidityChange::remove(Liquidity::new(1)) else {
            panic!("valid change");
        };
        let result = pool.add_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InvalidLiquidity(_))));
    }

    #[test]
    fn remove_liquidity_with_add_variant_rejected() {
        let mut pool = make_pool_with_position(-100, 100, 1_000_000);
        let Ok(change) = LiquidityChange::add(Amount::new(100), Amount::new(200)) else {
            panic!("valid change");
        };
        let result = pool.remove_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InvalidLiquidity(_))));
    }

    // -- Collect fees for non-existent position -------------------------------

    #[test]
    fn collect_fees_position_not_found() {
        let mut pool = make_pool_with_position(-100, 100, 1_000_000);
        let orphan = pos(-500, 500, 1);
        let result = pool.collect_fees(&orphan);
        assert!(matches!(result, Err(AmmError::PositionNotFound)));
    }

    // -- Accessors ------------------------------------------------------------

    #[test]
    fn accessors() {
        let pool = make_pool_with_position(-100, 100, 1_000_000);
        assert_eq!(*pool.token_pair(), make_pair());
        assert_eq!(pool.fee_tier(), fee_30bp());
        assert!(pool.sqrt_price() > 0.0);
    }

    // -- Price movement direction ---------------------------------------------

    #[test]
    fn price_moves_down_when_selling_a() {
        let mut pool = make_pool_with_position(-1000, 1000, 10_000_000);
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
        // Selling A → more A in pool → price of A decreases (price A→B decreases)
        assert!(p_after.get() < p_before.get());
    }

    #[test]
    fn price_moves_up_when_selling_b() {
        let mut pool = make_pool_with_position(-1000, 1000, 10_000_000);
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
        // Selling B → more B in pool → price of A increases (price A→B increases)
        assert!(p_after.get() > p_before.get());
    }

    // -- Debug ----------------------------------------------------------------

    #[test]
    fn debug_format_contains_struct_name() {
        let pool = make_pool_with_position(-100, 100, 1_000);
        let dbg = format!("{pool:?}");
        assert!(dbg.contains("ClmmPool"));
    }

    // -- ExactOut swap --------------------------------------------------------

    #[test]
    fn swap_exact_out() {
        let mut pool = make_pool_with_position(-1000, 1000, 10_000_000);
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
}
