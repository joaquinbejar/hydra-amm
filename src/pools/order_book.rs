//! Order Book hybrid pool implementation (Phoenix style).
//!
//! Wraps the [`orderbook_rs::OrderBook`] crate as a central limit order
//! book (CLOB) matching engine behind the [`SwapPool`] and
//! [`LiquidityPool`] trait interfaces.
//!
//! # Design
//!
//! - **Swap** → market order submission via
//!   `OrderBook::submit_market_order`.
//! - **Add liquidity** → limit order placement via
//!   `OrderBook::add_limit_order`.
//! - **Remove liquidity** → order cancellation via
//!   `OrderBook::cancel_order`.
//! - **Spot price** → mid-price derived from best bid / best ask.
//!
//! # Fee Handling
//!
//! Taker fees are deducted from the input amount before the market
//! order is submitted to the book.  Accumulated fees are tracked per
//! token (base / quote) and can be collected via [`LiquidityPool::collect_fees`].
//!
//! # Quantity Conversion
//!
//! The AMM domain uses [`Amount`] (`u128`) while `orderbook-rs` uses
//! `u64` for quantities.  Conversions are checked — an
//! [`AmmError::Overflow`] is returned if the quantity exceeds `u64::MAX`.

use crate::config::OrderBookConfig;
use crate::domain::{
    Amount, FeeTier, Liquidity, LiquidityChange, Position, Price, Rounding, SwapResult, SwapSpec,
    Token, TokenPair,
};
use crate::error::AmmError;
use crate::traits::{FromConfig, LiquidityPool, SwapPool};
use orderbook_rs::{DefaultOrderBook, OrderId, Side, TimeInForce};

/// An Order Book hybrid AMM pool.
///
/// Created from an [`OrderBookConfig`] via [`FromConfig`].  Wraps an
/// [`orderbook_rs::OrderBook`] engine for CLOB matching with FIFO
/// price-time priority.
///
/// # State
///
/// - `token_pair` — the two tokens traded in this book
/// - `fee_tier` — taker fee (deducted from input before matching)
/// - `tick_size` — minimum price increment for limit orders
/// - `lot_size` — minimum quantity increment for orders
/// - `inner` — the `orderbook-rs` CLOB engine
/// - `accumulated_fees_base` / `accumulated_fees_quote` — fee counters
///
/// # Trait Limitations
///
/// [`OrderBook`](orderbook_rs::OrderBook) uses internal concurrent data
/// structures (`Arc`, `DashMap`, `SkipMap`) and does **not** implement
/// `Clone` or `PartialEq`.  Consequently, `OrderBookPool` cannot derive
/// those traits.  [`PoolBox`](crate::pools::pool_box::PoolBox) only
/// requires `Debug`, so this is fine.
pub struct OrderBookPool {
    token_pair: TokenPair,
    fee_tier: FeeTier,
    tick_size: Amount,
    lot_size: Amount,
    inner: DefaultOrderBook,
    accumulated_fees_base: Amount,
    accumulated_fees_quote: Amount,
}

impl core::fmt::Debug for OrderBookPool {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("OrderBookPool")
            .field("token_pair", &self.token_pair)
            .field("fee_tier", &self.fee_tier)
            .field("tick_size", &self.tick_size)
            .field("lot_size", &self.lot_size)
            .field("symbol", &self.inner.symbol())
            .field("accumulated_fees_base", &self.accumulated_fees_base)
            .field("accumulated_fees_quote", &self.accumulated_fees_quote)
            .finish()
    }
}

impl OrderBookPool {
    /// Returns the tick size (minimum price increment).
    pub const fn tick_size(&self) -> Amount {
        self.tick_size
    }

    /// Returns the lot size (minimum quantity increment).
    pub const fn lot_size(&self) -> Amount {
        self.lot_size
    }

    /// Returns accumulated fees for the base token.
    pub const fn accumulated_fees_base(&self) -> Amount {
        self.accumulated_fees_base
    }

    /// Returns accumulated fees for the quote token.
    pub const fn accumulated_fees_quote(&self) -> Amount {
        self.accumulated_fees_quote
    }

    /// Returns the best bid price, if any.
    pub fn best_bid(&self) -> Option<u128> {
        self.inner.best_bid()
    }

    /// Returns the best ask price, if any.
    pub fn best_ask(&self) -> Option<u128> {
        self.inner.best_ask()
    }

    /// Returns the mid-price as `(best_bid + best_ask) / 2`, if both
    /// sides have orders.
    pub fn mid_price_raw(&self) -> Option<f64> {
        self.inner.mid_price()
    }

    /// Returns a reference to the inner `OrderBook` engine.
    pub const fn inner(&self) -> &DefaultOrderBook {
        &self.inner
    }

    /// Places a limit order in the book.
    ///
    /// This is the low-level method used by [`LiquidityPool::add_liquidity`].
    ///
    /// # Arguments
    ///
    /// - `price` — limit price (must be a multiple of `tick_size`)
    /// - `quantity` — order size in base units (must be a multiple of `lot_size`)
    /// - `side` — [`Side::Buy`] or [`Side::Sell`]
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidConfiguration`] if price is not aligned to
    ///   tick size or quantity is not aligned to lot size.
    /// - [`AmmError::Overflow`] if quantity exceeds `u64::MAX`.
    pub fn place_limit_order(
        &self,
        price: u128,
        quantity: u128,
        side: Side,
    ) -> Result<OrderId, AmmError> {
        // Validate tick alignment
        if self.tick_size.get() > 0 && !price.is_multiple_of(self.tick_size.get()) {
            return Err(AmmError::InvalidConfiguration(
                "price must be a multiple of tick_size",
            ));
        }

        // Validate lot alignment
        if self.lot_size.get() > 0 && !quantity.is_multiple_of(self.lot_size.get()) {
            return Err(AmmError::InvalidConfiguration(
                "quantity must be a multiple of lot_size",
            ));
        }

        let qty_u64 =
            u64::try_from(quantity).map_err(|_| AmmError::Overflow("quantity exceeds u64::MAX"))?;

        if qty_u64 == 0 {
            return Err(AmmError::InvalidQuantity("quantity must be non-zero"));
        }

        let id = OrderId::new();
        self.inner
            .add_limit_order(id, price, qty_u64, side, TimeInForce::Gtc, None)
            .map_err(|_| AmmError::InvalidConfiguration("orderbook: order placement failed"))?;

        Ok(id)
    }

    /// Converts an [`Amount`] to `u64`, returning an error on overflow.
    fn amount_to_u64(amount: Amount) -> Result<u64, AmmError> {
        u64::try_from(amount.get()).map_err(|_| AmmError::Overflow("amount exceeds u64::MAX"))
    }

    /// Computes the output amount from a market order match result.
    ///
    /// For a **sell** (selling base to get quote):
    ///   `output = Σ (fill_price × fill_qty)` for each fill
    ///
    /// For a **buy** (selling quote to get base):
    ///   `output = Σ fill_qty` (the base tokens received)
    ///
    /// The input consumed is `executed_quantity` (what was taken from
    /// the taker's net input).
    #[allow(clippy::cast_possible_truncation)]
    fn compute_swap_output(
        &self,
        side: Side,
        executed_qty: u64,
        executed_value: u128,
    ) -> Result<(Amount, Amount), AmmError> {
        if executed_qty == 0 {
            return Err(AmmError::InsufficientLiquidity);
        }

        match side {
            // Selling base → output is quote (executed_value = Σ price × qty)
            Side::Sell => {
                let amount_in = Amount::new(u128::from(executed_qty));
                let amount_out = Amount::new(executed_value);
                Ok((amount_in, amount_out))
            }
            // Buying base → output is base (executed_qty)
            // Input consumed is executed_value (quote tokens spent)
            Side::Buy => {
                let amount_in = Amount::new(executed_value);
                let amount_out = Amount::new(u128::from(executed_qty));
                Ok((amount_in, amount_out))
            }
        }
    }
}

impl FromConfig<OrderBookConfig> for OrderBookPool {
    /// Creates a new pool from the given configuration.
    ///
    /// Initialises an empty `orderbook-rs` order book with a symbol
    /// derived from the token pair addresses.
    ///
    /// # Errors
    ///
    /// Propagates any error from [`OrderBookConfig::validate`].
    fn from_config(config: &OrderBookConfig) -> Result<Self, AmmError> {
        config.validate()?;

        let symbol = "HYDRA";
        let book = DefaultOrderBook::new(symbol);

        Ok(Self {
            token_pair: *config.token_pair(),
            fee_tier: config.fee_tier(),
            tick_size: config.tick_size(),
            lot_size: config.lot_size(),
            inner: book,
            accumulated_fees_base: Amount::ZERO,
            accumulated_fees_quote: Amount::ZERO,
        })
    }
}

impl SwapPool for OrderBookPool {
    /// Executes a swap by submitting a market order to the CLOB.
    ///
    /// 1. Deduct taker fee from `amount_in`
    /// 2. Determine side: `token_in == first` → `Sell` (sell base,
    ///    receive quote); else → `Buy` (sell quote, receive base)
    /// 3. Submit market order for `net_input` quantity
    /// 4. Compute output from match fills
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidToken`] if `token_in` is not in the pair.
    /// - [`AmmError::InsufficientLiquidity`] if the book cannot fill.
    /// - [`AmmError::Overflow`] if quantity conversion fails.
    fn swap(&mut self, spec: SwapSpec, token_in: Token) -> Result<SwapResult, AmmError> {
        if !self.token_pair.contains(&token_in) {
            return Err(AmmError::InvalidToken(
                "token_in is not part of the pool pair",
            ));
        }

        let is_sell_base = token_in == self.token_pair.first();

        match spec {
            SwapSpec::ExactIn { amount_in } => {
                // Deduct fee
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

                // Determine side and quantity for the market order
                let (side, qty) = if is_sell_base {
                    // Selling base tokens → Side::Sell
                    (Side::Sell, Self::amount_to_u64(net_input)?)
                } else {
                    // Selling quote to buy base → Side::Buy
                    // For buy side, we need to estimate how much base we can get.
                    // We simulate the order to determine fill quantity.
                    let sim = self
                        .inner
                        .simulate_market_order(Self::amount_to_u64(net_input)?, Side::Buy);
                    if sim.total_filled == 0 {
                        return Err(AmmError::InsufficientLiquidity);
                    }
                    (Side::Buy, Self::amount_to_u64(net_input)?)
                };

                // Submit market order
                let order_id = OrderId::new();
                let match_result = self
                    .inner
                    .submit_market_order(order_id, qty, side)
                    .map_err(|_| AmmError::InsufficientLiquidity)?;

                let exec_qty = match_result.executed_quantity();
                let exec_value = match_result.executed_value();

                let (consumed_in, amount_out) =
                    self.compute_swap_output(side, exec_qty, exec_value)?;

                // For partial fills, the actual amount_in is fee + consumed
                let actual_amount_in = if is_sell_base {
                    // Consumed is base tokens matched
                    consumed_in
                        .checked_add(&fee)
                        .ok_or(AmmError::Overflow("amount_in + fee overflow"))?
                } else {
                    amount_in
                };

                // Accumulate fees
                if is_sell_base {
                    self.accumulated_fees_base = self
                        .accumulated_fees_base
                        .checked_add(&fee)
                        .ok_or(AmmError::Overflow("accumulated fee overflow"))?;
                } else {
                    self.accumulated_fees_quote = self
                        .accumulated_fees_quote
                        .checked_add(&fee)
                        .ok_or(AmmError::Overflow("accumulated fee overflow"))?;
                }

                SwapResult::new(actual_amount_in, amount_out, fee)
            }
            SwapSpec::ExactOut { amount_out } => {
                // For exact-out, simulate to find required input, then execute
                let side = if is_sell_base { Side::Sell } else { Side::Buy };

                // Binary search for the minimum input that produces >= amount_out
                let target_out = amount_out.get();
                let mut lo: u64 = 1;
                let mut hi: u64 = u64::MAX / 2;
                let mut best: Option<(u64, u128, u64, u128)> = None; // (qty, fee, exec_qty, exec_value)

                for _ in 0..64 {
                    if lo > hi {
                        break;
                    }
                    let mid = lo + (hi - lo) / 2;
                    let gross_input = Amount::new(u128::from(mid));

                    let fee_res = self.fee_tier.apply_to_amount(gross_input, Rounding::Up);
                    let Ok(fee_amt) = fee_res else {
                        lo = mid.saturating_add(1);
                        continue;
                    };
                    let Some(net) = gross_input.checked_sub(&fee_amt) else {
                        lo = mid.saturating_add(1);
                        continue;
                    };
                    if net.is_zero() {
                        lo = mid.saturating_add(1);
                        continue;
                    }
                    let Ok(net_u64) = Self::amount_to_u64(net) else {
                        hi = mid.saturating_sub(1);
                        continue;
                    };

                    let sim = self.inner.simulate_market_order(net_u64, side);
                    let (_, out) = match self.compute_swap_output(
                        side,
                        sim.total_filled,
                        sim.fills.iter().map(|(p, q)| p * u128::from(*q)).sum(),
                    ) {
                        Ok(v) => v,
                        Err(_) => {
                            lo = mid.saturating_add(1);
                            continue;
                        }
                    };

                    if out.get() >= target_out {
                        let exec_value: u128 =
                            sim.fills.iter().map(|(p, q)| p * u128::from(*q)).sum();
                        best = Some((mid, fee_amt.get(), sim.total_filled, exec_value));
                        hi = mid.saturating_sub(1);
                    } else {
                        lo = mid.saturating_add(1);
                    }
                }

                let Some((required_gross, fee_val, _, _)) = best else {
                    return Err(AmmError::InsufficientLiquidity);
                };

                // Now actually execute the market order
                let gross = Amount::new(u128::from(required_gross));
                let fee = Amount::new(fee_val);
                let net = gross
                    .checked_sub(&fee)
                    .ok_or(AmmError::Overflow("net input underflow"))?;
                let net_u64 = Self::amount_to_u64(net)?;

                let order_id = OrderId::new();
                let match_result = self
                    .inner
                    .submit_market_order(order_id, net_u64, side)
                    .map_err(|_| AmmError::InsufficientLiquidity)?;

                let exec_qty = match_result.executed_quantity();
                let exec_value = match_result.executed_value();
                let (_, actual_out) = self.compute_swap_output(side, exec_qty, exec_value)?;

                // Accumulate fees
                if is_sell_base {
                    self.accumulated_fees_base = self
                        .accumulated_fees_base
                        .checked_add(&fee)
                        .ok_or(AmmError::Overflow("accumulated fee overflow"))?;
                } else {
                    self.accumulated_fees_quote = self
                        .accumulated_fees_quote
                        .checked_add(&fee)
                        .ok_or(AmmError::Overflow("accumulated fee overflow"))?;
                }

                SwapResult::new(gross, actual_out, fee)
            }
        }
    }

    /// Returns the mid-price derived from the best bid and best ask.
    ///
    /// If `base` is the pool's first token, returns the mid-price
    /// directly.  If inverted, returns `1 / mid_price`.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidToken`] if either token is not in the pair.
    /// - [`AmmError::InsufficientLiquidity`] if one or both sides of the
    ///   book are empty.
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

        let mid = self
            .inner
            .mid_price()
            .ok_or(AmmError::InsufficientLiquidity)?;

        if *base == self.token_pair.first() {
            Price::new(mid)
        } else {
            if mid <= 0.0 {
                return Err(AmmError::DivisionByZero);
            }
            Price::new(1.0 / mid)
        }
    }

    fn token_pair(&self) -> &TokenPair {
        &self.token_pair
    }

    fn fee_tier(&self) -> FeeTier {
        self.fee_tier
    }
}

impl LiquidityPool for OrderBookPool {
    /// Adds liquidity by placing a limit order in the book.
    ///
    /// The `LiquidityChange::Add` variant is interpreted as:
    /// - `amount_a` → base quantity to **sell** (ask side) at an
    ///   internally derived price
    /// - `amount_b` → quote quantity to **bid** (buy side) at an
    ///   internally derived price
    ///
    /// For simplicity, orders are placed at the current best price +/- 1
    /// tick.  If the book is empty, a default mid-price of `tick_size`
    /// is used.
    ///
    /// Returns the total quantity placed as an [`Amount`].
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidLiquidity`] if `change` is not an `Add`
    ///   variant.
    /// - [`AmmError::InvalidQuantity`] if both amounts are zero.
    fn add_liquidity(&mut self, change: &LiquidityChange) -> Result<Amount, AmmError> {
        let LiquidityChange::Add { amount_a, amount_b } = *change else {
            return Err(AmmError::InvalidLiquidity(
                "expected LiquidityChange::Add variant",
            ));
        };

        if amount_a.is_zero() && amount_b.is_zero() {
            return Err(AmmError::InvalidQuantity("must deposit at least one token"));
        }

        let mut total_placed = Amount::ZERO;

        // Place ask order (selling base) if amount_a > 0
        if !amount_a.is_zero() {
            let price = self
                .inner
                .best_ask()
                .unwrap_or(self.tick_size.get().saturating_mul(100));
            self.place_limit_order(price, amount_a.get(), Side::Sell)?;
            total_placed = total_placed
                .checked_add(&amount_a)
                .ok_or(AmmError::Overflow("total placed overflow"))?;
        }

        // Place bid order (buying base) if amount_b > 0
        if !amount_b.is_zero() {
            let price = self
                .inner
                .best_bid()
                .unwrap_or(self.tick_size.get().saturating_mul(99));
            self.place_limit_order(price, amount_b.get(), Side::Buy)?;
            total_placed = total_placed
                .checked_add(&amount_b)
                .ok_or(AmmError::Overflow("total placed overflow"))?;
        }

        Ok(total_placed)
    }

    /// Removes liquidity by cancelling orders from the book.
    ///
    /// This is a simplified implementation that removes all orders and
    /// returns the total cancelled quantity.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidLiquidity`] if `change` is not a `Remove`
    ///   variant or liquidity is zero.
    fn remove_liquidity(&mut self, change: &LiquidityChange) -> Result<Amount, AmmError> {
        let LiquidityChange::Remove { liquidity } = *change else {
            return Err(AmmError::InvalidLiquidity(
                "expected LiquidityChange::Remove variant",
            ));
        };

        if liquidity.is_zero() {
            return Err(AmmError::InvalidLiquidity("cannot remove zero liquidity"));
        }

        // Cancel orders from the book up to the requested liquidity
        let all_orders = self.inner.get_all_orders();
        let mut cancelled_qty: u128 = 0;
        let target = liquidity.get();

        for order_arc in &all_orders {
            if cancelled_qty >= target {
                break;
            }
            let oid = order_arc.id();
            let order_qty = u128::from(order_arc.visible_quantity());

            if self.inner.cancel_order(oid).is_ok() {
                cancelled_qty = cancelled_qty.saturating_add(order_qty);
            }
        }

        if cancelled_qty == 0 {
            return Err(AmmError::InsufficientLiquidity);
        }

        Ok(Amount::new(cancelled_qty))
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

    /// Returns total liquidity as the sum of all resting order
    /// quantities on both sides of the book.
    fn total_liquidity(&self) -> Liquidity {
        let (buy_pressure, sell_pressure) = self.inner.buy_sell_pressure();
        let total = u128::from(buy_pressure).saturating_add(u128::from(sell_pressure));
        Liquidity::new(total)
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;
    use crate::config::OrderBookConfig;
    use crate::domain::{BasisPoints, Decimals, Liquidity, TokenAddress};
    use crate::traits::FromConfig;

    // -- helpers --------------------------------------------------------------

    fn make_pair() -> TokenPair {
        let Ok(d6) = Decimals::new(6) else {
            panic!("valid decimals");
        };
        let Ok(d18) = Decimals::new(18) else {
            panic!("valid decimals");
        };
        let tok_a = Token::new(TokenAddress::from_bytes([1u8; 32]), d6);
        let tok_b = Token::new(TokenAddress::from_bytes([2u8; 32]), d18);
        let Ok(pair) = TokenPair::new(tok_a, tok_b) else {
            panic!("expected valid pair");
        };
        pair
    }

    fn token_a() -> Token {
        let Ok(d6) = Decimals::new(6) else {
            panic!("valid decimals");
        };
        Token::new(TokenAddress::from_bytes([1u8; 32]), d6)
    }

    fn token_b() -> Token {
        let Ok(d18) = Decimals::new(18) else {
            panic!("valid decimals");
        };
        Token::new(TokenAddress::from_bytes([2u8; 32]), d18)
    }

    fn fee() -> FeeTier {
        FeeTier::new(BasisPoints::new(30))
    }

    fn zero_fee() -> FeeTier {
        FeeTier::new(BasisPoints::new(0))
    }

    fn make_pool(fee_tier: FeeTier) -> OrderBookPool {
        let Ok(cfg) = OrderBookConfig::new(make_pair(), fee_tier, Amount::new(1), Amount::new(1))
        else {
            panic!("expected valid config");
        };
        let Ok(pool) = OrderBookPool::from_config(&cfg) else {
            panic!("expected valid pool");
        };
        pool
    }

    fn make_pool_with_sizes(tick: u128, lot: u128) -> OrderBookPool {
        let Ok(cfg) =
            OrderBookConfig::new(make_pair(), zero_fee(), Amount::new(tick), Amount::new(lot))
        else {
            panic!("expected valid config");
        };
        let Ok(pool) = OrderBookPool::from_config(&cfg) else {
            panic!("expected valid pool");
        };
        pool
    }

    // -- FromConfig -----------------------------------------------------------

    #[test]
    fn from_config_creates_pool() {
        let pool = make_pool(fee());
        assert_eq!(*pool.token_pair(), make_pair());
        assert_eq!(pool.fee_tier(), fee());
        assert_eq!(pool.tick_size(), Amount::new(1));
        assert_eq!(pool.lot_size(), Amount::new(1));
    }

    #[test]
    fn from_config_empty_book() {
        let pool = make_pool(fee());
        assert_eq!(pool.total_liquidity(), Liquidity::ZERO);
        assert!(pool.best_bid().is_none());
        assert!(pool.best_ask().is_none());
        assert!(pool.mid_price_raw().is_none());
    }

    // -- Scenario 1: Place Single Limit Order ---------------------------------

    #[test]
    fn test_orderbook_place_single_order() {
        let pool = make_pool(zero_fee());

        // Place sell order: 1000 units at price 150
        let result = pool.place_limit_order(150, 1000, Side::Sell);
        assert!(result.is_ok());

        // Book should have the order on the ask side
        assert_eq!(pool.best_ask(), Some(150));
        assert_eq!(pool.total_liquidity(), Liquidity::new(1000));
    }

    #[test]
    fn place_bid_order() {
        let pool = make_pool(zero_fee());
        let result = pool.place_limit_order(100, 500, Side::Buy);
        assert!(result.is_ok());
        assert_eq!(pool.best_bid(), Some(100));
        assert_eq!(pool.total_liquidity(), Liquidity::new(500));
    }

    // -- Scenario 2: Multiple Orders at Same Price Level ----------------------

    #[test]
    fn test_orderbook_multiple_orders_same_level() {
        let pool = make_pool(zero_fee());

        // Place 3 orders at same price (150), quantities 100, 200, 300
        assert!(pool.place_limit_order(150, 100, Side::Sell).is_ok());
        assert!(pool.place_limit_order(150, 200, Side::Sell).is_ok());
        assert!(pool.place_limit_order(150, 300, Side::Sell).is_ok());

        // Total quantity at level = 600
        let (_, sell_pressure) = pool.inner.buy_sell_pressure();
        assert_eq!(sell_pressure, 600);
        assert_eq!(pool.total_liquidity(), Liquidity::new(600));
    }

    // -- Scenario 3: Swap Matches Single Price Level --------------------------

    #[test]
    fn test_orderbook_swap_matches_single_level() {
        let _pool = make_pool(zero_fee());

        // Place 500 on bid side at price 150
        let mut pool2 = make_pool(zero_fee());
        assert!(pool2.place_limit_order(150, 500, Side::Buy).is_ok());

        // Swap selling base (token_a) → matches against bids
        let Ok(spec) = SwapSpec::exact_in(Amount::new(500)) else {
            panic!("valid spec");
        };
        let result = pool2.swap(spec, token_a());
        assert!(result.is_ok());
        let Ok(sr) = result else {
            panic!("expected Ok");
        };

        // Sold 500 base at price 150 → output = 500 * 150 = 75000 quote
        assert_eq!(sr.amount_out().get(), 75000);
    }

    // -- Scenario 4: Swap Walks Through Multiple Price Levels -----------------

    #[test]
    fn test_orderbook_swap_walks_multiple_levels() {
        let mut pool = make_pool(zero_fee());

        // Place orders on bid side at multiple prices
        assert!(pool.place_limit_order(149, 200, Side::Buy).is_ok());
        assert!(pool.place_limit_order(150, 300, Side::Buy).is_ok());
        assert!(pool.place_limit_order(151, 400, Side::Buy).is_ok());

        // Total bid liquidity = 900
        let (buy_p, _) = pool.inner.buy_sell_pressure();
        assert_eq!(buy_p, 900);

        // Swap 1000 base (sell) — walks through all levels, 100 unmatched
        let Ok(spec) = SwapSpec::exact_in(Amount::new(1000)) else {
            panic!("valid spec");
        };
        let result = pool.swap(spec, token_a());
        assert!(result.is_ok());
        let Ok(sr) = result else {
            panic!("expected Ok");
        };

        // Should match: 400@151 + 300@150 + 200@149 = 900 filled
        // Output = 400*151 + 300*150 + 200*149 = 60400 + 45000 + 29800 = 135200
        assert_eq!(sr.amount_out().get(), 135200);
    }

    // -- Scenario 5: Partial Fill at Price Level ------------------------------

    #[test]
    fn test_orderbook_partial_fill() {
        let mut pool = make_pool(zero_fee());

        // Place 500 on bid side at price 150
        assert!(pool.place_limit_order(150, 500, Side::Buy).is_ok());

        // Swap 300 base → partial fill
        let Ok(spec) = SwapSpec::exact_in(Amount::new(300)) else {
            panic!("valid spec");
        };
        let result = pool.swap(spec, token_a());
        assert!(result.is_ok());
        let Ok(sr) = result else {
            panic!("expected Ok");
        };

        // Matched 300 at price 150 → output = 300 * 150 = 45000
        assert_eq!(sr.amount_out().get(), 45000);

        // Remaining on bid: 500 - 300 = 200
        let (buy_p, _) = pool.inner.buy_sell_pressure();
        assert_eq!(buy_p, 200);
    }

    // -- Scenario 6: Empty Book Behavior --------------------------------------

    #[test]
    fn test_orderbook_empty_book_no_liquidity() {
        let mut pool = make_pool(zero_fee());

        let Ok(spec) = SwapSpec::exact_in(Amount::new(1000)) else {
            panic!("valid spec");
        };
        let result = pool.swap(spec, token_a());
        assert!(matches!(result, Err(AmmError::InsufficientLiquidity)));
    }

    // -- Fee deduction --------------------------------------------------------

    #[test]
    fn swap_deducts_fee_from_input() {
        let mut pool = make_pool(fee()); // 0.30% fee

        // Place large bid liquidity
        assert!(pool.place_limit_order(100, 10_000, Side::Buy).is_ok());

        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let result = pool.swap(spec, token_a());
        assert!(result.is_ok());
        let Ok(sr) = result else {
            panic!("expected Ok");
        };

        // Fee = ceil(10000 * 30 / 10000) = 30
        assert_eq!(sr.fee().get(), 30);

        // Net input = 10000 - 30 = 9970
        // Output = 9970 * 100 = 997000
        assert_eq!(sr.amount_out().get(), 997_000);
    }

    #[test]
    fn accumulated_fees_tracked() {
        let mut pool = make_pool(fee());
        assert!(pool.place_limit_order(100, 10_000, Side::Buy).is_ok());

        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let _sr = pool.swap(spec, token_a());

        // Fee on base side
        assert!(pool.accumulated_fees_base().get() > 0);
        assert_eq!(pool.accumulated_fees_quote().get(), 0);
    }

    #[test]
    fn collect_fees_resets_accumulators() {
        let mut pool = make_pool(fee());
        assert!(pool.place_limit_order(100, 10_000, Side::Buy).is_ok());

        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let _ = pool.swap(spec, token_a());

        let Ok(lower) = crate::domain::Tick::new(0) else {
            panic!("valid tick");
        };
        let Ok(upper) = crate::domain::Tick::new(1) else {
            panic!("valid tick");
        };
        let Ok(pos) = Position::new(lower, upper, Liquidity::new(1)) else {
            panic!("valid position");
        };
        let Ok(fees) = pool.collect_fees(&pos) else {
            panic!("expected Ok");
        };
        assert!(fees.get() > 0);

        // After collection, accumulators reset
        assert_eq!(pool.accumulated_fees_base().get(), 0);
        assert_eq!(pool.accumulated_fees_quote().get(), 0);
    }

    // -- Spot price -----------------------------------------------------------

    #[test]
    fn spot_price_with_orders() {
        let pool = make_pool(zero_fee());
        assert!(pool.place_limit_order(100, 10, Side::Buy).is_ok());
        assert!(pool.place_limit_order(105, 10, Side::Sell).is_ok());

        let result = pool.spot_price(&token_a(), &token_b());
        assert!(result.is_ok());
        let Ok(price) = result else {
            panic!("expected Ok");
        };
        // Mid price = (100 + 105) / 2 = 102.5
        assert!((price.get() - 102.5).abs() < 0.01);
    }

    #[test]
    fn spot_price_inverted() {
        let pool = make_pool(zero_fee());
        assert!(pool.place_limit_order(100, 10, Side::Buy).is_ok());
        assert!(pool.place_limit_order(105, 10, Side::Sell).is_ok());

        let result = pool.spot_price(&token_b(), &token_a());
        assert!(result.is_ok());
        let Ok(price) = result else {
            panic!("expected Ok");
        };
        // Inverted: 1 / 102.5 ≈ 0.00976
        assert!((price.get() - 1.0 / 102.5).abs() < 0.001);
    }

    #[test]
    fn spot_price_empty_book_errors() {
        let pool = make_pool(zero_fee());
        let result = pool.spot_price(&token_a(), &token_b());
        assert!(matches!(result, Err(AmmError::InsufficientLiquidity)));
    }

    #[test]
    fn spot_price_same_token_returns_one() {
        let pool = make_pool(zero_fee());
        let result = pool.spot_price(&token_a(), &token_a());
        assert!(result.is_ok());
        let Ok(price) = result else {
            panic!("expected Ok");
        };
        assert!((price.get() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn spot_price_invalid_token() {
        let pool = make_pool(zero_fee());
        let Ok(d8) = Decimals::new(8) else {
            panic!("valid decimals");
        };
        let bad_tok = Token::new(TokenAddress::from_bytes([99u8; 32]), d8);
        let result = pool.spot_price(&bad_tok, &token_b());
        assert!(matches!(result, Err(AmmError::InvalidToken(_))));
    }

    // -- Swap with invalid token ----------------------------------------------

    #[test]
    fn swap_invalid_token_errors() {
        let mut pool = make_pool(zero_fee());
        let Ok(d8) = Decimals::new(8) else {
            panic!("valid decimals");
        };
        let bad_tok = Token::new(TokenAddress::from_bytes([99u8; 32]), d8);

        let Ok(spec) = SwapSpec::exact_in(Amount::new(100)) else {
            panic!("valid spec");
        };
        let result = pool.swap(spec, bad_tok);
        assert!(matches!(result, Err(AmmError::InvalidToken(_))));
    }

    // -- Swap buying base (quote → base) --------------------------------------

    #[test]
    fn swap_buy_base_with_quote() {
        let mut pool = make_pool(zero_fee());

        // Place sell orders (asks)
        assert!(pool.place_limit_order(100, 500, Side::Sell).is_ok());

        // Swap with token_b (quote) → buy base
        let Ok(spec) = SwapSpec::exact_in(Amount::new(500)) else {
            panic!("valid spec");
        };
        let result = pool.swap(spec, token_b());
        assert!(result.is_ok());
        let Ok(sr) = result else {
            panic!("expected Ok");
        };

        // Buying base: quantity submitted as buy order = 500
        // Output = base tokens received
        assert!(sr.amount_out().get() > 0);
    }

    // -- Tick/lot size validation ----------------------------------------------

    #[test]
    fn place_order_tick_size_validation() {
        let pool = make_pool_with_sizes(10, 1);
        // Price 15 is not a multiple of tick_size=10
        let result = pool.place_limit_order(15, 100, Side::Buy);
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    #[test]
    fn place_order_lot_size_validation() {
        let pool = make_pool_with_sizes(1, 100);
        // Quantity 50 is not a multiple of lot_size=100
        let result = pool.place_limit_order(10, 50, Side::Sell);
        assert!(matches!(result, Err(AmmError::InvalidConfiguration(_))));
    }

    #[test]
    fn place_order_zero_quantity_rejected() {
        let pool = make_pool(zero_fee());
        let result = pool.place_limit_order(100, 0, Side::Buy);
        assert!(matches!(result, Err(AmmError::InvalidQuantity(_))));
    }

    #[test]
    fn place_order_aligned_succeeds() {
        let pool = make_pool_with_sizes(10, 100);
        let result = pool.place_limit_order(100, 500, Side::Buy);
        assert!(result.is_ok());
    }

    // -- Liquidity management -------------------------------------------------

    #[test]
    fn add_liquidity_places_orders() {
        let mut pool = make_pool(zero_fee());

        // Seed the book with initial orders so best_bid/best_ask exist
        assert!(pool.place_limit_order(100, 10, Side::Buy).is_ok());
        assert!(pool.place_limit_order(105, 10, Side::Sell).is_ok());

        let change = LiquidityChange::Add {
            amount_a: Amount::new(500),
            amount_b: Amount::new(300),
        };
        let result = pool.add_liquidity(&change);
        assert!(result.is_ok());
        let Ok(placed) = result else {
            panic!("expected Ok");
        };
        assert_eq!(placed.get(), 800); // 500 + 300
    }

    #[test]
    fn add_liquidity_zero_both_rejected() {
        let mut pool = make_pool(zero_fee());
        let change = LiquidityChange::Add {
            amount_a: Amount::ZERO,
            amount_b: Amount::ZERO,
        };
        let result = pool.add_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InvalidQuantity(_))));
    }

    #[test]
    fn remove_liquidity_cancels_orders() {
        let mut pool = make_pool(zero_fee());
        assert!(pool.place_limit_order(100, 500, Side::Buy).is_ok());
        assert!(pool.place_limit_order(105, 300, Side::Sell).is_ok());
        assert_eq!(pool.total_liquidity(), Liquidity::new(800));

        let change = LiquidityChange::Remove {
            liquidity: Liquidity::new(400),
        };
        let result = pool.remove_liquidity(&change);
        assert!(result.is_ok());

        // Some orders should have been cancelled
        assert!(pool.total_liquidity().get() < 800);
    }

    #[test]
    fn remove_liquidity_zero_rejected() {
        let mut pool = make_pool(zero_fee());
        let change = LiquidityChange::Remove {
            liquidity: Liquidity::ZERO,
        };
        let result = pool.remove_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InvalidLiquidity(_))));
    }

    #[test]
    fn remove_liquidity_empty_book_errors() {
        let mut pool = make_pool(zero_fee());
        let change = LiquidityChange::Remove {
            liquidity: Liquidity::new(100),
        };
        let result = pool.remove_liquidity(&change);
        assert!(matches!(result, Err(AmmError::InsufficientLiquidity)));
    }

    // -- Total liquidity tracking ---------------------------------------------

    #[test]
    fn total_liquidity_tracks_both_sides() {
        let pool = make_pool(zero_fee());
        assert!(pool.place_limit_order(100, 500, Side::Buy).is_ok());
        assert!(pool.place_limit_order(110, 300, Side::Sell).is_ok());
        assert_eq!(pool.total_liquidity(), Liquidity::new(800));
    }

    #[test]
    fn total_liquidity_after_swap() {
        let mut pool = make_pool(zero_fee());
        assert!(pool.place_limit_order(100, 500, Side::Buy).is_ok());

        let Ok(spec) = SwapSpec::exact_in(Amount::new(200)) else {
            panic!("valid spec");
        };
        let _ = pool.swap(spec, token_a());

        // After selling 200 base, bids consumed 200 → 300 remaining
        assert_eq!(pool.total_liquidity(), Liquidity::new(300));
    }

    // -- Accessors ------------------------------------------------------------

    #[test]
    fn accessors() {
        let pool = make_pool(fee());
        assert_eq!(pool.tick_size(), Amount::new(1));
        assert_eq!(pool.lot_size(), Amount::new(1));
        assert_eq!(pool.accumulated_fees_base(), Amount::ZERO);
        assert_eq!(pool.accumulated_fees_quote(), Amount::ZERO);
    }

    #[test]
    fn best_bid_ask_after_orders() {
        let pool = make_pool(zero_fee());
        assert!(pool.place_limit_order(99, 10, Side::Buy).is_ok());
        assert!(pool.place_limit_order(100, 10, Side::Buy).is_ok());
        assert!(pool.place_limit_order(105, 10, Side::Sell).is_ok());
        assert!(pool.place_limit_order(110, 10, Side::Sell).is_ok());

        assert_eq!(pool.best_bid(), Some(100));
        assert_eq!(pool.best_ask(), Some(105));
    }

    // -- Debug format ---------------------------------------------------------

    #[test]
    fn debug_format_contains_struct_name() {
        let pool = make_pool(fee());
        let dbg = format!("{pool:?}");
        assert!(dbg.contains("OrderBookPool"));
    }

    // -- Inner accessor -------------------------------------------------------

    #[test]
    fn inner_accessor_returns_book() {
        let pool = make_pool(zero_fee());
        assert_eq!(pool.inner().symbol(), "HYDRA");
    }

    // -- Multiple swaps -------------------------------------------------------

    #[test]
    fn multiple_sequential_swaps() {
        let mut pool = make_pool(zero_fee());
        assert!(pool.place_limit_order(100, 1000, Side::Buy).is_ok());

        // First swap: sell 200 base
        let Ok(spec1) = SwapSpec::exact_in(Amount::new(200)) else {
            panic!("valid spec");
        };
        let r1 = pool.swap(spec1, token_a());
        assert!(r1.is_ok());

        // Second swap: sell 300 base
        let Ok(spec2) = SwapSpec::exact_in(Amount::new(300)) else {
            panic!("valid spec");
        };
        let r2 = pool.swap(spec2, token_a());
        assert!(r2.is_ok());

        // Remaining: 1000 - 200 - 300 = 500
        let (buy_p, _) = pool.inner.buy_sell_pressure();
        assert_eq!(buy_p, 500);
    }

    // -- Swap with fee on quote side ------------------------------------------

    #[test]
    fn swap_quote_side_fee_tracked() {
        let mut pool = make_pool(fee());
        assert!(pool.place_limit_order(100, 10_000, Side::Sell).is_ok());

        // Swap with quote token (buy base)
        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let result = pool.swap(spec, token_b());
        assert!(result.is_ok());

        // Fee should be on quote side
        assert_eq!(pool.accumulated_fees_base().get(), 0);
        assert!(pool.accumulated_fees_quote().get() > 0);
    }
}
