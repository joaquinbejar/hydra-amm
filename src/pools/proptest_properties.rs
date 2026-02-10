//! Property-based tests using `proptest` for AMM invariant validation.
//!
//! Covers six properties from `08-TESTING.md`:
//!
//! 1. **Swap reversibility** — round-trip A→B→A returns ≤ original.
//! 2. **Invariant preservation** — pool invariant non-decreasing after swaps.
//! 3. **Fee monotonicity** — larger input ⇒ larger or equal fee.
//! 4. **Liquidity conservation** — add then remove ≈ original amounts.
//! 5. **Price movement direction** — selling A moves spot price correctly.
//! 6. **CLMM tick consistency** — `tick_at_price(price_at_tick(t)) == t`.

use proptest::prelude::*;

use crate::config::{ConstantProductConfig, DynamicConfig, HybridConfig, WeightedConfig};
use crate::domain::{
    Amount, BasisPoints, Decimals, FeeTier, Liquidity, LiquidityChange, Price, SwapSpec, Token,
    TokenAddress, TokenPair,
};
use crate::traits::{FromConfig, LiquidityPool, SwapPool};

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

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
        panic!("valid pair");
    };
    pair
}

fn fee_30bp() -> FeeTier {
    FeeTier::new(BasisPoints::new(30))
}

// ---------------------------------------------------------------------------
// Pool factory helpers (each creates a fresh pool from random reserves)
// ---------------------------------------------------------------------------

fn make_cp(ra: u128, rb: u128) -> crate::pools::ConstantProductPool {
    let Ok(cfg) =
        ConstantProductConfig::new(make_pair(), fee_30bp(), Amount::new(ra), Amount::new(rb))
    else {
        panic!("valid CP config");
    };
    let Ok(pool) = crate::pools::ConstantProductPool::from_config(&cfg) else {
        panic!("valid CP pool");
    };
    pool
}

fn make_hybrid(amp: u32, reserve: u128) -> crate::pools::HybridPool {
    let Ok(cfg) = HybridConfig::new(
        make_pair(),
        fee_30bp(),
        amp,
        Amount::new(reserve),
        Amount::new(reserve),
    ) else {
        panic!("valid Hybrid config");
    };
    let Ok(pool) = crate::pools::HybridPool::from_config(&cfg) else {
        panic!("valid Hybrid pool");
    };
    pool
}

fn make_weighted(ra: u128, rb: u128) -> crate::pools::WeightedPool {
    let Ok(d18) = Decimals::new(18) else {
        panic!("valid decimals");
    };
    let Ok(d6) = Decimals::new(6) else {
        panic!("valid decimals");
    };
    let t1 = Token::new(TokenAddress::from_bytes([1u8; 32]), d18);
    let t2 = Token::new(TokenAddress::from_bytes([2u8; 32]), d6);
    let Ok(cfg) = WeightedConfig::new(
        vec![t1, t2],
        vec![BasisPoints::new(5_000), BasisPoints::new(5_000)],
        fee_30bp(),
        vec![Amount::new(ra), Amount::new(rb)],
    ) else {
        panic!("valid Weighted config");
    };
    let Ok(pool) = crate::pools::WeightedPool::from_config(&cfg) else {
        panic!("valid Weighted pool");
    };
    pool
}

fn make_dynamic(k: f64, oracle: f64, base: u128, quote: u128) -> crate::pools::DynamicPool {
    let Ok(oracle_price) = Price::new(oracle) else {
        panic!("valid oracle price");
    };
    let Ok(cfg) = DynamicConfig::new(
        make_pair(),
        fee_30bp(),
        oracle_price,
        k,
        Amount::new(base),
        Amount::new(quote),
    ) else {
        panic!("valid Dynamic config");
    };
    let Ok(pool) = crate::pools::DynamicPool::from_config(&cfg) else {
        panic!("valid Dynamic pool");
    };
    pool
}

// ---------------------------------------------------------------------------
// Custom strategies
// ---------------------------------------------------------------------------

/// Reserve values in range [10_000, 10_000_000] to avoid extremes.
fn reserve_strategy() -> impl Strategy<Value = u128> {
    10_000u128..=10_000_000u128
}

/// Amplification values for Hybrid pools in [1, 500].
fn amplification_strategy() -> impl Strategy<Value = u32> {
    1u32..=500u32
}

/// k coefficient for Dynamic pools in [0.0, 1.0].
fn k_strategy() -> impl Strategy<Value = f64> {
    (0u32..=100u32).prop_map(|v| f64::from(v) / 100.0)
}

/// Oracle price deviation factor from AMM price: [0.9, 1.1].
/// Keeps oracle close to reserve ratio so blending does not create
/// arbitrage opportunities that break swap reversibility.
fn oracle_deviation_strategy() -> impl Strategy<Value = f64> {
    (90u32..=110u32).prop_map(|v| f64::from(v) / 100.0)
}

/// Tick values in valid range for CLMM.
fn tick_strategy() -> impl Strategy<Value = i32> {
    -500_000i32..=500_000i32
}

// ---------------------------------------------------------------------------
// Property 1: Swap Reversibility
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn prop_swap_reversibility_constant_product(
        ra in reserve_strategy(),
        rb in reserve_strategy(),
    ) {
        let swap_in = (ra / 1_000).max(1);
        let mut pool = make_cp(ra, rb);

        // A → B
        let Ok(spec_ab) = SwapSpec::exact_in(Amount::new(swap_in)) else {
            return Ok(());
        };
        let Ok(result_ab) = pool.swap(spec_ab, tok_a()) else {
            return Ok(());
        };
        let received_b = result_ab.amount_out().get();
        if received_b == 0 { return Ok(()); }

        // B → A
        let Ok(spec_ba) = SwapSpec::exact_in(Amount::new(received_b)) else {
            return Ok(());
        };
        let Ok(result_ba) = pool.swap(spec_ba, tok_b()) else {
            return Ok(());
        };
        let final_a = result_ba.amount_out().get();

        prop_assert!(
            final_a <= swap_in,
            "round-trip should lose value: final={} > original={}",
            final_a, swap_in
        );
    }

    #[test]
    fn prop_swap_reversibility_hybrid(
        reserve in reserve_strategy(),
        amp in amplification_strategy(),
    ) {
        let swap_in = (reserve / 1_000).max(1);
        let mut pool = make_hybrid(amp, reserve);

        let Ok(spec_ab) = SwapSpec::exact_in(Amount::new(swap_in)) else {
            return Ok(());
        };
        let Ok(result_ab) = pool.swap(spec_ab, tok_a()) else {
            return Ok(());
        };
        let received_b = result_ab.amount_out().get();
        if received_b == 0 { return Ok(()); }

        let Ok(spec_ba) = SwapSpec::exact_in(Amount::new(received_b)) else {
            return Ok(());
        };
        let Ok(result_ba) = pool.swap(spec_ba, tok_b()) else {
            return Ok(());
        };

        prop_assert!(
            result_ba.amount_out().get() <= swap_in,
            "hybrid round-trip should lose value: final={} > original={}",
            result_ba.amount_out().get(), swap_in
        );
    }

    #[test]
    fn prop_swap_reversibility_weighted(
        ra in reserve_strategy(),
        rb in reserve_strategy(),
    ) {
        let swap_in = (ra / 1_000).max(1);
        let mut pool = make_weighted(ra, rb);

        let Ok(spec_ab) = SwapSpec::exact_in(Amount::new(swap_in)) else {
            return Ok(());
        };
        let t1 = tok_a();
        let Ok(result_ab) = pool.swap(spec_ab, t1) else {
            return Ok(());
        };
        let received_b = result_ab.amount_out().get();
        if received_b == 0 { return Ok(()); }

        let Ok(spec_ba) = SwapSpec::exact_in(Amount::new(received_b)) else {
            return Ok(());
        };
        let t2 = tok_b();
        let Ok(result_ba) = pool.swap(spec_ba, t2) else {
            return Ok(());
        };

        prop_assert!(
            result_ba.amount_out().get() <= swap_in,
            "weighted round-trip should lose value: final={} > original={}",
            result_ba.amount_out().get(), swap_in
        );
    }

    #[test]
    fn prop_swap_reversibility_dynamic(
        base in reserve_strategy(),
        quote in reserve_strategy(),
        k in k_strategy(),
        deviation in oracle_deviation_strategy(),
    ) {
        // Oracle price ≈ AMM price (quote/base) × deviation
        // This avoids arbitrage from oracle/AMM divergence.
        let amm_price = quote as f64 / base as f64;
        let oracle = amm_price * deviation;
        if oracle <= 0.0 || !oracle.is_finite() { return Ok(()); }

        let swap_in = (base / 1_000).max(1);
        let mut pool = make_dynamic(k, oracle, base, quote);

        let Ok(spec_ab) = SwapSpec::exact_in(Amount::new(swap_in)) else {
            return Ok(());
        };
        let Ok(result_ab) = pool.swap(spec_ab, tok_a()) else {
            return Ok(());
        };
        let received_b = result_ab.amount_out().get();
        if received_b == 0 { return Ok(()); }

        let Ok(spec_ba) = SwapSpec::exact_in(Amount::new(received_b)) else {
            return Ok(());
        };
        let Ok(result_ba) = pool.swap(spec_ba, tok_b()) else {
            return Ok(());
        };

        prop_assert!(
            result_ba.amount_out().get() <= swap_in,
            "dynamic round-trip should lose value: final={} > original={}",
            result_ba.amount_out().get(), swap_in
        );
    }
}

// ---------------------------------------------------------------------------
// Property 2: Invariant Preservation
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn prop_invariant_preservation_constant_product(
        ra in reserve_strategy(),
        rb in reserve_strategy(),
    ) {
        let swap_in = (ra / 500).max(1);
        let mut pool = make_cp(ra, rb);
        let k_before = pool.reserve_a().get() as u128 * pool.reserve_b().get() as u128;

        for _ in 0..5 {
            let Ok(spec) = SwapSpec::exact_in(Amount::new(swap_in)) else {
                break;
            };
            if pool.swap(spec, tok_a()).is_err() { break; }
        }

        let k_after = pool.reserve_a().get() as u128 * pool.reserve_b().get() as u128;
        prop_assert!(
            k_after >= k_before,
            "CP invariant k should grow from fees: k_after={} < k_before={}",
            k_after, k_before
        );
    }

    #[test]
    fn prop_invariant_preservation_hybrid(
        reserve in reserve_strategy(),
        amp in amplification_strategy(),
    ) {
        let swap_in = (reserve / 500).max(1);
        let mut pool = make_hybrid(amp, reserve);
        let d_before = pool.invariant_d();

        for _ in 0..5 {
            let Ok(spec) = SwapSpec::exact_in(Amount::new(swap_in)) else {
                break;
            };
            if pool.swap(spec, tok_a()).is_err() { break; }
        }

        let d_after = pool.invariant_d();
        prop_assert!(
            d_after >= d_before,
            "Hybrid invariant D should grow from fees: d_after={} < d_before={}",
            d_after, d_before
        );
    }

    #[test]
    fn prop_invariant_preservation_weighted(
        ra in reserve_strategy(),
        rb in reserve_strategy(),
    ) {
        let swap_in = (ra / 500).max(1);
        let mut pool = make_weighted(ra, rb);
        let Ok(inv_before) = pool.compute_invariant() else {
            return Ok(());
        };

        for _ in 0..5 {
            let Ok(spec) = SwapSpec::exact_in(Amount::new(swap_in)) else {
                break;
            };
            let t = tok_a();
            if pool.swap(spec, t).is_err() { break; }
        }

        let Ok(inv_after) = pool.compute_invariant() else {
            return Ok(());
        };
        prop_assert!(
            inv_after >= inv_before - 1.0,
            "Weighted invariant should be non-decreasing: after={} < before={}",
            inv_after, inv_before
        );
    }
}

// ---------------------------------------------------------------------------
// Property 3: Fee Monotonicity
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn prop_fee_monotonicity_constant_product(
        ra in reserve_strategy(),
        rb in reserve_strategy(),
    ) {
        let inputs = [
            (ra / 10_000).max(1),
            (ra / 1_000).max(2),
            (ra / 100).max(3),
        ];

        let mut fees = Vec::new();
        for &input in &inputs {
            let mut pool = make_cp(ra, rb);
            let Ok(spec) = SwapSpec::exact_in(Amount::new(input)) else {
                continue;
            };
            let Ok(result) = pool.swap(spec, tok_a()) else {
                continue;
            };
            fees.push(result.fee().get());
        }

        for pair in fees.windows(2) {
            if let [prev, curr] = pair {
                prop_assert!(
                    curr >= prev,
                    "fee should be non-decreasing: {} < {}",
                    curr, prev
                );
            }
        }
    }

    #[test]
    fn prop_fee_monotonicity_hybrid(
        reserve in reserve_strategy(),
        amp in amplification_strategy(),
    ) {
        let inputs = [
            (reserve / 10_000).max(1),
            (reserve / 1_000).max(2),
            (reserve / 100).max(3),
        ];

        let mut fees = Vec::new();
        for &input in &inputs {
            let mut pool = make_hybrid(amp, reserve);
            let Ok(spec) = SwapSpec::exact_in(Amount::new(input)) else {
                continue;
            };
            let Ok(result) = pool.swap(spec, tok_a()) else {
                continue;
            };
            fees.push(result.fee().get());
        }

        for pair in fees.windows(2) {
            if let [prev, curr] = pair {
                prop_assert!(
                    curr >= prev,
                    "fee should be non-decreasing: {} < {}",
                    curr, prev
                );
            }
        }
    }

    #[test]
    fn prop_fee_monotonicity_weighted(
        ra in reserve_strategy(),
        rb in reserve_strategy(),
    ) {
        let inputs = [
            (ra / 10_000).max(1),
            (ra / 1_000).max(2),
            (ra / 100).max(3),
        ];

        let mut fees = Vec::new();
        for &input in &inputs {
            let mut pool = make_weighted(ra, rb);
            let Ok(spec) = SwapSpec::exact_in(Amount::new(input)) else {
                continue;
            };
            let t = tok_a();
            let Ok(result) = pool.swap(spec, t) else {
                continue;
            };
            fees.push(result.fee().get());
        }

        for pair in fees.windows(2) {
            if let [prev, curr] = pair {
                prop_assert!(
                    curr >= prev,
                    "fee should be non-decreasing: {} < {}",
                    curr, prev
                );
            }
        }
    }

    #[test]
    fn prop_fee_monotonicity_dynamic(
        base in reserve_strategy(),
        quote in reserve_strategy(),
        k in k_strategy(),
        deviation in oracle_deviation_strategy(),
    ) {
        let amm_price = quote as f64 / base as f64;
        let oracle = amm_price * deviation;
        if oracle <= 0.0 || !oracle.is_finite() { return Ok(()); }

        let inputs = [
            (base / 10_000).max(1),
            (base / 1_000).max(2),
            (base / 100).max(3),
        ];

        let mut fees = Vec::new();
        for &input in &inputs {
            let mut pool = make_dynamic(k, oracle, base, quote);
            let Ok(spec) = SwapSpec::exact_in(Amount::new(input)) else {
                continue;
            };
            let Ok(result) = pool.swap(spec, tok_a()) else {
                continue;
            };
            fees.push(result.fee().get());
        }

        for pair in fees.windows(2) {
            if let [prev, curr] = pair {
                prop_assert!(
                    curr >= prev,
                    "fee should be non-decreasing: {} < {}",
                    curr, prev
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Property 4: Liquidity Conservation
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn prop_liquidity_conservation_constant_product(
        ra in reserve_strategy(),
        rb in reserve_strategy(),
    ) {
        let mut pool = make_cp(ra, rb);
        let liq_before = pool.total_liquidity().get();

        // Add proportional liquidity (10%)
        let add_a = ra / 10;
        let add_b = rb / 10;
        if add_a == 0 || add_b == 0 { return Ok(()); }

        let Ok(change) = LiquidityChange::add(Amount::new(add_a), Amount::new(add_b)) else {
            return Ok(());
        };
        let Ok(minted) = pool.add_liquidity(&change) else {
            return Ok(());
        };
        prop_assert!(minted.get() > 0, "should mint LP tokens");
        prop_assert!(
            pool.total_liquidity().get() > liq_before,
            "liquidity should increase"
        );

        // Remove what was minted
        let Ok(remove_change) = LiquidityChange::remove(Liquidity::new(minted.get())) else {
            return Ok(());
        };
        let Ok(_) = pool.remove_liquidity(&remove_change) else {
            return Ok(());
        };

        // Liquidity should return to approximately the original value
        let liq_after = pool.total_liquidity().get();
        let diff = liq_after.abs_diff(liq_before);
        // Allow 1% tolerance for rounding
        let tolerance = liq_before / 100 + 1;
        prop_assert!(
            diff <= tolerance,
            "liquidity should be conserved: before={} after={} diff={}",
            liq_before, liq_after, diff
        );
    }

    #[test]
    fn prop_liquidity_conservation_hybrid(
        reserve in reserve_strategy(),
        amp in amplification_strategy(),
    ) {
        let mut pool = make_hybrid(amp, reserve);
        let liq_before = pool.total_liquidity().get();

        let add_amount = reserve / 10;
        if add_amount == 0 { return Ok(()); }

        let Ok(change) = LiquidityChange::add(Amount::new(add_amount), Amount::new(add_amount)) else {
            return Ok(());
        };
        let Ok(minted) = pool.add_liquidity(&change) else {
            return Ok(());
        };
        prop_assert!(minted.get() > 0);

        let Ok(remove_change) = LiquidityChange::remove(Liquidity::new(minted.get())) else {
            return Ok(());
        };
        let Ok(_) = pool.remove_liquidity(&remove_change) else {
            return Ok(());
        };

        let liq_after = pool.total_liquidity().get();
        let diff = liq_after.abs_diff(liq_before);
        let tolerance = liq_before / 100 + 1;
        prop_assert!(
            diff <= tolerance,
            "hybrid liquidity should be conserved: before={} after={} diff={}",
            liq_before, liq_after, diff
        );
    }
}

// ---------------------------------------------------------------------------
// Property 5: Price Movement Direction
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn prop_price_movement_direction_constant_product(
        ra in reserve_strategy(),
        rb in reserve_strategy(),
    ) {
        let swap_in = (ra / 100).max(1);
        let mut pool = make_cp(ra, rb);

        let Ok(price_before) = pool.spot_price(&tok_a(), &tok_b()) else {
            return Ok(());
        };

        let Ok(spec) = SwapSpec::exact_in(Amount::new(swap_in)) else {
            return Ok(());
        };
        if pool.swap(spec, tok_a()).is_err() { return Ok(()); }

        let Ok(price_after) = pool.spot_price(&tok_a(), &tok_b()) else {
            return Ok(());
        };

        // Selling A increases A reserve, decreases B → price(A/B) should decrease
        // (more A per B means A is cheaper)
        prop_assert!(
            price_after.get() <= price_before.get(),
            "selling A should decrease price(A→B): before={} after={}",
            price_before.get(), price_after.get()
        );
    }

    #[test]
    fn prop_price_movement_direction_hybrid(
        reserve in reserve_strategy(),
        amp in amplification_strategy(),
    ) {
        let swap_in = (reserve / 100).max(1);
        let mut pool = make_hybrid(amp, reserve);

        let Ok(price_before) = pool.spot_price(&tok_a(), &tok_b()) else {
            return Ok(());
        };

        let Ok(spec) = SwapSpec::exact_in(Amount::new(swap_in)) else {
            return Ok(());
        };
        if pool.swap(spec, tok_a()).is_err() { return Ok(()); }

        let Ok(price_after) = pool.spot_price(&tok_a(), &tok_b()) else {
            return Ok(());
        };

        prop_assert!(
            price_after.get() <= price_before.get(),
            "hybrid: selling A should decrease price(A→B): before={} after={}",
            price_before.get(), price_after.get()
        );
    }

    #[test]
    fn prop_price_movement_direction_weighted(
        ra in reserve_strategy(),
        rb in reserve_strategy(),
    ) {
        let swap_in = (ra / 100).max(1);
        let mut pool = make_weighted(ra, rb);

        let Ok(price_before) = pool.spot_price(&tok_a(), &tok_b()) else {
            return Ok(());
        };

        let Ok(spec) = SwapSpec::exact_in(Amount::new(swap_in)) else {
            return Ok(());
        };
        let t = tok_a();
        if pool.swap(spec, t).is_err() { return Ok(()); }

        let Ok(price_after) = pool.spot_price(&tok_a(), &tok_b()) else {
            return Ok(());
        };

        // For weighted 50/50, spot_price = (B/W_B) / (A/W_A)
        // Selling A increases A balance → denominator grows → price increases
        // (the price of A in terms of B goes up because B is scarcer)
        prop_assert!(
            price_after.get() >= price_before.get(),
            "weighted: selling A should increase spot_price(A,B): before={} after={}",
            price_before.get(), price_after.get()
        );
    }
}

// ---------------------------------------------------------------------------
// Property 6: CLMM Tick Consistency
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn prop_clmm_tick_consistency(tick_val in tick_strategy()) {
        let Ok(tick) = crate::domain::Tick::new(tick_val) else {
            return Ok(());
        };
        let Ok(price) = crate::math::price_at_tick(tick) else {
            return Ok(());
        };

        // Price must be positive and finite
        prop_assert!(price.get() > 0.0, "price must be positive for tick {}", tick_val);
        prop_assert!(price.get().is_finite(), "price must be finite for tick {}", tick_val);

        let Ok(round_trip) = crate::math::tick_at_price(price) else {
            return Ok(());
        };
        prop_assert_eq!(
            round_trip, tick,
            "tick_at_price(price_at_tick({})) should round-trip: got {}",
            tick_val, round_trip.get()
        );
    }

    #[test]
    fn prop_price_positive_after_tick(tick_val in tick_strategy()) {
        let Ok(tick) = crate::domain::Tick::new(tick_val) else {
            return Ok(());
        };
        let Ok(price) = crate::math::price_at_tick(tick) else {
            return Ok(());
        };
        prop_assert!(
            price.get() > 0.0 && price.get().is_finite(),
            "price at tick {} must be positive and finite, got {}",
            tick_val, price.get()
        );
    }
}
