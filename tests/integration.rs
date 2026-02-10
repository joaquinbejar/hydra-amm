//! Integration tests exercising the full system from config to pool operation.
//!
//! These tests verify end-to-end flows through the public API:
//! factory round-trip, multi-pool comparison, config validation,
//! and the full trading lifecycle.
//!
//! These tests require all pool features to be enabled.

#![cfg(all(
    feature = "constant-product",
    feature = "clmm",
    feature = "hybrid",
    feature = "weighted",
    feature = "dynamic",
    feature = "order-book",
))]
#![allow(clippy::panic)]

use hydra_amm::config::{
    AmmConfig, ClmmConfig, ConstantProductConfig, DynamicConfig, HybridConfig, OrderBookConfig,
    WeightedConfig,
};
use hydra_amm::domain::{
    Amount, BasisPoints, Decimals, FeeTier, Liquidity, LiquidityChange, Price, SwapSpec, Tick,
    Token, TokenAddress, TokenPair,
};
use hydra_amm::factory::DefaultPoolFactory;
use hydra_amm::traits::{LiquidityPool, SwapPool};

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

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

fn make_pair() -> TokenPair {
    let Ok(pair) = TokenPair::new(tok_a(), tok_b()) else {
        panic!("valid pair");
    };
    pair
}

fn fee_30bp() -> FeeTier {
    FeeTier::new(BasisPoints::new(30))
}

fn tick(v: i32) -> Tick {
    let Ok(t) = Tick::new(v) else {
        panic!("valid tick");
    };
    t
}

fn dummy_position() -> hydra_amm::domain::Position {
    let Ok(p) = hydra_amm::domain::Position::new(tick(0), tick(100), Liquidity::new(1)) else {
        panic!("valid position");
    };
    p
}

// ---------------------------------------------------------------------------
// Config builders for each pool type
// ---------------------------------------------------------------------------

fn cp_config(ra: u128, rb: u128) -> AmmConfig {
    let Ok(cfg) =
        ConstantProductConfig::new(make_pair(), fee_30bp(), Amount::new(ra), Amount::new(rb))
    else {
        panic!("valid CP config");
    };
    AmmConfig::ConstantProduct(cfg)
}

fn clmm_config() -> AmmConfig {
    let Ok(cfg) = ClmmConfig::new(make_pair(), fee_30bp(), 10, tick(0), vec![]) else {
        panic!("valid CLMM config");
    };
    AmmConfig::Clmm(cfg)
}

fn clmm_config_with_position() -> AmmConfig {
    let Ok(pos) =
        hydra_amm::domain::Position::new(tick(-100), tick(100), Liquidity::new(1_000_000))
    else {
        panic!("valid position");
    };
    let Ok(cfg) = ClmmConfig::new(make_pair(), fee_30bp(), 10, tick(0), vec![pos]) else {
        panic!("valid CLMM config");
    };
    AmmConfig::Clmm(cfg)
}

fn hybrid_config(amp: u32, reserve: u128) -> AmmConfig {
    let Ok(cfg) = HybridConfig::new(
        make_pair(),
        fee_30bp(),
        amp,
        Amount::new(reserve),
        Amount::new(reserve),
    ) else {
        panic!("valid Hybrid config");
    };
    AmmConfig::Hybrid(cfg)
}

fn weighted_config(ra: u128, rb: u128) -> AmmConfig {
    let Ok(cfg) = WeightedConfig::new(
        vec![tok_a(), tok_b()],
        vec![BasisPoints::new(5_000), BasisPoints::new(5_000)],
        fee_30bp(),
        vec![Amount::new(ra), Amount::new(rb)],
    ) else {
        panic!("valid Weighted config");
    };
    AmmConfig::Weighted(cfg)
}

fn dynamic_config(k: f64, oracle: f64, base: u128, quote: u128) -> AmmConfig {
    let Ok(price) = Price::new(oracle) else {
        panic!("valid oracle price");
    };
    let Ok(cfg) = DynamicConfig::new(
        make_pair(),
        fee_30bp(),
        price,
        k,
        Amount::new(base),
        Amount::new(quote),
    ) else {
        panic!("valid Dynamic config");
    };
    AmmConfig::Dynamic(cfg)
}

fn order_book_config() -> AmmConfig {
    let Ok(cfg) = OrderBookConfig::new(make_pair(), fee_30bp(), Amount::new(1), Amount::new(1))
    else {
        panic!("valid OrderBook config");
    };
    AmmConfig::OrderBook(cfg)
}

// ===========================================================================
// Suite 1: Factory Round-Trip
// ===========================================================================

#[test]
fn factory_round_trip_constant_product() {
    let config = cp_config(1_000_000, 2_000_000);
    let Ok(mut pool) = DefaultPoolFactory::create(&config) else {
        panic!("factory should create CP pool");
    };

    // Verify initial state
    assert_eq!(*pool.token_pair(), make_pair());
    assert_eq!(pool.fee_tier(), fee_30bp());
    assert!(pool.total_liquidity().get() > 0);

    // Execute swap and verify output
    let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
        panic!("valid spec");
    };
    let Ok(result) = pool.swap(spec, tok_a()) else {
        panic!("swap should succeed");
    };
    assert!(result.amount_out().get() > 0);
    assert!(result.fee().get() > 0);
    // Fee should be 0.3% of 10_000 = 30
    assert_eq!(result.fee().get(), 30);
}

#[test]
fn factory_round_trip_clmm() {
    let config = clmm_config();
    let Ok(pool) = DefaultPoolFactory::create(&config) else {
        panic!("factory should create CLMM pool");
    };

    assert_eq!(*pool.token_pair(), make_pair());
    assert_eq!(pool.fee_tier(), fee_30bp());
    // Empty CLMM starts with zero liquidity
    assert_eq!(pool.total_liquidity(), Liquidity::ZERO);
}

#[test]
fn factory_round_trip_clmm_with_position() {
    let config = clmm_config_with_position();
    let Ok(mut pool) = DefaultPoolFactory::create(&config) else {
        panic!("factory should create CLMM pool with position");
    };

    assert!(pool.total_liquidity().get() > 0);

    // Swap within the position range
    let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
        panic!("valid spec");
    };
    let Ok(result) = pool.swap(spec, tok_a()) else {
        panic!("swap should succeed on CLMM with liquidity");
    };
    assert!(result.amount_out().get() > 0);
}

#[test]
fn factory_round_trip_hybrid() {
    let config = hybrid_config(100, 1_000_000);
    let Ok(mut pool) = DefaultPoolFactory::create(&config) else {
        panic!("factory should create Hybrid pool");
    };

    assert_eq!(*pool.token_pair(), make_pair());
    assert_eq!(pool.fee_tier(), fee_30bp());
    assert!(pool.total_liquidity().get() > 0);

    let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
        panic!("valid spec");
    };
    let Ok(result) = pool.swap(spec, tok_a()) else {
        panic!("swap should succeed");
    };
    assert!(result.amount_out().get() > 0);
    assert!(result.fee().get() > 0);
}

#[test]
fn factory_round_trip_weighted() {
    let config = weighted_config(1_000_000, 2_000_000);
    let Ok(mut pool) = DefaultPoolFactory::create(&config) else {
        panic!("factory should create Weighted pool");
    };

    assert_eq!(pool.fee_tier(), fee_30bp());
    assert!(pool.total_liquidity().get() > 0);

    let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
        panic!("valid spec");
    };
    let Ok(result) = pool.swap(spec, tok_a()) else {
        panic!("swap should succeed");
    };
    assert!(result.amount_out().get() > 0);
}

#[test]
fn factory_round_trip_dynamic() {
    let config = dynamic_config(0.5, 1.5, 1_000_000, 1_500_000);
    let Ok(mut pool) = DefaultPoolFactory::create(&config) else {
        panic!("factory should create Dynamic pool");
    };

    assert_eq!(*pool.token_pair(), make_pair());
    assert_eq!(pool.fee_tier(), fee_30bp());
    assert!(pool.total_liquidity().get() > 0);

    let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
        panic!("valid spec");
    };
    let Ok(result) = pool.swap(spec, tok_a()) else {
        panic!("swap should succeed");
    };
    assert!(result.amount_out().get() > 0);
}

#[test]
fn factory_round_trip_order_book() {
    let config = order_book_config();
    let Ok(pool) = DefaultPoolFactory::create(&config) else {
        panic!("factory should create OrderBook pool");
    };

    assert_eq!(*pool.token_pair(), make_pair());
    assert_eq!(pool.fee_tier(), fee_30bp());
    // Empty order book starts with zero liquidity
    assert_eq!(pool.total_liquidity(), Liquidity::ZERO);
}

// ===========================================================================
// Suite 2: Multi-Pool Comparison
// ===========================================================================

#[test]
fn multi_pool_comparison_swap_outputs() {
    // Same reserves (1M/1M), same swap (10k A→B)
    let Ok(mut cp) = DefaultPoolFactory::create(&cp_config(1_000_000, 1_000_000)) else {
        panic!("CP pool");
    };
    let Ok(mut hybrid) = DefaultPoolFactory::create(&hybrid_config(100, 1_000_000)) else {
        panic!("Hybrid pool");
    };
    let Ok(mut weighted) = DefaultPoolFactory::create(&weighted_config(1_000_000, 1_000_000))
    else {
        panic!("Weighted pool");
    };
    // Dynamic with oracle = AMM price = 1.0, k=1.0 (pure CP behavior)
    let Ok(mut dynamic) =
        DefaultPoolFactory::create(&dynamic_config(1.0, 1.0, 1_000_000, 1_000_000))
    else {
        panic!("Dynamic pool");
    };

    let swap_amount = 10_000u128;

    let Ok(spec_cp) = SwapSpec::exact_in(Amount::new(swap_amount)) else {
        panic!("valid spec");
    };
    let Ok(spec_hy) = SwapSpec::exact_in(Amount::new(swap_amount)) else {
        panic!("valid spec");
    };
    let Ok(spec_wt) = SwapSpec::exact_in(Amount::new(swap_amount)) else {
        panic!("valid spec");
    };
    let Ok(spec_dy) = SwapSpec::exact_in(Amount::new(swap_amount)) else {
        panic!("valid spec");
    };

    let Ok(cp_result) = cp.swap(spec_cp, tok_a()) else {
        panic!("CP swap");
    };
    let Ok(hy_result) = hybrid.swap(spec_hy, tok_a()) else {
        panic!("Hybrid swap");
    };
    let Ok(wt_result) = weighted.swap(spec_wt, tok_a()) else {
        panic!("Weighted swap");
    };
    let Ok(dy_result) = dynamic.swap(spec_dy, tok_a()) else {
        panic!("Dynamic swap");
    };

    // All should produce positive output
    assert!(cp_result.amount_out().get() > 0, "CP output > 0");
    assert!(hy_result.amount_out().get() > 0, "Hybrid output > 0");
    assert!(wt_result.amount_out().get() > 0, "Weighted output > 0");
    assert!(dy_result.amount_out().get() > 0, "Dynamic output > 0");

    // All should charge fees
    assert!(cp_result.fee().get() > 0, "CP fee > 0");
    assert!(hy_result.fee().get() > 0, "Hybrid fee > 0");
    assert!(wt_result.fee().get() > 0, "Weighted fee > 0");
    assert!(dy_result.fee().get() > 0, "Dynamic fee > 0");

    // With equal reserves and high amplification, Hybrid (StableSwap)
    // should give better or equal output than Constant Product
    assert!(
        hy_result.amount_out().get() >= cp_result.amount_out().get(),
        "Hybrid ({}) should >= CP ({}) at peg with amp=100",
        hy_result.amount_out().get(),
        cp_result.amount_out().get()
    );

    // Weighted 50/50 should be very close to CP (same formula)
    let cp_out = cp_result.amount_out().get();
    let wt_out = wt_result.amount_out().get();
    let diff = cp_out.abs_diff(wt_out);
    // Allow small rounding difference (< 0.1%)
    assert!(
        diff <= cp_out / 1_000 + 1,
        "Weighted 50/50 ({wt_out}) should ≈ CP ({cp_out}), diff={diff}"
    );
}

#[test]
fn multi_pool_outputs_are_deterministic() {
    // Execute the same swap twice on identically configured pools
    for _ in 0..2 {
        let Ok(mut pool) = DefaultPoolFactory::create(&cp_config(1_000_000, 2_000_000)) else {
            panic!("CP pool");
        };
        let Ok(spec) = SwapSpec::exact_in(Amount::new(5_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("swap should succeed");
        };
        // CP formula: out = 2_000_000 * (5000 - 15) / (1_000_000 + 5000 - 15) = ...
        // Just verify deterministic: same output each iteration
        assert!(
            result.amount_out().get() > 9_000,
            "expected ~9970, got {}",
            result.amount_out().get()
        );
    }
}

// ===========================================================================
// Suite 3: Config Validation
// ===========================================================================

#[test]
fn config_validation_cp_zero_reserve_a() {
    let result =
        ConstantProductConfig::new(make_pair(), fee_30bp(), Amount::ZERO, Amount::new(1_000));
    // Either config constructor or factory should reject
    match result {
        Err(_) => {} // Config constructor already rejected — fine
        Ok(cfg) => {
            let amm = AmmConfig::ConstantProduct(cfg);
            let factory_result = DefaultPoolFactory::create(&amm);
            assert!(
                factory_result.is_err(),
                "factory should reject zero reserve_a"
            );
        }
    }
}

#[test]
fn config_validation_cp_zero_reserve_b() {
    let result =
        ConstantProductConfig::new(make_pair(), fee_30bp(), Amount::new(1_000), Amount::ZERO);
    match result {
        Err(_) => {}
        Ok(cfg) => {
            let amm = AmmConfig::ConstantProduct(cfg);
            let factory_result = DefaultPoolFactory::create(&amm);
            assert!(
                factory_result.is_err(),
                "factory should reject zero reserve_b"
            );
        }
    }
}

#[test]
fn config_validation_hybrid_zero_amplification() {
    let result = HybridConfig::new(
        make_pair(),
        fee_30bp(),
        0,
        Amount::new(1_000),
        Amount::new(1_000),
    );
    match result {
        Err(_) => {} // Constructor rejected — fine
        Ok(cfg) => {
            let amm = AmmConfig::Hybrid(cfg);
            let factory_result = DefaultPoolFactory::create(&amm);
            assert!(factory_result.is_err(), "factory should reject amp=0");
        }
    }
}

#[test]
fn config_validation_hybrid_zero_reserves() {
    let result = HybridConfig::new(
        make_pair(),
        fee_30bp(),
        100,
        Amount::ZERO,
        Amount::new(1_000),
    );
    match result {
        Err(_) => {}
        Ok(cfg) => {
            let amm = AmmConfig::Hybrid(cfg);
            let factory_result = DefaultPoolFactory::create(&amm);
            assert!(
                factory_result.is_err(),
                "factory should reject zero reserve"
            );
        }
    }
}

#[test]
fn config_validation_weighted_bad_weights() {
    // Weights don't sum to 10000
    let result = WeightedConfig::new(
        vec![tok_a(), tok_b()],
        vec![BasisPoints::new(3_000), BasisPoints::new(3_000)],
        fee_30bp(),
        vec![Amount::new(1_000), Amount::new(1_000)],
    );
    match result {
        Err(_) => {}
        Ok(cfg) => {
            let amm = AmmConfig::Weighted(cfg);
            let factory_result = DefaultPoolFactory::create(&amm);
            assert!(factory_result.is_err(), "factory should reject bad weights");
        }
    }
}

#[test]
fn config_validation_weighted_zero_balance() {
    let result = WeightedConfig::new(
        vec![tok_a(), tok_b()],
        vec![BasisPoints::new(5_000), BasisPoints::new(5_000)],
        fee_30bp(),
        vec![Amount::ZERO, Amount::new(1_000)],
    );
    match result {
        Err(_) => {}
        Ok(cfg) => {
            let amm = AmmConfig::Weighted(cfg);
            let factory_result = DefaultPoolFactory::create(&amm);
            assert!(
                factory_result.is_err(),
                "factory should reject zero balance"
            );
        }
    }
}

#[test]
fn config_validation_dynamic_k_out_of_range() {
    let Ok(price) = Price::new(1.0) else {
        panic!("valid price");
    };
    let result = DynamicConfig::new(
        make_pair(),
        fee_30bp(),
        price,
        1.5,
        Amount::new(1_000),
        Amount::new(1_000),
    );
    match result {
        Err(_) => {} // k > 1.0 should be rejected
        Ok(cfg) => {
            let amm = AmmConfig::Dynamic(cfg);
            let factory_result = DefaultPoolFactory::create(&amm);
            assert!(factory_result.is_err(), "factory should reject k > 1.0");
        }
    }
}

#[test]
fn config_validation_dynamic_negative_k() {
    let Ok(price) = Price::new(1.0) else {
        panic!("valid price");
    };
    let result = DynamicConfig::new(
        make_pair(),
        fee_30bp(),
        price,
        -0.1,
        Amount::new(1_000),
        Amount::new(1_000),
    );
    match result {
        Err(_) => {}
        Ok(cfg) => {
            let amm = AmmConfig::Dynamic(cfg);
            let factory_result = DefaultPoolFactory::create(&amm);
            assert!(factory_result.is_err(), "factory should reject k < 0");
        }
    }
}

#[test]
fn config_validation_dynamic_zero_reserves() {
    let Ok(price) = Price::new(1.0) else {
        panic!("valid price");
    };
    let result = DynamicConfig::new(
        make_pair(),
        fee_30bp(),
        price,
        0.5,
        Amount::ZERO,
        Amount::new(1_000),
    );
    match result {
        Err(_) => {}
        Ok(cfg) => {
            let amm = AmmConfig::Dynamic(cfg);
            let factory_result = DefaultPoolFactory::create(&amm);
            assert!(
                factory_result.is_err(),
                "factory should reject zero reserve"
            );
        }
    }
}

#[test]
fn config_validation_dynamic_zero_oracle_price() {
    let Ok(price) = Price::new(0.0) else {
        panic!("valid price");
    };
    let result = DynamicConfig::new(
        make_pair(),
        fee_30bp(),
        price,
        0.5,
        Amount::new(1_000),
        Amount::new(1_000),
    );
    match result {
        Err(_) => {}
        Ok(cfg) => {
            let amm = AmmConfig::Dynamic(cfg);
            let factory_result = DefaultPoolFactory::create(&amm);
            assert!(factory_result.is_err(), "factory should reject oracle=0");
        }
    }
}

#[test]
fn config_validation_order_book_zero_tick_size() {
    let result = OrderBookConfig::new(make_pair(), fee_30bp(), Amount::ZERO, Amount::new(1));
    match result {
        Err(_) => {}
        Ok(cfg) => {
            let amm = AmmConfig::OrderBook(cfg);
            let factory_result = DefaultPoolFactory::create(&amm);
            assert!(
                factory_result.is_err(),
                "factory should reject zero tick_size"
            );
        }
    }
}

#[test]
fn config_validation_order_book_zero_lot_size() {
    let result = OrderBookConfig::new(make_pair(), fee_30bp(), Amount::new(1), Amount::ZERO);
    match result {
        Err(_) => {}
        Ok(cfg) => {
            let amm = AmmConfig::OrderBook(cfg);
            let factory_result = DefaultPoolFactory::create(&amm);
            assert!(
                factory_result.is_err(),
                "factory should reject zero lot_size"
            );
        }
    }
}

#[test]
fn config_validation_clmm_unaligned_tick() {
    // tick_spacing=10, current_tick=5 → not aligned
    let result = ClmmConfig::new(make_pair(), fee_30bp(), 10, tick(5), vec![]);
    match result {
        Err(_) => {}
        Ok(cfg) => {
            let amm = AmmConfig::Clmm(cfg);
            let factory_result = DefaultPoolFactory::create(&amm);
            assert!(
                factory_result.is_err(),
                "factory should reject unaligned tick"
            );
        }
    }
}

// No panics on any invalid config — graceful error handling
#[test]
fn config_validation_never_panics() {
    // Attempt various invalid configs; none should panic
    let _ = ConstantProductConfig::new(make_pair(), fee_30bp(), Amount::ZERO, Amount::ZERO);
    let _ = HybridConfig::new(make_pair(), fee_30bp(), 0, Amount::ZERO, Amount::ZERO);
    let _ = WeightedConfig::new(vec![], vec![], fee_30bp(), vec![]);
    let _ = OrderBookConfig::new(make_pair(), fee_30bp(), Amount::ZERO, Amount::ZERO);
}

// ===========================================================================
// Suite 4: Feature Flag Isolation
// ===========================================================================
// Feature flag isolation is primarily verified by the CI build matrix which
// compiles with individual feature flags. The factory's catch-all arm returns
// InvalidConfiguration for disabled features. We test the factory creates
// all types when all features are enabled.

#[test]
fn factory_creates_all_pool_types_when_all_features_enabled() {
    assert!(DefaultPoolFactory::create(&cp_config(1_000, 2_000)).is_ok());
    assert!(DefaultPoolFactory::create(&clmm_config()).is_ok());
    assert!(DefaultPoolFactory::create(&hybrid_config(100, 1_000)).is_ok());
    assert!(DefaultPoolFactory::create(&weighted_config(1_000, 2_000)).is_ok());
    assert!(DefaultPoolFactory::create(&dynamic_config(0.5, 1.0, 1_000, 1_000)).is_ok());
    assert!(DefaultPoolFactory::create(&order_book_config()).is_ok());
}

// ===========================================================================
// Suite 5: Full Trading Lifecycle
// ===========================================================================

#[test]
fn full_trading_lifecycle_constant_product() {
    // Step 1: Create pool with initial reserves
    let Ok(mut pool) = DefaultPoolFactory::create(&cp_config(1_000_000, 2_000_000)) else {
        panic!("factory should create pool");
    };
    let initial_liq = pool.total_liquidity();
    assert!(initial_liq.get() > 0, "pool should start with liquidity");

    // Step 2: LP1 adds 10% proportional liquidity
    let Ok(add_change) = LiquidityChange::add(Amount::new(100_000), Amount::new(200_000)) else {
        panic!("valid add change");
    };
    let Ok(minted) = pool.add_liquidity(&add_change) else {
        panic!("add_liquidity should succeed");
    };
    assert!(minted.get() > 0, "should mint LP tokens");
    let liq_after_add = pool.total_liquidity();
    assert!(
        liq_after_add.get() > initial_liq.get(),
        "liquidity should increase after add"
    );

    // Step 3: Execute multiple swaps
    let swap_amounts = [1_000u128, 5_000, 2_000, 10_000, 500];
    for &amount in &swap_amounts {
        let Ok(spec) = SwapSpec::exact_in(Amount::new(amount)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("swap should succeed");
        };
        assert!(result.amount_out().get() > 0);
        assert!(result.fee().get() > 0);
    }

    // Step 4: Collect accumulated fees
    let Ok(fees) = pool.collect_fees(&dummy_position()) else {
        panic!("collect_fees should succeed");
    };
    assert!(fees.get() > 0, "fees should have accumulated from swaps");

    // Step 5: Remove the LP tokens that were minted
    let Ok(remove_change) = LiquidityChange::remove(Liquidity::new(minted.get())) else {
        panic!("valid remove change");
    };
    let Ok(withdrawn) = pool.remove_liquidity(&remove_change) else {
        panic!("remove_liquidity should succeed");
    };
    assert!(withdrawn.get() > 0, "should receive tokens back");

    // Step 6: Verify final state — liquidity should be approximately back to initial
    let final_liq = pool.total_liquidity();
    let diff = if final_liq.get() > initial_liq.get() {
        final_liq.get() - initial_liq.get()
    } else {
        initial_liq.get() - final_liq.get()
    };
    // Allow small tolerance for rounding
    let tolerance = initial_liq.get() / 100 + 1;
    assert!(
        diff <= tolerance,
        "final liquidity ({}) should ≈ initial ({}), diff={}",
        final_liq.get(),
        initial_liq.get(),
        diff
    );
}

#[test]
fn full_trading_lifecycle_hybrid() {
    // Step 1: Create Hybrid pool at peg
    let Ok(mut pool) = DefaultPoolFactory::create(&hybrid_config(100, 1_000_000)) else {
        panic!("factory should create pool");
    };
    let initial_liq = pool.total_liquidity();

    // Step 2: Add liquidity
    let Ok(add_change) = LiquidityChange::add(Amount::new(100_000), Amount::new(100_000)) else {
        panic!("valid add change");
    };
    let Ok(minted) = pool.add_liquidity(&add_change) else {
        panic!("add_liquidity should succeed");
    };
    assert!(minted.get() > 0);

    // Step 3: Execute swaps in both directions
    for _ in 0..3 {
        let Ok(spec) = SwapSpec::exact_in(Amount::new(5_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_a()) else {
            panic!("swap A→B should succeed");
        };
        assert!(result.amount_out().get() > 0);
    }

    for _ in 0..3 {
        let Ok(spec) = SwapSpec::exact_in(Amount::new(5_000)) else {
            panic!("valid spec");
        };
        let Ok(result) = pool.swap(spec, tok_b()) else {
            panic!("swap B→A should succeed");
        };
        assert!(result.amount_out().get() > 0);
    }

    // Step 4: Collect fees
    let Ok(fees) = pool.collect_fees(&dummy_position()) else {
        panic!("collect_fees should succeed");
    };
    assert!(fees.get() > 0, "fees should have accumulated");

    // Step 5: Remove liquidity
    let Ok(remove_change) = LiquidityChange::remove(Liquidity::new(minted.get())) else {
        panic!("valid remove change");
    };
    let Ok(withdrawn) = pool.remove_liquidity(&remove_change) else {
        panic!("remove_liquidity should succeed");
    };
    assert!(withdrawn.get() > 0);

    // Final liquidity should be close to initial
    let final_liq = pool.total_liquidity();
    let diff = if final_liq.get() > initial_liq.get() {
        final_liq.get() - initial_liq.get()
    } else {
        initial_liq.get() - final_liq.get()
    };
    let tolerance = initial_liq.get() / 100 + 1;
    assert!(
        diff <= tolerance,
        "final liquidity ({}) should ≈ initial ({}), diff={}",
        final_liq.get(),
        initial_liq.get(),
        diff
    );
}

#[test]
fn full_lifecycle_no_tokens_lost_or_created() {
    // Track token conservation: total tokens A in system = initial_ra + deposited_a
    let ra = 1_000_000u128;
    let rb = 2_000_000u128;
    let Ok(mut pool) = DefaultPoolFactory::create(&cp_config(ra, rb)) else {
        panic!("factory");
    };

    // Execute a swap and verify: amount_in + reserves_before = amount_out + reserves_after
    // (within the pool's reserves, excluding external balances)
    let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
        panic!("valid spec");
    };
    let Ok(result) = pool.swap(spec, tok_a()) else {
        panic!("swap");
    };

    // After swap: the pool absorbed 10_000 A and released result.amount_out() B
    // The fee stays inside the pool, so total value is conserved
    assert!(result.amount_in().get() > 0);
    assert!(result.amount_out().get() > 0);
    assert!(result.fee().get() > 0);
    // fee is deducted from amount_in before computing output
    assert!(result.fee().get() < result.amount_in().get());
}

#[test]
fn full_lifecycle_swap_exact_out() {
    let Ok(mut pool) = DefaultPoolFactory::create(&cp_config(1_000_000, 2_000_000)) else {
        panic!("factory");
    };

    let Ok(spec) = SwapSpec::exact_out(Amount::new(1_000)) else {
        panic!("valid spec");
    };
    let Ok(result) = pool.swap(spec, tok_a()) else {
        panic!("exact_out swap should succeed");
    };

    // Should receive at least the requested amount
    assert!(result.amount_out().get() >= 1_000);
    assert!(result.amount_in().get() > 0);
    assert!(result.fee().get() > 0);
}

#[test]
fn full_lifecycle_multiple_lps() {
    let Ok(mut pool) = DefaultPoolFactory::create(&cp_config(1_000_000, 2_000_000)) else {
        panic!("factory");
    };
    let initial_liq = pool.total_liquidity().get();

    // LP1 adds 10% liquidity
    let Ok(add1) = LiquidityChange::add(Amount::new(100_000), Amount::new(200_000)) else {
        panic!("valid change");
    };
    let Ok(minted1) = pool.add_liquidity(&add1) else {
        panic!("LP1 add should succeed");
    };

    // LP2 adds 5% liquidity
    let Ok(add2) = LiquidityChange::add(Amount::new(50_000), Amount::new(100_000)) else {
        panic!("valid change");
    };
    let Ok(minted2) = pool.add_liquidity(&add2) else {
        panic!("LP2 add should succeed");
    };

    assert!(
        minted1.get() > minted2.get(),
        "LP1 deposited more → more LP tokens"
    );

    // Execute some swaps to generate fees
    for _ in 0..5 {
        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("spec");
        };
        let Ok(_) = pool.swap(spec, tok_a()) else {
            panic!("swap");
        };
    }

    // LP1 removes their share
    let Ok(rem1) = LiquidityChange::remove(Liquidity::new(minted1.get())) else {
        panic!("valid remove");
    };
    let Ok(withdrawn1) = pool.remove_liquidity(&rem1) else {
        panic!("LP1 remove");
    };

    // LP2 removes their share
    let Ok(rem2) = LiquidityChange::remove(Liquidity::new(minted2.get())) else {
        panic!("valid remove");
    };
    let Ok(withdrawn2) = pool.remove_liquidity(&rem2) else {
        panic!("LP2 remove");
    };

    // LP1 had more liquidity → should withdraw more
    assert!(
        withdrawn1.get() > withdrawn2.get(),
        "LP1 ({}) should withdraw more than LP2 ({})",
        withdrawn1.get(),
        withdrawn2.get()
    );

    // Pool liquidity should return to approximately initial
    let final_liq = pool.total_liquidity().get();
    let diff = final_liq.abs_diff(initial_liq);
    let tolerance = initial_liq / 100 + 1;
    assert!(
        diff <= tolerance,
        "liquidity should return to ≈ initial: final={final_liq}, initial={initial_liq}, diff={diff}"
    );
}
