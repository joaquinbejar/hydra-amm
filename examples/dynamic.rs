//! Dynamic / Proactive Market Maker (PMM) example (DODO style).
//!
//! Demonstrates creating a dynamic pool that uses an oracle price to
//! concentrate liquidity, with a slippage coefficient controlling how
//! closely the pool tracks the oracle.
//!
//! # Run
//!
//! ```bash
//! cargo run --example dynamic --all-features
//! ```

use hydra_amm::config::{AmmConfig, DynamicConfig};
use hydra_amm::domain::{
    Amount, BasisPoints, Decimals, FeeTier, Liquidity, LiquidityChange, Price, Rounding, SwapSpec,
    Token, TokenAddress, TokenPair,
};
use hydra_amm::factory::DefaultPoolFactory;
use hydra_amm::traits::{LiquidityPool, SwapPool};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Dynamic / Proactive Market Maker (DODO style) ===\n");

    // ── 1. Define tokens ────────────────────────────────────────────────
    let base = Token::new(TokenAddress::from_bytes([1u8; 32]), Decimals::new(18)?);
    let quote = Token::new(TokenAddress::from_bytes([2u8; 32]), Decimals::new(6)?);
    let pair = TokenPair::new(base, quote)?;

    println!("Base token:  {} decimals", base.decimals().get());
    println!("Quote token: {} decimals", quote.decimals().get());

    // ── 2. Configure the pool ───────────────────────────────────────────
    //    oracle_price = 100.0 (quote per base)
    //    slippage_coefficient k = 0.5 (between constant product and oracle)
    //    k = 0.0 → trades at oracle price (infinite liquidity)
    //    k = 1.0 → behaves like constant product
    let fee = FeeTier::new(BasisPoints::new(30));
    let oracle_price = Price::new(100.0)?;
    let k = 0.5;
    let base_reserve = Amount::new(1_000_000);
    let quote_reserve = Amount::new(100_000_000); // 100 M quote

    let config = AmmConfig::Dynamic(DynamicConfig::new(
        pair,
        fee,
        oracle_price,
        k,
        base_reserve,
        quote_reserve,
    )?);

    println!("\nPool config: {config}");
    println!("  Fee tier:      {} bps", fee.basis_points());
    println!("  Oracle price:  {oracle_price}");
    println!("  Slippage k:    {k} (0.0=oracle, 1.0=CPMM)");
    println!("  Base reserve:  {base_reserve}");
    println!("  Quote reserve: {quote_reserve}");

    // ── 3. Create the pool ──────────────────────────────────────────────
    let mut pool = DefaultPoolFactory::create(&config)?;
    println!("\nPool created successfully");

    // ── 4. Query the initial spot price ─────────────────────────────────
    let price = pool.spot_price(&base, &quote)?;
    println!("  Spot price (quote per base): {price}");

    // ── 5. Execute a swap: sell base tokens ─────────────────────────────
    let swap_amount = Amount::new(10_000);
    let spec = SwapSpec::exact_in(swap_amount)?;
    let result = pool.swap(spec, base)?;

    println!("\n--- Swap: sell {swap_amount} base ---");
    println!("  Amount in:   {}", result.amount_in());
    println!("  Amount out:  {} quote", result.amount_out());
    println!("  Fee paid:    {}", result.fee());
    let effective = result.effective_price(Rounding::Down)?;
    println!("  Eff. price:  {effective}");

    // ── 6. Measure slippage against oracle ──────────────────────────────
    let slippage = result.slippage_percent(oracle_price, Rounding::Down)?;
    println!("  Slippage vs oracle: {slippage:.4}%");

    // ── 7. Price after swap ─────────────────────────────────────────────
    let price_after = pool.spot_price(&base, &quote)?;
    println!("\n  Spot price after swap: {price_after}");

    // ── 8. Swap in the opposite direction ───────────────────────────────
    let spec2 = SwapSpec::exact_in(Amount::new(500_000))?;
    let result2 = pool.swap(spec2, quote)?;
    println!("\n--- Swap: sell 500 000 quote ---");
    println!("  Amount out:  {} base", result2.amount_out());
    println!("  Fee paid:    {}", result2.fee());

    // ── 9. Liquidity management ─────────────────────────────────────────
    let add = LiquidityChange::add(Amount::new(100_000), Amount::new(10_000_000))?;
    let minted = pool.add_liquidity(&add)?;
    println!("\n--- Add Liquidity ---");
    println!("  LP minted:   {minted}");
    println!("  Total liq:   {}", pool.total_liquidity());

    let remove = LiquidityChange::remove(Liquidity::new(50_000))?;
    let returned = pool.remove_liquidity(&remove)?;
    println!("\n--- Remove Liquidity ---");
    println!("  Returned:    {returned}");

    println!("\n=== Done ===");
    Ok(())
}
