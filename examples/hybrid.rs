//! Hybrid / StableSwap AMM example (Curve style).
//!
//! Demonstrates creating a hybrid pool optimized for stablecoin pairs,
//! where the amplification parameter controls the curve shape between
//! constant product and constant sum.
//!
//! # Run
//!
//! ```bash
//! cargo run --example hybrid --all-features
//! ```

use hydra_amm::config::{AmmConfig, HybridConfig};
use hydra_amm::domain::{
    Amount, BasisPoints, Decimals, FeeTier, Liquidity, LiquidityChange, Rounding, SwapSpec, Token,
    TokenAddress, TokenPair,
};
use hydra_amm::factory::DefaultPoolFactory;
use hydra_amm::traits::{LiquidityPool, SwapPool};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Hybrid / StableSwap AMM (Curve style) ===\n");

    // ── 1. Define stablecoin tokens ─────────────────────────────────────
    let usdc = Token::new(TokenAddress::from_bytes([1u8; 32]), Decimals::new(6)?);
    let usdt = Token::new(TokenAddress::from_bytes([2u8; 32]), Decimals::new(6)?);
    let pair = TokenPair::new(usdc, usdt)?;

    println!("Token A (USDC): {} decimals", usdc.decimals().get());
    println!("Token B (USDT): {} decimals", usdt.decimals().get());

    // ── 2. Configure the pool ───────────────────────────────────────────
    //    amplification = 100: strong peg around 1:1
    //    Higher amplification → flatter curve → less slippage near peg
    let fee = FeeTier::new(BasisPoints::new(4)); // 0.04% fee (typical for stables)
    let amplification = 100;
    let reserve_a = Amount::new(10_000_000); // 10 M USDC
    let reserve_b = Amount::new(10_000_000); // 10 M USDT

    let config = AmmConfig::Hybrid(HybridConfig::new(
        pair,
        fee,
        amplification,
        reserve_a,
        reserve_b,
    )?);

    println!("\nPool config: {config}");
    println!("  Fee tier:        {} bps", fee.basis_points());
    println!("  Amplification:   {amplification} (range: 1–10 000)");
    println!("  Reserve A:       {reserve_a}");
    println!("  Reserve B:       {reserve_b}");

    // ── 3. Create the pool ──────────────────────────────────────────────
    let mut pool = DefaultPoolFactory::create(&config)?;
    println!("\nPool created successfully");

    // ── 4. Query the initial spot price ─────────────────────────────────
    //    For stablecoins, we expect this to be very close to 1.0
    let price = pool.spot_price(&usdc, &usdt)?;
    println!("  Spot price (USDT per USDC): {price}");

    // ── 5. Execute a large swap ─────────────────────────────────────────
    //    StableSwap should show very low slippage compared to constant product
    let swap_amount = Amount::new(1_000_000); // 1 M USDC
    let spec = SwapSpec::exact_in(swap_amount)?;
    let result = pool.swap(spec, usdc)?;

    println!("\n--- Swap: sell {swap_amount} USDC ---");
    println!("  Amount in:   {}", result.amount_in());
    println!("  Amount out:  {}", result.amount_out());
    println!("  Fee paid:    {}", result.fee());
    let effective = result.effective_price(Rounding::Down)?;
    println!("  Eff. price:  {effective}");

    // ── 6. Measure slippage against the 1:1 peg ────────────────────────
    let peg = hydra_amm::domain::Price::ONE;
    let slippage = result.slippage_percent(peg, Rounding::Down)?;
    println!("  Slippage:    {slippage:.4}%");

    // ── 7. Check price after swap ───────────────────────────────────────
    let price_after = pool.spot_price(&usdc, &usdt)?;
    println!("\n  Spot price after swap: {price_after}");

    // ── 8. Add liquidity ────────────────────────────────────────────────
    let add = LiquidityChange::add(Amount::new(5_000_000), Amount::new(5_000_000))?;
    let minted = pool.add_liquidity(&add)?;
    println!("\n--- Add Liquidity ---");
    println!("  Deposited:   5 000 000 A + 5 000 000 B");
    println!("  LP minted:   {minted}");
    println!("  Total liq:   {}", pool.total_liquidity());

    // ── 9. Remove liquidity ─────────────────────────────────────────────
    let remove = LiquidityChange::remove(Liquidity::new(1_000_000))?;
    let returned = pool.remove_liquidity(&remove)?;
    println!("\n--- Remove Liquidity ---");
    println!("  Removed:     1 000 000 LP units");
    println!("  Returned:    {returned}");

    println!("\n=== Done ===");
    Ok(())
}
