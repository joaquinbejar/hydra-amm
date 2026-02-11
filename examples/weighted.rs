//! Weighted Pool AMM example (Balancer style).
//!
//! Demonstrates creating a weighted pool with custom token weights
//! (e.g., 80/20 split), executing swaps, and managing liquidity.
//!
//! # Run
//!
//! ```bash
//! cargo run --example weighted --all-features
//! ```

use hydra_amm::config::{AmmConfig, WeightedConfig};
use hydra_amm::domain::{
    Amount, BasisPoints, Decimals, FeeTier, Liquidity, LiquidityChange, Rounding, SwapSpec, Token,
    TokenAddress,
};
use hydra_amm::factory::DefaultPoolFactory;
use hydra_amm::traits::{LiquidityPool, SwapPool};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Weighted Pool AMM (Balancer style) ===\n");

    // ── 1. Define tokens ────────────────────────────────────────────────
    let weth = Token::new(TokenAddress::from_bytes([1u8; 32]), Decimals::new(18)?);
    let dai = Token::new(TokenAddress::from_bytes([2u8; 32]), Decimals::new(18)?);

    println!("Token 0 (WETH): {} decimals", weth.decimals().get());
    println!("Token 1 (DAI):  {} decimals", dai.decimals().get());

    // ── 2. Configure an 80/20 weighted pool ─────────────────────────────
    //    Weights are in basis points and must sum to 10 000.
    //    80% WETH / 20% DAI — a classic Balancer configuration.
    let fee = FeeTier::new(BasisPoints::new(30)); // 0.30% fee
    let weight_weth = BasisPoints::new(8_000); // 80%
    let weight_dai = BasisPoints::new(2_000); // 20%

    let balance_weth = Amount::new(1_000_000); // 1 M WETH (smallest units)
    let balance_dai = Amount::new(4_000_000); // 4 M DAI

    let config = AmmConfig::Weighted(WeightedConfig::new(
        vec![weth, dai],
        vec![weight_weth, weight_dai],
        fee,
        vec![balance_weth, balance_dai],
    )?);

    println!("\nPool config: {config}");
    println!("  Fee tier:      {} bps", fee.basis_points());
    println!("  Weight WETH:   {} bps (80%)", weight_weth);
    println!("  Weight DAI:    {} bps (20%)", weight_dai);
    println!("  Balance WETH:  {balance_weth}");
    println!("  Balance DAI:   {balance_dai}");

    // ── 3. Create the pool ──────────────────────────────────────────────
    let mut pool = DefaultPoolFactory::create(&config)?;
    println!("\nPool created successfully");

    // ── 4. Query the initial spot price ─────────────────────────────────
    let price = pool.spot_price(&weth, &dai)?;
    println!("  Spot price (DAI per WETH): {price}");

    // ── 5. Execute a swap: sell WETH for DAI ────────────────────────────
    let swap_amount = Amount::new(10_000);
    let spec = SwapSpec::exact_in(swap_amount)?;
    let result = pool.swap(spec, weth)?;

    println!("\n--- Swap: sell {swap_amount} WETH ---");
    println!("  Amount in:   {}", result.amount_in());
    println!("  Amount out:  {} DAI", result.amount_out());
    println!("  Fee paid:    {}", result.fee());
    let effective = result.effective_price(Rounding::Down)?;
    println!("  Eff. price:  {effective}");

    // ── 6. Price after swap ─────────────────────────────────────────────
    let price_after = pool.spot_price(&weth, &dai)?;
    println!("\n  Spot price after swap: {price_after}");

    // ── 7. Swap in the opposite direction: sell DAI for WETH ────────────
    let spec2 = SwapSpec::exact_in(Amount::new(50_000))?;
    let result2 = pool.swap(spec2, dai)?;
    println!("\n--- Swap: sell 50 000 DAI ---");
    println!("  Amount out:  {} WETH", result2.amount_out());
    println!("  Fee paid:    {}", result2.fee());

    // ── 8. Add liquidity ────────────────────────────────────────────────
    let add = LiquidityChange::add(Amount::new(100_000), Amount::new(400_000))?;
    let minted = pool.add_liquidity(&add)?;
    println!("\n--- Add Liquidity ---");
    println!("  Deposited:   100 000 WETH + 400 000 DAI");
    println!("  LP minted:   {minted}");
    println!("  Total liq:   {}", pool.total_liquidity());

    // ── 9. Remove liquidity ─────────────────────────────────────────────
    let remove = LiquidityChange::remove(Liquidity::new(50_000))?;
    let returned = pool.remove_liquidity(&remove)?;
    println!("\n--- Remove Liquidity ---");
    println!("  Removed:     50 000 LP units");
    println!("  Returned:    {returned}");

    println!("\n=== Done ===");
    Ok(())
}
