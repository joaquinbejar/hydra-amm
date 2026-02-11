//! Constant Product AMM example (Uniswap V2 style).
//!
//! Demonstrates creating a constant product pool (`x · y = k`), executing
//! swaps, adding/removing liquidity, and querying spot prices.
//!
//! # Run
//!
//! ```bash
//! cargo run --example constant_product --all-features
//! ```

use hydra_amm::config::{AmmConfig, ConstantProductConfig};
use hydra_amm::domain::{
    Amount, BasisPoints, Decimals, FeeTier, Liquidity, LiquidityChange, Rounding, SwapSpec, Token,
    TokenAddress, TokenPair,
};
use hydra_amm::factory::DefaultPoolFactory;
use hydra_amm::traits::{LiquidityPool, SwapPool};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Constant Product AMM (x · y = k) ===\n");

    // ── 1. Define tokens ────────────────────────────────────────────────
    let usdc = Token::new(TokenAddress::from_bytes([1u8; 32]), Decimals::new(6)?);
    let weth = Token::new(TokenAddress::from_bytes([2u8; 32]), Decimals::new(18)?);
    let pair = TokenPair::new(usdc, weth)?;

    println!("Token A (USDC): {} decimals", usdc.decimals().get());
    println!("Token B (WETH): {} decimals", weth.decimals().get());

    // ── 2. Configure a pool with balanced reserves and 0.30% fee ────────
    let fee = FeeTier::new(BasisPoints::new(30));
    let reserve_a = Amount::new(1_000_000); // 1 M USDC
    let reserve_b = Amount::new(1_000_000); // 1 M WETH (in smallest units)

    let config =
        AmmConfig::ConstantProduct(ConstantProductConfig::new(pair, fee, reserve_a, reserve_b)?);
    println!("\nPool config: {config}");
    println!("  Fee tier:    {} bps", fee.basis_points());
    println!("  Reserve A:   {reserve_a}");
    println!("  Reserve B:   {reserve_b}");

    // ── 3. Create the pool via the factory ──────────────────────────────
    let mut pool = DefaultPoolFactory::create(&config)?;
    println!("\nPool created successfully via DefaultPoolFactory");

    // ── 4. Query the initial spot price ─────────────────────────────────
    let price = pool.spot_price(&usdc, &weth)?;
    println!("\nSpot price (WETH per USDC): {price}");

    // ── 5. Execute a swap: sell 10 000 USDC for WETH ────────────────────
    let swap_amount = Amount::new(10_000);
    let spec = SwapSpec::exact_in(swap_amount)?;
    let result = pool.swap(spec, usdc)?;

    println!("\n--- Swap: sell {swap_amount} USDC ---");
    println!("  Amount in:   {}", result.amount_in());
    println!("  Amount out:  {}", result.amount_out());
    println!("  Fee paid:    {}", result.fee());
    let effective = result.effective_price(Rounding::Down)?;
    println!("  Eff. price:  {effective}");

    // ── 6. Check the new spot price after the swap ──────────────────────
    let price_after = pool.spot_price(&usdc, &weth)?;
    println!("\nSpot price after swap: {price_after}");
    println!("  Price moved from {price} → {price_after}");

    // ── 7. Add liquidity ────────────────────────────────────────────────
    let add = LiquidityChange::add(Amount::new(500_000), Amount::new(500_000))?;
    let minted = pool.add_liquidity(&add)?;
    println!("\n--- Add Liquidity ---");
    println!("  Deposited:   500 000 A + 500 000 B");
    println!("  LP minted:   {minted}");
    println!("  Total liq:   {}", pool.total_liquidity());

    // ── 8. Remove liquidity ─────────────────────────────────────────────
    let remove = LiquidityChange::remove(Liquidity::new(100_000))?;
    let returned = pool.remove_liquidity(&remove)?;
    println!("\n--- Remove Liquidity ---");
    println!("  Removed:     100 000 LP units");
    println!("  Returned:    {returned}");
    println!("  Total liq:   {}", pool.total_liquidity());

    // ── 9. Execute another swap to show the pool still works ────────────
    let spec2 = SwapSpec::exact_in(Amount::new(5_000))?;
    let result2 = pool.swap(spec2, weth)?;
    println!("\n--- Swap: sell 5 000 WETH ---");
    println!("  Amount out:  {}", result2.amount_out());
    println!("  Fee paid:    {}", result2.fee());

    println!("\n=== Done ===");
    Ok(())
}
