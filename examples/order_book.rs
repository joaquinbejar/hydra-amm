//! Order Book Hybrid AMM example (Phoenix style).
//!
//! Demonstrates creating an order book hybrid pool that combines a
//! central limit order book (CLOB) with AMM fallback pricing.
//!
//! # Run
//!
//! ```bash
//! cargo run --example order_book --all-features
//! ```

use hydra_amm::config::{AmmConfig, OrderBookConfig};
use hydra_amm::domain::{
    Amount, BasisPoints, Decimals, FeeTier, Liquidity, LiquidityChange, Rounding, SwapSpec, Token,
    TokenAddress, TokenPair,
};
use hydra_amm::factory::DefaultPoolFactory;
use hydra_amm::traits::{LiquidityPool, SwapPool};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Order Book Hybrid AMM (Phoenix style) ===\n");

    // ── 1. Define tokens ────────────────────────────────────────────────
    let sol = Token::new(TokenAddress::from_bytes([1u8; 32]), Decimals::new(9)?);
    let usdc = Token::new(TokenAddress::from_bytes([2u8; 32]), Decimals::new(6)?);
    let pair = TokenPair::new(sol, usdc)?;

    println!("Token A (SOL):  {} decimals", sol.decimals().get());
    println!("Token B (USDC): {} decimals", usdc.decimals().get());

    // ── 2. Configure the order book pool ────────────────────────────────
    //    tick_size = minimum price increment
    //    lot_size  = minimum quantity increment
    let fee = FeeTier::new(BasisPoints::new(10)); // 0.10% fee
    let tick_size = Amount::new(1); // 1 unit price granularity
    let lot_size = Amount::new(100); // minimum 100 units per order

    let config = AmmConfig::OrderBook(OrderBookConfig::new(pair, fee, tick_size, lot_size)?);

    println!("Pool config: {config}");
    println!("  Fee tier:    {} bps", fee.basis_points());
    println!("  Tick size:   {tick_size}");
    println!("  Lot size:    {lot_size}");

    // ── 3. Create the pool ──────────────────────────────────────────────
    let mut pool = DefaultPoolFactory::create(&config)?;
    println!("\nPool created successfully");

    // ── 4. Add initial liquidity ────────────────────────────────────────
    //    The order book needs liquidity before it can facilitate swaps.
    let add = LiquidityChange::add(Amount::new(1_000_000), Amount::new(1_000_000))?;
    let minted = pool.add_liquidity(&add)?;
    println!("\n--- Seed Liquidity ---");
    println!("  Deposited:   1 000 000 SOL + 1 000 000 USDC");
    println!("  LP minted:   {minted}");
    println!("  Total liq:   {}", pool.total_liquidity());

    // ── 5. Query the spot price ─────────────────────────────────────────
    let price = pool.spot_price(&sol, &usdc)?;
    println!("\n  Spot price (USDC per SOL): {price}");

    // ── 6. Execute a swap: sell SOL for USDC ────────────────────────────
    let swap_amount = Amount::new(10_000);
    let spec = SwapSpec::exact_in(swap_amount)?;
    let result = pool.swap(spec, sol)?;

    println!("\n--- Swap: sell {swap_amount} SOL ---");
    println!("  Amount in:   {}", result.amount_in());
    println!("  Amount out:  {} USDC", result.amount_out());
    println!("  Fee paid:    {}", result.fee());
    let effective = result.effective_price(Rounding::Down)?;
    println!("  Eff. price:  {effective}");

    // ── 7. Swap in the opposite direction ───────────────────────────────
    let spec2 = SwapSpec::exact_in(Amount::new(5_000))?;
    let result2 = pool.swap(spec2, usdc)?;
    println!("\n--- Swap: sell 5 000 USDC ---");
    println!("  Amount out:  {} SOL", result2.amount_out());
    println!("  Fee paid:    {}", result2.fee());

    // ── 8. Remove some liquidity ────────────────────────────────────────
    let remove = LiquidityChange::remove(Liquidity::new(100_000))?;
    let returned = pool.remove_liquidity(&remove)?;
    println!("\n--- Remove Liquidity ---");
    println!("  Removed:     100 000 LP units");
    println!("  Returned:    {returned}");
    println!("  Total liq:   {}", pool.total_liquidity());

    println!("\n=== Done ===");
    Ok(())
}
