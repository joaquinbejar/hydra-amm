//! Concentrated Liquidity Market Maker (CLMM) example (Uniswap V3 style).
//!
//! Demonstrates creating a CLMM pool with tick-based concentrated liquidity
//! positions, executing swaps across tick ranges, and managing liquidity.
//!
//! # Run
//!
//! ```bash
//! cargo run --example clmm --all-features
//! ```

use hydra_amm::config::{AmmConfig, ClmmConfig};
use hydra_amm::domain::{
    Amount, BasisPoints, Decimals, FeeTier, Liquidity, LiquidityChange, Position, Rounding,
    SwapSpec, Tick, Token, TokenAddress, TokenPair,
};
use hydra_amm::factory::DefaultPoolFactory;
use hydra_amm::traits::{LiquidityPool, SwapPool};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Concentrated Liquidity Market Maker (CLMM) ===\n");

    // ── 1. Define tokens ────────────────────────────────────────────────
    let tok_a = Token::new(TokenAddress::from_bytes([1u8; 32]), Decimals::new(6)?);
    let tok_b = Token::new(TokenAddress::from_bytes([2u8; 32]), Decimals::new(18)?);
    let pair = TokenPair::new(tok_a, tok_b)?;

    // ── 2. Create initial positions ─────────────────────────────────────
    //    Liquidity is concentrated in specific tick ranges.
    //    Tick spacing = 10, so all ticks must be multiples of 10.
    let position_narrow = Position::new(
        Tick::new(-100)?, // lower tick
        Tick::new(100)?,  // upper tick
        Liquidity::new(1_000_000),
    )?;

    let position_wide = Position::new(Tick::new(-500)?, Tick::new(500)?, Liquidity::new(500_000))?;

    println!(
        "Position 1 (narrow): ticks [{}, {}], liquidity = 1 000 000",
        position_narrow.lower_tick(),
        position_narrow.upper_tick()
    );
    println!(
        "Position 2 (wide):   ticks [{}, {}], liquidity = 500 000",
        position_wide.lower_tick(),
        position_wide.upper_tick()
    );

    // ── 3. Configure the CLMM pool ─────────────────────────────────────
    let fee = FeeTier::new(BasisPoints::new(30));
    let tick_spacing = 10;
    let current_tick = Tick::new(0)?;

    let config = AmmConfig::Clmm(ClmmConfig::new(
        pair,
        fee,
        tick_spacing,
        current_tick,
        vec![position_narrow, position_wide],
    )?);

    println!("\nPool config: {config}");
    println!("  Fee tier:      {} bps", fee.basis_points());
    println!("  Tick spacing:  {tick_spacing}");
    println!("  Current tick:  {current_tick}");

    // ── 4. Create the pool via the factory ──────────────────────────────
    let mut pool = DefaultPoolFactory::create(&config)?;
    println!("\nPool created successfully");
    println!("  Total liquidity: {}", pool.total_liquidity());

    // ── 5. Query the initial spot price ─────────────────────────────────
    let price = pool.spot_price(&tok_a, &tok_b)?;
    println!("  Spot price (B per A): {price}");

    // ── 6. Execute a swap: sell token A ─────────────────────────────────
    let swap_amount = Amount::new(1_000);
    let spec = SwapSpec::exact_in(swap_amount)?;
    let result = pool.swap(spec, tok_a)?;

    println!("\n--- Swap: sell {swap_amount} token A ---");
    println!("  Amount in:   {}", result.amount_in());
    println!("  Amount out:  {}", result.amount_out());
    println!("  Fee paid:    {}", result.fee());
    let effective = result.effective_price(Rounding::Down)?;
    println!("  Eff. price:  {effective}");

    // ── 7. Check price after swap ───────────────────────────────────────
    let price_after = pool.spot_price(&tok_a, &tok_b)?;
    println!("\n  Spot price after swap: {price_after}");

    // ── 8. Add more liquidity ───────────────────────────────────────────
    let add = LiquidityChange::add(Amount::new(200_000), Amount::new(200_000))?;
    let minted = pool.add_liquidity(&add)?;
    println!("\n--- Add Liquidity ---");
    println!("  Deposited:   200 000 A + 200 000 B");
    println!("  LP minted:   {minted}");
    println!("  Total liq:   {}", pool.total_liquidity());

    // ── 9. Swap in the opposite direction ───────────────────────────────
    let spec2 = SwapSpec::exact_in(Amount::new(500))?;
    let result2 = pool.swap(spec2, tok_b)?;
    println!("\n--- Swap: sell 500 token B ---");
    println!("  Amount out:  {}", result2.amount_out());
    println!("  Fee paid:    {}", result2.fee());

    println!("\n=== Done ===");
    Ok(())
}
