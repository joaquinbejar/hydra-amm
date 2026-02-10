# Hydra AMM

[![Crates.io](https://img.shields.io/crates/v/hydra-amm.svg)](https://crates.io/crates/hydra-amm)
[![Documentation](https://docs.rs/hydra-amm/badge.svg)](https://docs.rs/hydra-amm)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Build Status](https://github.com/joaquinbejar/hydra-amm/actions/workflows/ci.yml/badge.svg)](https://github.com/joaquinbejar/hydra-amm/actions)
[![codecov](https://codecov.io/gh/joaquinbejar/hydra-amm/branch/main/graph/badge.svg)](https://codecov.io/gh/joaquinbejar/hydra-amm)

**Universal AMM engine**: build, configure, and operate any Automated Market Maker through a unified interface.

Hydra AMM is a Rust library that provides a common set of traits, domain types, and feature-gated pool implementations covering the six major AMM families found across DeFi. Use it as a foundation to build your own AMM, simulate swap scenarios, or integrate multiple pool types into a single system.

---

## Supported AMM Families

| Family | Invariant / Model | Real-World Examples | Feature Flag |
|--------|-------------------|---------------------|--------------|
| **Constant Product** | x · y = k | Uniswap v2, SushiSwap, Raydium CPMM, PancakeSwap | `constant-product` |
| **Concentrated Liquidity (CLMM)** | Tick-based ranges | Uniswap v3/v4, Orca Whirlpools, Raydium CLMM, Trader Joe LB | `clmm` |
| **Hybrid / StableSwap** | Curve amplified invariant | Curve Finance, Aerodrome/Velodrome, Thorchain | `hybrid` |
| **Weighted Pools** | ∏(Bᵢ^Wᵢ) = k | Balancer 80/20, multi-token pools | `weighted` |
| **Dynamic / Proactive MM** | Oracle-driven pricing | DODO PMM, Meteora DLMM, Lifinity, KyberSwap DMM | `dynamic` |
| **Order Book Hybrid** | CLOB + AMM fallback | Phoenix | `order-book` |

---

## Architecture

The crate is organized into six layers, each building on the previous:

```
┌─────────────────────────────────────────────────┐
│  Layer 5: Factory & Dispatch                    │
│  DefaultPoolFactory · PoolBox enum dispatch     │
├─────────────────────────────────────────────────┤
│  Layer 4: Pool Implementations (feature-gated)  │
│  ConstantProduct · CLMM · Hybrid · Weighted     │
│  Dynamic · OrderBook                            │
├─────────────────────────────────────────────────┤
│  Layer 3: Configuration                         │
│  AmmConfig enum · 6 config structs              │
├─────────────────────────────────────────────────┤
│  Layer 2: Core Traits                           │
│  SwapPool · LiquidityPool · FromConfig          │
├─────────────────────────────────────────────────┤
│  Layer 1: Domain Types                          │
│  Token · Amount · Price · Tick · Position        │
├─────────────────────────────────────────────────┤
│  Layer 0: Math & Precision                      │
│  Precision trait · CheckedArithmetic · Rounding │
└─────────────────────────────────────────────────┘
```

**Key design principles:**

- **Configuration-driven**: Pools are created from declarative `AmmConfig` structs via a factory.
- **Zero-cost abstractions**: Enum dispatch (`PoolBox`) instead of `dyn` trait objects — no vtable overhead.
- **Checked arithmetic**: All operations are explicitly checked for overflow/underflow. No panics in library code.
- **Newtypes everywhere**: `Amount`, `Price`, `Tick`, `FeeTier`, etc. — no raw primitives in public API.
- **Feature-gated**: Each pool type is behind its own Cargo feature. Compile only what you need.

---

## Installation

Add `hydra-amm` to your project:

```bash
cargo add hydra-amm
```

Or add it manually to your `Cargo.toml`:

```toml
[dependencies]
hydra-amm = "0.1"
```

This enables **all pool types** by default. To select only the pool types you need:

```toml
[dependencies]
hydra-amm = { version = "0.1", default-features = false, features = ["std", "constant-product", "clmm"] }
```

---

## Feature Flags

| Feature | Default | Description |
|---------|---------|-------------|
| `std` | ✅ | Standard library support (BTreeMap storage, Display impls) |
| `fixed-point` | ❌ | I80F48 fixed-point arithmetic via the [`fixed`](https://crates.io/crates/fixed) crate |
| `float` | ❌ | f64 floating-point arithmetic (implies `std`) |
| `constant-product` | ✅ | Constant product (x·y=k) pool |
| `clmm` | ✅ | Concentrated Liquidity Market Maker pool |
| `hybrid` | ✅ | Hybrid / StableSwap pool (Curve-style) |
| `weighted` | ✅ | Weighted pool (Balancer-style) |
| `dynamic` | ✅ | Dynamic / Proactive Market Maker pool (DODO-style) |
| `order-book` | ✅ | Order Book Hybrid pool (uses [`orderbook-rs`](https://crates.io/crates/orderbook-rs)) |
| `all-pools` | ✅ | Convenience: enables all six pool types |

### Minimal Dependency Example

For an on-chain environment that only needs constant-product swaps with fixed-point math:

```toml
[dependencies]
hydra-amm = { version = "0.1", default-features = false, features = ["fixed-point", "constant-product"] }
```

---

## Quick Start

### Creating a Constant Product Pool and Executing a Swap

```rust
use hydra_amm::config::{AmmConfig, ConstantProductConfig};
use hydra_amm::domain::{
    Amount, BasisPoints, Decimals, FeeTier, SwapSpec,
    Token, TokenAddress, TokenPair,
};
use hydra_amm::factory::DefaultPoolFactory;
use hydra_amm::traits::SwapPool;

// 1. Define two tokens (32-byte addresses + decimal precision)
let usdc = Token::new(
    TokenAddress::from_bytes([1u8; 32]),
    Decimals::new(6).expect("valid decimals"),
);
let weth = Token::new(
    TokenAddress::from_bytes([2u8; 32]),
    Decimals::new(18).expect("valid decimals"),
);

// 2. Build a Constant Product pool configuration
let pair = TokenPair::new(usdc, weth).expect("distinct tokens");
let fee  = FeeTier::new(BasisPoints::new(30)); // 0.30% fee
let config = AmmConfig::ConstantProduct(
    ConstantProductConfig::new(pair, fee, Amount::new(1_000_000), Amount::new(1_000_000))
        .expect("valid config"),
);

// 3. Create the pool via the factory
let mut pool = DefaultPoolFactory::create(&config).expect("pool created");

// 4. Execute a swap (sell 10 000 units of token A for token B)
let spec = SwapSpec::exact_in(Amount::new(10_000)).expect("non-zero amount");
let result = pool.swap(spec, usdc).expect("swap succeeded");

assert!(result.amount_out().get() > 0);
assert!(result.fee().get() > 0);
```

### Advanced: CLMM Pool with Concentrated Liquidity Positions

```rust
use hydra_amm::config::{AmmConfig, ClmmConfig};
use hydra_amm::domain::{
    Amount, BasisPoints, Decimals, FeeTier, Liquidity, LiquidityChange,
    Position, SwapSpec, Tick, Token, TokenAddress, TokenPair,
};
use hydra_amm::factory::DefaultPoolFactory;
use hydra_amm::traits::{LiquidityPool, SwapPool};

// 1. Define tokens
let tok_a = Token::new(TokenAddress::from_bytes([1u8; 32]), Decimals::new(6).expect("ok"));
let tok_b = Token::new(TokenAddress::from_bytes([2u8; 32]), Decimals::new(18).expect("ok"));
let pair  = TokenPair::new(tok_a, tok_b).expect("distinct");

// 2. Configure a CLMM pool at tick 0, tick spacing 10
let fee = FeeTier::new(BasisPoints::new(30));
let initial_position = Position::new(
    Tick::new(-100).expect("valid tick"),
    Tick::new(100).expect("valid tick"),
    Liquidity::new(1_000_000),
).expect("valid position");

let config = AmmConfig::Clmm(
    ClmmConfig::new(
        pair,
        fee,
        10,                                  // tick spacing
        Tick::new(0).expect("valid tick"),    // current tick
        vec![initial_position],              // initial positions
    ).expect("valid config"),
);

// 3. Create pool and add more liquidity
let mut pool = DefaultPoolFactory::create(&config).expect("pool created");
let add = LiquidityChange::add(Amount::new(500_000), Amount::new(500_000))
    .expect("valid change");
let _ = pool.add_liquidity(&add);

// 4. Execute a swap
let spec = SwapSpec::exact_in(Amount::new(1_000)).expect("non-zero");
let result = pool.swap(spec, tok_a).expect("swap ok");
assert!(result.amount_out().get() > 0);
```

### Implementing a Custom Pool

Implement the `SwapPool` trait for your own AMM type:

```rust,ignore
use hydra_amm::traits::SwapPool;
use hydra_amm::domain::{FeeTier, Price, SwapResult, SwapSpec, Token, TokenPair};
use hydra_amm::error::AmmError;

struct MyCustomPool {
    pair: TokenPair,
    fee: FeeTier,
    // your state here
}

impl SwapPool for MyCustomPool {
    fn swap(&mut self, spec: SwapSpec, token_in: Token) -> Result<SwapResult, AmmError> {
        // your swap logic — apply fee, compute output, update reserves
        todo!()
    }

    fn spot_price(&self, base: &Token, quote: &Token) -> Result<Price, AmmError> {
        // return the current exchange rate (quote per base)
        todo!()
    }

    fn token_pair(&self) -> &TokenPair {
        &self.pair
    }

    fn fee_tier(&self) -> FeeTier {
        self.fee
    }
}
```

---

## Module Structure

```
hydra_amm/
├── error       — AmmError enum (code ranges 1000-4999)
├── domain      — Token, Amount, Price, Tick, Position, SwapSpec, SwapResult, ...
├── math        — Precision trait, CheckedArithmetic, Rounding, tick math
├── traits      — SwapPool, LiquidityPool, FromConfig
├── config      — AmmConfig enum + per-pool config structs
├── pools       — Feature-gated pool implementations + PoolBox dispatch enum
├── factory     — DefaultPoolFactory::create()
└── prelude     — Convenience re-exports for common types and traits
```

---

## Safety and Correctness

This crate prioritizes correctness above all:

- **`unsafe` code is denied** — enforced at the compiler level
- **No `.unwrap()` / `.expect()` / `panic!`** — denied via Clippy lints in library code
- **Checked arithmetic** — all operations return `Option` or `Result`
- **Explicit rounding** — all divisions specify rounding direction (up or down, always against the user)
- **Overflow checks** enabled in both debug and release profiles
- **Property-based testing** with `proptest` for invariant validation
- **30 doc-tests** — all code examples in documentation are compiled and executed

---

## API Reference

Full API documentation is available on [docs.rs/hydra-amm](https://docs.rs/hydra-amm).

---

## Development

### Prerequisites

- Rust (edition 2024, see `rust-toolchain.toml`)
- Make

### Common Commands

```bash
# Build
make build                   # Debug build
make release                 # Release build

# Test
make test                    # Run all tests with all features
make test-lib                # Library tests only
make test-doc                # Documentation tests

# Quality
make fmt                     # Format code
make lint                    # Run clippy (strict)
make lint-fix                # Auto-fix lint issues
make check                   # fmt-check + lint + test
make pre-push                # Full pre-push validation

# Documentation
make doc                     # Generate docs
make doc-open                # Generate and open in browser

# Coverage
make coverage                # Generate XML coverage report
make coverage-html           # Generate HTML coverage report

# Benchmarks
make bench                   # Run criterion benchmarks
```

### Pre-Push Checklist

Always run before pushing:

```bash
make pre-push
```

This executes: `cargo fix` → `cargo fmt` → `cargo clippy` → `cargo test` → `cargo doc`

---

## AMM Classification

The following diagram shows the AMM landscape covered by this crate:

```
Automated Market Makers
├── Constant Product (x·y=k)
│   ├── Uniswap v2
│   ├── SushiSwap
│   ├── QuickSwap
│   ├── Raydium (CPMM)
│   └── PancakeSwap
├── Concentrated Liquidity (CLMM)
│   ├── Uniswap v3 / v4
│   ├── Orca (Whirlpools)
│   ├── Raydium (CLMM)
│   ├── Trader Joe (Liquidity Book)
│   ├── Maverick
│   ├── Ambient Finance
│   ├── Cetus Protocol
│   ├── Camelot
│   └── iZUMi (DL-AMM)
├── Hybrid / StableSwap
│   ├── Curve Finance
│   ├── Aerodrome / Velodrome
│   └── Thorchain (Orbital Pools)
├── Weighted Pools
│   └── Balancer (80/20, multi-token)
├── Dynamic / Proactive MM
│   ├── DODO (PMM)
│   ├── Meteora (DLMM)
│   ├── Lifinity
│   └── KyberSwap (DMM)
└── Order Book Hybrid
    └── Phoenix (CLOB on Solana)
```

---

## Contributing

Contributions are welcome! Please follow these guidelines:

1. **Fork** the repository and create a feature branch
2. **Read** the documentation in `.internalDoc/` (especially `09-RUST-GUIDELINES.md`)
3. **Write tests** for all new public functions
4. **Run** `make pre-push` before submitting
5. **Create** a PR with a clear description

### Code Standards

- All comments and documentation in **English**
- `///` doc comments on every public item
- `#[must_use]` on all pure functions
- Checked arithmetic only — no panics in library code
- Newtypes for all domain concepts

---

## License

This project is licensed under the MIT License — see the [LICENSE](LICENSE) file for details.

---

## Contact

- **Author**: Joaquín Béjar García
- **Email**: jb@taunais.com
- **Telegram**: [@joaquin_bejar](https://t.me/joaquin_bejar)
- **Repository**: [github.com/joaquinbejar/hydra-amm](https://github.com/joaquinbejar/hydra-amm)
- **Crates.io**: [crates.io/crates/hydra-amm](https://crates.io/crates/hydra-amm)
- **Documentation**: [docs.rs/hydra-amm](https://docs.rs/hydra-amm)
