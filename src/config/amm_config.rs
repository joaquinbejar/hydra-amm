//! Top-level AMM configuration enum.
//!
//! [`AmmConfig`] is the declarative blueprint for creating any pool type.
//! Each variant wraps a pool-specific configuration struct that fully
//! describes the pool's immutable parameters.
//!
//! # Factory Integration
//!
//! The factory pattern matches on `AmmConfig` to dispatch construction:
//!
//! ```text
//! match config {
//!     AmmConfig::ConstantProduct(cfg) => ConstantProductPool::from_config(&cfg),
//!     AmmConfig::Clmm(cfg)            => ConcentratedLiquidityPool::from_config(&cfg),
//!     ...
//! }
//! ```

use super::{
    ClmmConfig, ConstantProductConfig, DynamicConfig, HybridConfig, OrderBookConfig, WeightedConfig,
};
use crate::error::AmmError;

/// Top-level configuration enum for all AMM pool types.
///
/// Each variant wraps its pool-specific configuration struct.  The enum
/// is used by the factory to determine which pool type to construct and
/// with what parameters.
///
/// # Variants
///
/// - [`ConstantProduct`](AmmConfig::ConstantProduct) — Uniswap V2 style (`x · y = k`)
/// - [`Clmm`](AmmConfig::Clmm) — Uniswap V3 style (concentrated liquidity)
/// - [`Hybrid`](AmmConfig::Hybrid) — Curve-style StableSwap
/// - [`Weighted`](AmmConfig::Weighted) — Balancer-style weighted pools
/// - [`Dynamic`](AmmConfig::Dynamic) — DODO-style proactive market making
/// - [`OrderBook`](AmmConfig::OrderBook) — Phoenix-style order book hybrid
///
/// # Validation
///
/// Call [`validate()`](AmmConfig::validate) to check all configuration
/// invariants before constructing a pool.
#[derive(Debug, Clone, PartialEq)]
pub enum AmmConfig {
    /// Constant Product AMM configuration (Uniswap V2 style).
    ConstantProduct(ConstantProductConfig),
    /// Concentrated Liquidity Market Maker configuration (Uniswap V3 style).
    Clmm(ClmmConfig),
    /// Hybrid / StableSwap configuration (Curve style).
    Hybrid(HybridConfig),
    /// Weighted pool configuration (Balancer style).
    Weighted(WeightedConfig),
    /// Dynamic / Proactive Market Maker configuration (DODO style).
    Dynamic(DynamicConfig),
    /// Order Book hybrid configuration (Phoenix style).
    OrderBook(OrderBookConfig),
}

impl AmmConfig {
    /// Validates the inner configuration by delegating to the
    /// variant-specific `validate()` method.
    ///
    /// # Errors
    ///
    /// Returns the same [`AmmError`] that the inner config's
    /// `validate()` would return.
    pub fn validate(&self) -> Result<(), AmmError> {
        match self {
            Self::ConstantProduct(cfg) => cfg.validate(),
            Self::Clmm(cfg) => cfg.validate(),
            Self::Hybrid(cfg) => cfg.validate(),
            Self::Weighted(cfg) => cfg.validate(),
            Self::Dynamic(cfg) => cfg.validate(),
            Self::OrderBook(cfg) => cfg.validate(),
        }
    }

    /// Returns `true` if this is a [`ConstantProduct`](Self::ConstantProduct) variant.
    #[must_use]
    pub const fn is_constant_product(&self) -> bool {
        matches!(self, Self::ConstantProduct(_))
    }

    /// Returns `true` if this is a [`Clmm`](Self::Clmm) variant.
    #[must_use]
    pub const fn is_clmm(&self) -> bool {
        matches!(self, Self::Clmm(_))
    }

    /// Returns `true` if this is a [`Hybrid`](Self::Hybrid) variant.
    #[must_use]
    pub const fn is_hybrid(&self) -> bool {
        matches!(self, Self::Hybrid(_))
    }

    /// Returns `true` if this is a [`Weighted`](Self::Weighted) variant.
    #[must_use]
    pub const fn is_weighted(&self) -> bool {
        matches!(self, Self::Weighted(_))
    }

    /// Returns `true` if this is a [`Dynamic`](Self::Dynamic) variant.
    #[must_use]
    pub const fn is_dynamic(&self) -> bool {
        matches!(self, Self::Dynamic(_))
    }

    /// Returns `true` if this is an [`OrderBook`](Self::OrderBook) variant.
    #[must_use]
    pub const fn is_order_book(&self) -> bool {
        matches!(self, Self::OrderBook(_))
    }
}

impl core::fmt::Display for AmmConfig {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::ConstantProduct(_) => write!(f, "ConstantProduct"),
            Self::Clmm(_) => write!(f, "Clmm"),
            Self::Hybrid(_) => write!(f, "Hybrid"),
            Self::Weighted(_) => write!(f, "Weighted"),
            Self::Dynamic(_) => write!(f, "Dynamic"),
            Self::OrderBook(_) => write!(f, "OrderBook"),
        }
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;
    use crate::domain::{
        Amount, BasisPoints, Decimals, FeeTier, Price, Tick, Token, TokenAddress, TokenPair,
    };

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

    fn fee() -> FeeTier {
        FeeTier::new(BasisPoints::new(30))
    }

    fn tick(v: i32) -> Tick {
        let Ok(t) = Tick::new(v) else {
            panic!("valid tick expected");
        };
        t
    }

    #[test]
    fn constant_product_variant() {
        let Ok(cfg) =
            ConstantProductConfig::new(make_pair(), fee(), Amount::new(1_000), Amount::new(2_000))
        else {
            panic!("expected Ok");
        };
        let amm = AmmConfig::ConstantProduct(cfg);
        assert!(amm.is_constant_product());
        assert!(!amm.is_clmm());
        assert!(amm.validate().is_ok());
    }

    #[test]
    fn clmm_variant() {
        let Ok(cfg) = ClmmConfig::new(make_pair(), fee(), 10, tick(0), vec![]) else {
            panic!("expected Ok");
        };
        let amm = AmmConfig::Clmm(cfg);
        assert!(amm.is_clmm());
        assert!(amm.validate().is_ok());
    }

    #[test]
    fn hybrid_variant() {
        let Ok(cfg) = HybridConfig::new(
            make_pair(),
            fee(),
            100,
            Amount::new(1_000),
            Amount::new(1_000),
        ) else {
            panic!("expected Ok");
        };
        let amm = AmmConfig::Hybrid(cfg);
        assert!(amm.is_hybrid());
        assert!(amm.validate().is_ok());
    }

    #[test]
    fn weighted_variant() {
        let bps = |v: u32| -> BasisPoints { BasisPoints::new(v) };
        let tok = |byte: u8| -> Token {
            let Ok(d) = Decimals::new(6) else {
                panic!("valid decimals");
            };
            Token::new(TokenAddress::from_bytes([byte; 32]), d)
        };
        let Ok(cfg) = WeightedConfig::new(
            vec![tok(1), tok(2)],
            vec![bps(5_000), bps(5_000)],
            fee(),
            vec![Amount::new(100), Amount::new(200)],
        ) else {
            panic!("expected Ok");
        };
        let amm = AmmConfig::Weighted(cfg);
        assert!(amm.is_weighted());
        assert!(amm.validate().is_ok());
    }

    #[test]
    fn dynamic_variant() {
        let Ok(price) = Price::new(100.0) else {
            panic!("expected valid price");
        };
        let Ok(cfg) = DynamicConfig::new(
            make_pair(),
            fee(),
            price,
            0.5,
            Amount::new(1_000),
            Amount::new(100_000),
        ) else {
            panic!("expected Ok");
        };
        let amm = AmmConfig::Dynamic(cfg);
        assert!(amm.is_dynamic());
        assert!(amm.validate().is_ok());
    }

    #[test]
    fn order_book_variant() {
        let Ok(cfg) = OrderBookConfig::new(make_pair(), fee(), Amount::new(1), Amount::new(10))
        else {
            panic!("expected Ok");
        };
        let amm = AmmConfig::OrderBook(cfg);
        assert!(amm.is_order_book());
        assert!(amm.validate().is_ok());
    }

    #[test]
    fn display_variants() {
        let Ok(cp) = ConstantProductConfig::new(make_pair(), fee(), Amount::new(1), Amount::new(1))
        else {
            panic!("expected Ok");
        };
        assert_eq!(
            format!("{}", AmmConfig::ConstantProduct(cp)),
            "ConstantProduct"
        );

        let Ok(clmm) = ClmmConfig::new(make_pair(), fee(), 1, tick(0), vec![]) else {
            panic!("expected Ok");
        };
        assert_eq!(format!("{}", AmmConfig::Clmm(clmm)), "Clmm");
    }
}
