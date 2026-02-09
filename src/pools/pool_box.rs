//! Enum dispatch wrapper for all pool types.
//!
//! [`PoolBox`] wraps every concrete pool implementation behind a single
//! enum, enabling heterogeneous collections and zero-cost static
//! dispatch.  Each variant is feature-gated to match its pool type.

#[cfg(feature = "clmm")]
use super::clmm::ClmmPool;
#[cfg(feature = "constant-product")]
use super::constant_product::ConstantProductPool;
#[cfg(feature = "dynamic")]
use super::dynamic::DynamicPool;
#[cfg(feature = "hybrid")]
use super::hybrid::HybridPool;
#[cfg(feature = "order-book")]
use super::order_book::OrderBookPool;
#[cfg(feature = "weighted")]
use super::weighted::WeightedPool;

use crate::domain::{
    Amount, FeeTier, Liquidity, LiquidityChange, Position, Price, SwapResult, SwapSpec, Token,
    TokenPair,
};
use crate::error::AmmError;
use crate::traits::{LiquidityPool, SwapPool};

/// Zero-cost dispatch enum wrapping all concrete pool implementations.
///
/// Each variant is feature-gated behind its respective Cargo feature
/// flag.  The enum implements [`SwapPool`] and [`LiquidityPool`] by
/// delegating every method call to the inner pool via `match`.
///
/// # Advantages
///
/// - **Zero-overhead dispatch**: no vtable, no dynamic allocation at
///   call time.
/// - **`no_std` compatible**: works without an allocator for vtable
///   management.
/// - **Exhaustive matching**: the compiler ensures all variants are
///   handled in every `match` expression.
/// - **Closed type set**: pool types are fixed at compile time.
///
/// # Example
///
/// ```text
/// let pool_box = PoolBox::ConstantProduct(Box::new(cp_pool));
/// let pair = pool_box.token_pair();
/// ```
#[derive(Debug)]
pub enum PoolBox {
    /// Constant Product AMM (Uniswap V2 style).
    #[cfg(feature = "constant-product")]
    ConstantProduct(Box<ConstantProductPool>),

    /// Concentrated Liquidity Market Maker (Uniswap V3 style).
    #[cfg(feature = "clmm")]
    Clmm(Box<ClmmPool>),

    /// Hybrid / StableSwap (Curve style).
    #[cfg(feature = "hybrid")]
    Hybrid(Box<HybridPool>),

    /// Weighted pool (Balancer style).
    #[cfg(feature = "weighted")]
    Weighted(Box<WeightedPool>),

    /// Dynamic / Proactive Market Maker (DODO style).
    #[cfg(feature = "dynamic")]
    Dynamic(Box<DynamicPool>),

    /// Order Book hybrid (Phoenix style).
    #[cfg(feature = "order-book")]
    OrderBook(Box<OrderBookPool>),
}

/// Helper macro to delegate a method call to every PoolBox variant.
///
/// Generates a match arm for each feature-gated variant, calling the
/// same method on the inner pool.
macro_rules! delegate {
    ($self:ident, $method:ident ( $($arg:expr),* )) => {
        match $self {
            #[cfg(feature = "constant-product")]
            PoolBox::ConstantProduct(p) => p.$method($($arg),*),
            #[cfg(feature = "clmm")]
            PoolBox::Clmm(p) => p.$method($($arg),*),
            #[cfg(feature = "hybrid")]
            PoolBox::Hybrid(p) => p.$method($($arg),*),
            #[cfg(feature = "weighted")]
            PoolBox::Weighted(p) => p.$method($($arg),*),
            #[cfg(feature = "dynamic")]
            PoolBox::Dynamic(p) => p.$method($($arg),*),
            #[cfg(feature = "order-book")]
            PoolBox::OrderBook(p) => p.$method($($arg),*),
        }
    };
}

impl SwapPool for PoolBox {
    fn swap(&mut self, spec: SwapSpec, token_in: Token) -> Result<SwapResult, AmmError> {
        delegate!(self, swap(spec, token_in))
    }

    fn spot_price(&self, base: &Token, quote: &Token) -> Result<Price, AmmError> {
        delegate!(self, spot_price(base, quote))
    }

    fn token_pair(&self) -> &TokenPair {
        delegate!(self, token_pair())
    }

    fn fee_tier(&self) -> FeeTier {
        delegate!(self, fee_tier())
    }
}

impl LiquidityPool for PoolBox {
    fn add_liquidity(&mut self, change: &LiquidityChange) -> Result<Amount, AmmError> {
        delegate!(self, add_liquidity(change))
    }

    fn remove_liquidity(&mut self, change: &LiquidityChange) -> Result<Amount, AmmError> {
        delegate!(self, remove_liquidity(change))
    }

    fn collect_fees(&mut self, position: &Position) -> Result<Amount, AmmError> {
        delegate!(self, collect_fees(position))
    }

    fn total_liquidity(&self) -> Liquidity {
        delegate!(self, total_liquidity())
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;
    use crate::domain::{BasisPoints, Decimals, Token, TokenAddress};
    use crate::traits::FromConfig;

    // -- helpers --------------------------------------------------------------

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

    fn fee() -> crate::domain::FeeTier {
        crate::domain::FeeTier::new(BasisPoints::new(30))
    }

    // -- ConstantProduct via PoolBox ------------------------------------------

    #[cfg(feature = "constant-product")]
    mod constant_product_tests {
        use super::*;
        use crate::config::ConstantProductConfig;

        fn make_cp_pool_box() -> PoolBox {
            let Ok(cfg) = ConstantProductConfig::new(
                make_pair(),
                fee(),
                crate::domain::Amount::new(1_000),
                crate::domain::Amount::new(2_000),
            ) else {
                panic!("expected valid config");
            };
            let Ok(pool) = ConstantProductPool::from_config(&cfg) else {
                panic!("expected valid pool");
            };
            PoolBox::ConstantProduct(Box::new(pool))
        }

        #[test]
        fn token_pair_delegation() {
            let pb = make_cp_pool_box();
            assert_eq!(*pb.token_pair(), make_pair());
        }

        #[test]
        fn fee_tier_delegation() {
            let pb = make_cp_pool_box();
            assert_eq!(pb.fee_tier(), fee());
        }

        #[test]
        fn total_liquidity_delegation() {
            let pb = make_cp_pool_box();
            assert_eq!(pb.total_liquidity(), Liquidity::ZERO);
        }

        #[test]
        fn swap_returns_not_implemented() {
            let mut pb = make_cp_pool_box();
            let Ok(d6) = Decimals::new(6) else {
                panic!("valid decimals");
            };
            let tok = Token::new(TokenAddress::from_bytes([1u8; 32]), d6);
            let Ok(spec) = SwapSpec::exact_in(crate::domain::Amount::new(100)) else {
                panic!("expected valid spec");
            };
            let result = pb.swap(spec, tok);
            assert!(result.is_err());
        }

        #[test]
        fn debug_format_contains_variant() {
            let pb = make_cp_pool_box();
            let dbg = format!("{pb:?}");
            assert!(dbg.contains("ConstantProduct"));
        }
    }

    // -- Clmm via PoolBox -----------------------------------------------------

    #[cfg(feature = "clmm")]
    mod clmm_tests {
        use super::*;
        use crate::config::ClmmConfig;
        use crate::domain::Tick;

        fn make_clmm_pool_box() -> PoolBox {
            let Ok(t) = Tick::new(0) else {
                panic!("valid tick");
            };
            let Ok(cfg) = ClmmConfig::new(make_pair(), fee(), 10, t, vec![]) else {
                panic!("expected valid config");
            };
            let Ok(pool) = ClmmPool::from_config(&cfg) else {
                panic!("expected valid pool");
            };
            PoolBox::Clmm(Box::new(pool))
        }

        #[test]
        fn token_pair_delegation() {
            let pb = make_clmm_pool_box();
            assert_eq!(*pb.token_pair(), make_pair());
        }

        #[test]
        fn fee_tier_delegation() {
            let pb = make_clmm_pool_box();
            assert_eq!(pb.fee_tier(), fee());
        }

        #[test]
        fn total_liquidity_delegation() {
            let pb = make_clmm_pool_box();
            assert_eq!(pb.total_liquidity(), Liquidity::ZERO);
        }
    }

    // -- Hybrid via PoolBox ---------------------------------------------------

    #[cfg(feature = "hybrid")]
    mod hybrid_tests {
        use super::*;
        use crate::config::HybridConfig;

        fn make_hybrid_pool_box() -> PoolBox {
            let Ok(cfg) = HybridConfig::new(
                make_pair(),
                fee(),
                100,
                crate::domain::Amount::new(1_000),
                crate::domain::Amount::new(1_000),
            ) else {
                panic!("expected valid config");
            };
            let Ok(pool) = HybridPool::from_config(&cfg) else {
                panic!("expected valid pool");
            };
            PoolBox::Hybrid(Box::new(pool))
        }

        #[test]
        fn token_pair_delegation() {
            let pb = make_hybrid_pool_box();
            assert_eq!(*pb.token_pair(), make_pair());
        }

        #[test]
        fn fee_tier_delegation() {
            let pb = make_hybrid_pool_box();
            assert_eq!(pb.fee_tier(), fee());
        }
    }

    // -- Dynamic via PoolBox --------------------------------------------------

    #[cfg(feature = "dynamic")]
    mod dynamic_tests {
        use super::*;
        use crate::config::DynamicConfig;

        fn make_dynamic_pool_box() -> PoolBox {
            let Ok(p) = crate::domain::Price::new(100.0) else {
                panic!("valid price");
            };
            let Ok(cfg) = DynamicConfig::new(
                make_pair(),
                fee(),
                p,
                0.5,
                crate::domain::Amount::new(1_000),
                crate::domain::Amount::new(1_000),
            ) else {
                panic!("expected valid config");
            };
            let Ok(pool) = DynamicPool::from_config(&cfg) else {
                panic!("expected valid pool");
            };
            PoolBox::Dynamic(Box::new(pool))
        }

        #[test]
        fn token_pair_delegation() {
            let pb = make_dynamic_pool_box();
            assert_eq!(*pb.token_pair(), make_pair());
        }

        #[test]
        fn fee_tier_delegation() {
            let pb = make_dynamic_pool_box();
            assert_eq!(pb.fee_tier(), fee());
        }
    }

    // -- OrderBook via PoolBox ------------------------------------------------

    #[cfg(feature = "order-book")]
    mod order_book_tests {
        use super::*;
        use crate::config::OrderBookConfig;

        fn make_ob_pool_box() -> PoolBox {
            let Ok(cfg) = OrderBookConfig::new(
                make_pair(),
                fee(),
                crate::domain::Amount::new(1),
                crate::domain::Amount::new(10),
            ) else {
                panic!("expected valid config");
            };
            let Ok(pool) = OrderBookPool::from_config(&cfg) else {
                panic!("expected valid pool");
            };
            PoolBox::OrderBook(Box::new(pool))
        }

        #[test]
        fn token_pair_delegation() {
            let pb = make_ob_pool_box();
            assert_eq!(*pb.token_pair(), make_pair());
        }

        #[test]
        fn fee_tier_delegation() {
            let pb = make_ob_pool_box();
            assert_eq!(pb.fee_tier(), fee());
        }
    }

    // -- Weighted via PoolBox -------------------------------------------------

    #[cfg(feature = "weighted")]
    mod weighted_tests {
        use super::*;
        use crate::config::WeightedConfig;

        fn make_weighted_pool_box() -> PoolBox {
            let Ok(d6) = Decimals::new(6) else {
                panic!("valid decimals");
            };
            let Ok(d18) = Decimals::new(18) else {
                panic!("valid decimals");
            };
            let tok_a = Token::new(TokenAddress::from_bytes([1u8; 32]), d6);
            let tok_b = Token::new(TokenAddress::from_bytes([2u8; 32]), d18);
            let Ok(cfg) = WeightedConfig::new(
                vec![tok_a, tok_b],
                vec![BasisPoints::new(5_000), BasisPoints::new(5_000)],
                fee(),
                vec![
                    crate::domain::Amount::new(1_000),
                    crate::domain::Amount::new(2_000),
                ],
            ) else {
                panic!("expected valid config");
            };
            let Ok(pool) = WeightedPool::from_config(&cfg) else {
                panic!("expected valid pool");
            };
            PoolBox::Weighted(Box::new(pool))
        }

        #[test]
        fn token_pair_delegation() {
            let pb = make_weighted_pool_box();
            assert_eq!(*pb.token_pair(), make_pair());
        }

        #[test]
        fn fee_tier_delegation() {
            let pb = make_weighted_pool_box();
            assert_eq!(pb.fee_tier(), fee());
        }
    }
}
