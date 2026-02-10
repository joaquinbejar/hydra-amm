//! Default pool factory implementation.

use crate::config::AmmConfig;
use crate::error::AmmError;
use crate::pools::PoolBox;

#[cfg(any(
    feature = "constant-product",
    feature = "clmm",
    feature = "hybrid",
    feature = "weighted",
    feature = "dynamic",
    feature = "order-book",
))]
use crate::traits::FromConfig;

/// Stateless factory for creating pool instances from configuration.
///
/// `DefaultPoolFactory` is the single entry point for constructing any
/// AMM pool.  It matches on the [`AmmConfig`] variant, validates the
/// configuration, delegates to the pool's [`FromConfig`] implementation,
/// and wraps the result in a [`PoolBox`].
///
/// # Thread Safety
///
/// [`create`](Self::create) is a pure function with no shared mutable
/// state — it is inherently `Send + Sync`.
///
/// # Example
///
/// ```rust
/// use hydra_amm::config::{AmmConfig, ConstantProductConfig};
/// use hydra_amm::domain::{
///     Amount, BasisPoints, Decimals, FeeTier, Token, TokenAddress, TokenPair,
/// };
/// use hydra_amm::factory::DefaultPoolFactory;
/// use hydra_amm::traits::SwapPool;
///
/// let tok_a = Token::new(TokenAddress::from_bytes([1u8; 32]), Decimals::new(6).expect("valid"));
/// let tok_b = Token::new(TokenAddress::from_bytes([2u8; 32]), Decimals::new(18).expect("valid"));
/// let pair  = TokenPair::new(tok_a, tok_b).expect("distinct");
/// let fee   = FeeTier::new(BasisPoints::new(30));
///
/// let config = AmmConfig::ConstantProduct(
///     ConstantProductConfig::new(pair, fee, Amount::new(1_000_000), Amount::new(1_000_000))
///         .expect("valid config"),
/// );
///
/// let pool = DefaultPoolFactory::create(&config).expect("pool created");
/// assert_eq!(*pool.token_pair(), pair);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DefaultPoolFactory;

impl DefaultPoolFactory {
    /// Creates a new pool instance from the given configuration.
    ///
    /// # Flow
    ///
    /// 1. Validate the configuration via [`AmmConfig::validate`].
    /// 2. Match on the config variant.
    /// 3. Delegate to the pool's [`FromConfig`] implementation.
    /// 4. Wrap the constructed pool in the corresponding [`PoolBox`]
    ///    variant.
    ///
    /// # Arguments
    ///
    /// - `config` — immutable reference to the AMM configuration.
    ///
    /// # Errors
    ///
    /// - [`AmmError::InvalidConfiguration`] if the configuration is
    ///   invalid or if the requested pool type's feature is not enabled.
    /// - Any error propagated from the pool's `from_config` method.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hydra_amm::config::{AmmConfig, ConstantProductConfig};
    /// use hydra_amm::domain::{
    ///     Amount, BasisPoints, Decimals, FeeTier, SwapSpec,
    ///     Token, TokenAddress, TokenPair,
    /// };
    /// use hydra_amm::factory::DefaultPoolFactory;
    /// use hydra_amm::traits::SwapPool;
    ///
    /// let tok_a = Token::new(TokenAddress::from_bytes([1u8; 32]), Decimals::new(6).expect("ok"));
    /// let tok_b = Token::new(TokenAddress::from_bytes([2u8; 32]), Decimals::new(18).expect("ok"));
    /// let pair  = TokenPair::new(tok_a, tok_b).expect("distinct");
    /// let fee   = FeeTier::new(BasisPoints::new(30));
    /// let cfg   = ConstantProductConfig::new(pair, fee, Amount::new(1_000_000), Amount::new(1_000_000))
    ///     .expect("valid");
    ///
    /// let mut pool = DefaultPoolFactory::create(&AmmConfig::ConstantProduct(cfg))
    ///     .expect("pool created");
    ///
    /// let spec   = SwapSpec::exact_in(Amount::new(1_000)).expect("non-zero");
    /// let result = pool.swap(spec, tok_a).expect("swap ok");
    /// assert!(result.amount_out().get() > 0);
    /// ```
    pub fn create(config: &AmmConfig) -> Result<PoolBox, AmmError> {
        config.validate()?;

        match config {
            #[cfg(feature = "constant-product")]
            AmmConfig::ConstantProduct(cfg) => {
                let pool = crate::pools::constant_product::ConstantProductPool::from_config(cfg)?;
                Ok(PoolBox::ConstantProduct(Box::new(pool)))
            }

            #[cfg(feature = "clmm")]
            AmmConfig::Clmm(cfg) => {
                let pool = crate::pools::clmm::ClmmPool::from_config(cfg)?;
                Ok(PoolBox::Clmm(Box::new(pool)))
            }

            #[cfg(feature = "hybrid")]
            AmmConfig::Hybrid(cfg) => {
                let pool = crate::pools::hybrid::HybridPool::from_config(cfg)?;
                Ok(PoolBox::Hybrid(Box::new(pool)))
            }

            #[cfg(feature = "weighted")]
            AmmConfig::Weighted(cfg) => {
                let pool = crate::pools::weighted::WeightedPool::from_config(cfg)?;
                Ok(PoolBox::Weighted(Box::new(pool)))
            }

            #[cfg(feature = "dynamic")]
            AmmConfig::Dynamic(cfg) => {
                let pool = crate::pools::dynamic::DynamicPool::from_config(cfg)?;
                Ok(PoolBox::Dynamic(Box::new(pool)))
            }

            #[cfg(feature = "order-book")]
            AmmConfig::OrderBook(cfg) => {
                let pool = crate::pools::order_book::OrderBookPool::from_config(cfg)?;
                Ok(PoolBox::OrderBook(Box::new(pool)))
            }

            // Catch-all for config variants whose pool feature is disabled.
            #[allow(unreachable_patterns)]
            _ => Err(AmmError::InvalidConfiguration(
                "requested pool type is not enabled (missing feature flag)",
            )),
        }
    }
}

#[cfg(test)]
#[allow(clippy::panic, unused_imports, dead_code)]
mod tests {
    use super::*;
    use crate::config::{
        ClmmConfig, ConstantProductConfig, DynamicConfig, HybridConfig, OrderBookConfig,
        WeightedConfig,
    };
    use crate::domain::{
        Amount, BasisPoints, Decimals, FeeTier, Liquidity, Price, SwapSpec, Tick, Token,
        TokenAddress, TokenPair,
    };
    use crate::traits::{LiquidityPool, SwapPool};

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

    fn token_a() -> Token {
        let Ok(d6) = Decimals::new(6) else {
            panic!("valid decimals");
        };
        Token::new(TokenAddress::from_bytes([1u8; 32]), d6)
    }

    fn fee() -> FeeTier {
        FeeTier::new(BasisPoints::new(30))
    }

    fn tick(v: i32) -> Tick {
        let Ok(t) = Tick::new(v) else {
            panic!("valid tick");
        };
        t
    }

    // -- ConstantProduct via factory ------------------------------------------

    #[cfg(feature = "constant-product")]
    mod constant_product_tests {
        use super::*;

        fn cp_config() -> AmmConfig {
            let Ok(cfg) = ConstantProductConfig::new(
                make_pair(),
                fee(),
                Amount::new(1_000_000),
                Amount::new(2_000_000),
            ) else {
                panic!("expected valid config");
            };
            AmmConfig::ConstantProduct(cfg)
        }

        #[test]
        fn create_constant_product() {
            let pool = DefaultPoolFactory::create(&cp_config());
            assert!(pool.is_ok());
        }

        #[test]
        fn created_pool_has_correct_pair() {
            let Ok(pool) = DefaultPoolFactory::create(&cp_config()) else {
                panic!("expected Ok");
            };
            assert_eq!(*pool.token_pair(), make_pair());
        }

        #[test]
        fn created_pool_has_correct_fee() {
            let Ok(pool) = DefaultPoolFactory::create(&cp_config()) else {
                panic!("expected Ok");
            };
            assert_eq!(pool.fee_tier(), fee());
        }

        #[test]
        fn created_pool_has_liquidity() {
            let Ok(pool) = DefaultPoolFactory::create(&cp_config()) else {
                panic!("expected Ok");
            };
            assert!(pool.total_liquidity().get() > 0);
        }

        #[test]
        fn factory_round_trip_swap() {
            let Ok(mut pool) = DefaultPoolFactory::create(&cp_config()) else {
                panic!("expected Ok");
            };
            let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
                panic!("valid spec");
            };
            let result = pool.swap(spec, token_a());
            assert!(result.is_ok());
            let Ok(sr) = result else {
                panic!("expected Ok");
            };
            assert!(sr.amount_out().get() > 0);
            assert!(sr.fee().get() > 0);
        }

        #[test]
        fn invalid_cp_config_rejected() {
            // Zero reserves → invalid
            let Ok(cfg) =
                ConstantProductConfig::new(make_pair(), fee(), Amount::ZERO, Amount::new(1_000))
            else {
                // Config constructor may reject this already
                return;
            };
            let amm = AmmConfig::ConstantProduct(cfg);
            let result = DefaultPoolFactory::create(&amm);
            assert!(result.is_err());
        }
    }

    // -- CLMM via factory -----------------------------------------------------

    #[cfg(feature = "clmm")]
    mod clmm_tests {
        use super::*;

        fn clmm_config() -> AmmConfig {
            let Ok(cfg) = ClmmConfig::new(make_pair(), fee(), 10, tick(0), vec![]) else {
                panic!("expected valid config");
            };
            AmmConfig::Clmm(cfg)
        }

        #[test]
        fn create_clmm() {
            let pool = DefaultPoolFactory::create(&clmm_config());
            assert!(pool.is_ok());
        }

        #[test]
        fn clmm_pool_has_correct_pair() {
            let Ok(pool) = DefaultPoolFactory::create(&clmm_config()) else {
                panic!("expected Ok");
            };
            assert_eq!(*pool.token_pair(), make_pair());
        }

        #[test]
        fn clmm_pool_starts_empty() {
            let Ok(pool) = DefaultPoolFactory::create(&clmm_config()) else {
                panic!("expected Ok");
            };
            assert_eq!(pool.total_liquidity(), Liquidity::ZERO);
        }
    }

    // -- Hybrid via factory ---------------------------------------------------

    #[cfg(feature = "hybrid")]
    mod hybrid_tests {
        use super::*;

        fn hybrid_config() -> AmmConfig {
            let Ok(cfg) = HybridConfig::new(
                make_pair(),
                fee(),
                100,
                Amount::new(1_000_000),
                Amount::new(1_000_000),
            ) else {
                panic!("expected valid config");
            };
            AmmConfig::Hybrid(cfg)
        }

        #[test]
        fn create_hybrid() {
            let pool = DefaultPoolFactory::create(&hybrid_config());
            assert!(pool.is_ok());
        }

        #[test]
        fn hybrid_pool_has_correct_pair() {
            let Ok(pool) = DefaultPoolFactory::create(&hybrid_config()) else {
                panic!("expected Ok");
            };
            assert_eq!(*pool.token_pair(), make_pair());
        }

        #[test]
        fn hybrid_round_trip_swap() {
            let Ok(mut pool) = DefaultPoolFactory::create(&hybrid_config()) else {
                panic!("expected Ok");
            };
            let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
                panic!("valid spec");
            };
            let result = pool.swap(spec, token_a());
            assert!(result.is_ok());
        }
    }

    // -- Weighted via factory -------------------------------------------------

    #[cfg(feature = "weighted")]
    mod weighted_tests {
        use super::*;

        fn weighted_config() -> AmmConfig {
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
                vec![Amount::new(1_000_000), Amount::new(2_000_000)],
            ) else {
                panic!("expected valid config");
            };
            AmmConfig::Weighted(cfg)
        }

        #[test]
        fn create_weighted() {
            let pool = DefaultPoolFactory::create(&weighted_config());
            assert!(pool.is_ok());
        }

        #[test]
        fn weighted_pool_has_correct_fee() {
            let Ok(pool) = DefaultPoolFactory::create(&weighted_config()) else {
                panic!("expected Ok");
            };
            assert_eq!(pool.fee_tier(), fee());
        }

        #[test]
        fn weighted_round_trip_swap() {
            let Ok(mut pool) = DefaultPoolFactory::create(&weighted_config()) else {
                panic!("expected Ok");
            };
            let Ok(d6) = Decimals::new(6) else {
                panic!("valid decimals");
            };
            let tok = Token::new(TokenAddress::from_bytes([1u8; 32]), d6);
            let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
                panic!("valid spec");
            };
            let result = pool.swap(spec, tok);
            assert!(result.is_ok());
        }
    }

    // -- Dynamic via factory --------------------------------------------------

    #[cfg(feature = "dynamic")]
    mod dynamic_tests {
        use super::*;

        fn dynamic_config() -> AmmConfig {
            let Ok(price) = Price::new(100.0) else {
                panic!("valid price");
            };
            let Ok(cfg) = DynamicConfig::new(
                make_pair(),
                fee(),
                price,
                0.5,
                Amount::new(1_000_000),
                Amount::new(100_000_000),
            ) else {
                panic!("expected valid config");
            };
            AmmConfig::Dynamic(cfg)
        }

        #[test]
        fn create_dynamic() {
            let pool = DefaultPoolFactory::create(&dynamic_config());
            assert!(pool.is_ok());
        }

        #[test]
        fn dynamic_pool_has_correct_pair() {
            let Ok(pool) = DefaultPoolFactory::create(&dynamic_config()) else {
                panic!("expected Ok");
            };
            assert_eq!(*pool.token_pair(), make_pair());
        }

        #[test]
        fn dynamic_round_trip_swap() {
            let Ok(mut pool) = DefaultPoolFactory::create(&dynamic_config()) else {
                panic!("expected Ok");
            };
            let Ok(spec) = SwapSpec::exact_in(Amount::new(1_000)) else {
                panic!("valid spec");
            };
            let result = pool.swap(spec, token_a());
            assert!(result.is_ok());
        }
    }

    // -- OrderBook via factory ------------------------------------------------

    #[cfg(feature = "order-book")]
    mod order_book_tests {
        use super::*;

        fn ob_config() -> AmmConfig {
            let Ok(cfg) = OrderBookConfig::new(make_pair(), fee(), Amount::new(1), Amount::new(1))
            else {
                panic!("expected valid config");
            };
            AmmConfig::OrderBook(cfg)
        }

        #[test]
        fn create_order_book() {
            let pool = DefaultPoolFactory::create(&ob_config());
            assert!(pool.is_ok());
        }

        #[test]
        fn order_book_starts_empty() {
            let Ok(pool) = DefaultPoolFactory::create(&ob_config()) else {
                panic!("expected Ok");
            };
            assert_eq!(pool.total_liquidity(), Liquidity::ZERO);
        }

        #[test]
        fn order_book_has_correct_fee() {
            let Ok(pool) = DefaultPoolFactory::create(&ob_config()) else {
                panic!("expected Ok");
            };
            assert_eq!(pool.fee_tier(), fee());
        }
    }

    // -- Cross-pool: multi-pool factory creation ------------------------------

    #[test]
    #[cfg(all(
        feature = "constant-product",
        feature = "clmm",
        feature = "hybrid",
        feature = "weighted",
        feature = "dynamic",
        feature = "order-book",
    ))]
    fn create_all_pool_types() {
        // ConstantProduct
        let Ok(cp_cfg) = ConstantProductConfig::new(
            make_pair(),
            fee(),
            Amount::new(1_000_000),
            Amount::new(2_000_000),
        ) else {
            panic!("expected valid config");
        };
        assert!(DefaultPoolFactory::create(&AmmConfig::ConstantProduct(cp_cfg)).is_ok());

        // CLMM
        let Ok(clmm_cfg) = ClmmConfig::new(make_pair(), fee(), 10, tick(0), vec![]) else {
            panic!("expected valid config");
        };
        assert!(DefaultPoolFactory::create(&AmmConfig::Clmm(clmm_cfg)).is_ok());

        // Hybrid
        let Ok(hybrid_cfg) = HybridConfig::new(
            make_pair(),
            fee(),
            100,
            Amount::new(1_000_000),
            Amount::new(1_000_000),
        ) else {
            panic!("expected valid config");
        };
        assert!(DefaultPoolFactory::create(&AmmConfig::Hybrid(hybrid_cfg)).is_ok());

        // Weighted
        let Ok(d6) = Decimals::new(6) else {
            panic!("valid decimals");
        };
        let Ok(d18) = Decimals::new(18) else {
            panic!("valid decimals");
        };
        let tok_a = Token::new(TokenAddress::from_bytes([1u8; 32]), d6);
        let tok_b = Token::new(TokenAddress::from_bytes([2u8; 32]), d18);
        let Ok(w_cfg) = WeightedConfig::new(
            vec![tok_a, tok_b],
            vec![BasisPoints::new(5_000), BasisPoints::new(5_000)],
            fee(),
            vec![Amount::new(1_000_000), Amount::new(2_000_000)],
        ) else {
            panic!("expected valid config");
        };
        assert!(DefaultPoolFactory::create(&AmmConfig::Weighted(w_cfg)).is_ok());

        // Dynamic
        let Ok(price) = Price::new(100.0) else {
            panic!("valid price");
        };
        let Ok(dyn_cfg) = DynamicConfig::new(
            make_pair(),
            fee(),
            price,
            0.5,
            Amount::new(1_000_000),
            Amount::new(100_000_000),
        ) else {
            panic!("expected valid config");
        };
        assert!(DefaultPoolFactory::create(&AmmConfig::Dynamic(dyn_cfg)).is_ok());

        // OrderBook
        let Ok(ob_cfg) = OrderBookConfig::new(make_pair(), fee(), Amount::new(1), Amount::new(1))
        else {
            panic!("expected valid config");
        };
        assert!(DefaultPoolFactory::create(&AmmConfig::OrderBook(ob_cfg)).is_ok());
    }

    // -- Integration: factory round-trip (create → swap → verify) -------------

    #[test]
    #[cfg(feature = "constant-product")]
    fn integration_factory_round_trip() {
        let Ok(cfg) = ConstantProductConfig::new(
            make_pair(),
            fee(),
            Amount::new(1_000_000),
            Amount::new(2_000_000),
        ) else {
            panic!("expected valid config");
        };
        let config = AmmConfig::ConstantProduct(cfg);

        // Step 1: Factory creates pool
        let Ok(mut pool) = DefaultPoolFactory::create(&config) else {
            panic!("expected Ok");
        };

        // Step 2: Verify initial state
        assert_eq!(*pool.token_pair(), make_pair());
        assert_eq!(pool.fee_tier(), fee());
        let initial_liq = pool.total_liquidity();
        assert!(initial_liq.get() > 0);

        // Step 3: Execute swap
        let Ok(spec) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(sr) = pool.swap(spec, token_a()) else {
            panic!("expected Ok swap");
        };

        // Step 4: Verify swap result
        assert!(sr.amount_out().get() > 0);
        assert!(sr.fee().get() > 0);
        // Fee should be approximately 0.3% of 10_000 = 30
        assert_eq!(sr.fee().get(), 30);
    }

    // -- Integration: config validation error propagation ---------------------

    #[test]
    #[cfg(feature = "constant-product")]
    fn integration_config_validation_propagates_error() {
        // ConstantProductConfig with zero reserves
        let Ok(cfg) =
            ConstantProductConfig::new(make_pair(), fee(), Amount::ZERO, Amount::new(1_000))
        else {
            // Constructor itself may reject — that's valid too
            return;
        };
        let config = AmmConfig::ConstantProduct(cfg);
        let result = DefaultPoolFactory::create(&config);
        assert!(result.is_err());
    }

    // -- Debug format ---------------------------------------------------------

    #[test]
    fn debug_format() {
        let factory = DefaultPoolFactory;
        let dbg = format!("{factory:?}");
        assert!(dbg.contains("DefaultPoolFactory"));
    }

    // -- Copy + Clone ---------------------------------------------------------

    #[test]
    fn factory_is_copy() {
        let a = DefaultPoolFactory;
        let b = a;
        assert_eq!(a, b);
    }

    // -- Multi-pool swap comparison -------------------------------------------

    #[test]
    #[cfg(all(feature = "constant-product", feature = "hybrid"))]
    fn integration_multi_pool_swap_comparison() {
        // Create CP pool
        let Ok(cp_cfg) = ConstantProductConfig::new(
            make_pair(),
            fee(),
            Amount::new(1_000_000),
            Amount::new(1_000_000),
        ) else {
            panic!("expected valid config");
        };
        let Ok(mut cp_pool) = DefaultPoolFactory::create(&AmmConfig::ConstantProduct(cp_cfg))
        else {
            panic!("expected Ok");
        };

        // Create Hybrid pool (same reserves, amp=100)
        let Ok(hybrid_cfg) = HybridConfig::new(
            make_pair(),
            fee(),
            100,
            Amount::new(1_000_000),
            Amount::new(1_000_000),
        ) else {
            panic!("expected valid config");
        };
        let Ok(mut hybrid_pool) = DefaultPoolFactory::create(&AmmConfig::Hybrid(hybrid_cfg)) else {
            panic!("expected Ok");
        };

        // Same swap on both
        let Ok(spec1) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(spec2) = SwapSpec::exact_in(Amount::new(10_000)) else {
            panic!("valid spec");
        };
        let Ok(cp_result) = cp_pool.swap(spec1, token_a()) else {
            panic!("cp swap failed");
        };
        let Ok(hybrid_result) = hybrid_pool.swap(spec2, token_a()) else {
            panic!("hybrid swap failed");
        };

        // Both should produce positive output
        assert!(cp_result.amount_out().get() > 0);
        assert!(hybrid_result.amount_out().get() > 0);

        // With equal reserves and high amp, StableSwap should give better
        // (or similar) output than constant product
        assert!(hybrid_result.amount_out().get() >= cp_result.amount_out().get());
    }
}
