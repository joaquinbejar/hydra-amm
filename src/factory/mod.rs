//! Pool instantiation via the factory pattern.
//!
//! The [`DefaultPoolFactory`] creates pool instances from [`AmmConfig`]
//! values, validating configuration and dispatching to the appropriate
//! pool constructor based on the config variant.
//!
//! # Usage
//!
//! ```rust
//! use hydra_amm::config::{AmmConfig, ConstantProductConfig};
//! use hydra_amm::domain::{
//!     Amount, BasisPoints, Decimals, FeeTier, Token, TokenAddress, TokenPair,
//! };
//! use hydra_amm::factory::DefaultPoolFactory;
//! use hydra_amm::traits::SwapPool;
//!
//! let tok_a = Token::new(TokenAddress::from_bytes([1u8; 32]), Decimals::new(6).expect("ok"));
//! let tok_b = Token::new(TokenAddress::from_bytes([2u8; 32]), Decimals::new(18).expect("ok"));
//! let pair  = TokenPair::new(tok_a, tok_b).expect("distinct");
//! let fee   = FeeTier::new(BasisPoints::new(30));
//! let cfg   = ConstantProductConfig::new(pair, fee, Amount::new(1_000_000), Amount::new(1_000_000))
//!     .expect("valid");
//!
//! let pool = DefaultPoolFactory::create(&AmmConfig::ConstantProduct(cfg))
//!     .expect("pool created");
//! assert_eq!(pool.fee_tier(), fee);
//! ```
//!
//! # Feature Gating
//!
//! Each match arm is gated behind its respective pool feature flag.
//! If a config variant is passed for a pool type whose feature is not
//! enabled, an [`AmmError::InvalidConfiguration`] is returned.
//!
//! [`AmmConfig`]: crate::config::AmmConfig
//! [`AmmError::InvalidConfiguration`]: crate::error::AmmError::InvalidConfiguration

mod default_factory;

pub use default_factory::DefaultPoolFactory;
