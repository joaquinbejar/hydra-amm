//! Pool instantiation via the factory pattern.
//!
//! The `DefaultPoolFactory` creates pool instances from `AmmConfig`
//! values, validating configuration and dispatching to the appropriate
//! pool constructor based on the config variant.
