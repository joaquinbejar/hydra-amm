//! Feature-gated pool implementations and the `PoolBox` dispatch enum.
//!
//! Each pool type is behind its own Cargo feature flag. The `PoolBox`
//! enum provides zero-cost static dispatch across all enabled pool types,
//! allowing heterogeneous collections without `dyn` trait objects.
