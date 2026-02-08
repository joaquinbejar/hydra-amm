//! Unified error types for the Hydra AMM library.
//!
//! All fallible operations across the crate return [`AmmError`] as their
//! error type, ensuring a consistent error handling experience for consumers.
//!
//! # Error Code Ranges
//!
//! | Range | Category | Description |
//! |-------|----------|-------------|
//! | 1000–1999 | Validation | Invalid inputs or parameters |
//! | 2000–2999 | State | Pool/position state violations |
//! | 3000–3999 | Arithmetic | Overflow, underflow, division by zero |
//! | 4000–4999 | Pool-specific | Algorithm or protocol-level failures |

use thiserror::Error;

/// Convenience alias used throughout the crate.
pub type Result<T> = core::result::Result<T, AmmError>;

// ---------------------------------------------------------------------------
// AmmError
// ---------------------------------------------------------------------------

/// Unified error enum for the Hydra AMM library.
///
/// Every fallible operation in the crate returns `Result<T, AmmError>`.
/// Variants are grouped by numeric error-code ranges so that callers can
/// pattern-match on categories or inspect individual codes for logging.
#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum AmmError {
    // ----- 1000–1999: Validation errors ------------------------------------
    /// An invalid price value was provided (code 1000).
    #[error("invalid price: {0}")]
    InvalidPrice(&'static str),

    /// An invalid quantity / amount was provided (code 1001).
    #[error("invalid quantity: {0}")]
    InvalidQuantity(&'static str),

    /// A tick range is invalid — e.g. lower >= upper (code 1002).
    #[error("invalid tick range: {0}")]
    InvalidTickRange(&'static str),

    /// An individual tick value is out of bounds (code 1003).
    #[error("invalid tick: {0}")]
    InvalidTick(&'static str),

    /// A liquidity value is invalid — e.g. zero when non-zero is required (code 1004).
    #[error("invalid liquidity: {0}")]
    InvalidLiquidity(&'static str),

    /// A fee rate / tier is out of the valid range (code 1005).
    #[error("invalid fee: {0}")]
    InvalidFee(&'static str),

    /// A precision or decimals value is out of range (code 1006).
    #[error("invalid precision: {0}")]
    InvalidPrecision(&'static str),

    /// A pool configuration is invalid (code 1007).
    #[error("invalid configuration: {0}")]
    InvalidConfiguration(&'static str),

    /// A token or token pair is invalid (code 1008).
    #[error("invalid token: {0}")]
    InvalidToken(&'static str),

    /// A weight value is invalid — e.g. zero or exceeds maximum (code 1009).
    #[error("invalid weight: {0}")]
    InvalidWeight(&'static str),

    // ----- 2000–2999: State errors -----------------------------------------
    /// The pool has not been initialized yet (code 2000).
    #[error("pool not initialized")]
    PoolNotInitialized,

    /// A referenced position was not found (code 2001).
    #[error("position not found")]
    PositionNotFound,

    /// Insufficient liquidity to satisfy the operation (code 2002).
    #[error("insufficient liquidity")]
    InsufficientLiquidity,

    /// Insufficient balance for the requested transfer (code 2003).
    #[error("insufficient balance")]
    InsufficientBalance,

    /// The pool is already initialized (code 2004).
    #[error("pool already initialized")]
    PoolAlreadyInitialized,

    /// A position with the same key already exists (code 2005).
    #[error("position already exists")]
    PositionAlreadyExists,

    /// One or both reserves are zero when a non-zero value is required (code 2006).
    #[error("zero reserve")]
    ZeroReserve,

    /// A required reserve was not found in the pool (code 2007).
    #[error("reserve not found")]
    ReserveNotFound,

    // ----- 3000–3999: Arithmetic errors ------------------------------------
    /// An arithmetic operation overflowed (code 3000).
    #[error("arithmetic overflow: {0}")]
    Overflow(&'static str),

    /// An arithmetic operation underflowed (code 3001).
    #[error("arithmetic underflow: {0}")]
    Underflow(&'static str),

    /// Division by zero was attempted (code 3002).
    #[error("division by zero")]
    DivisionByZero,

    /// Unacceptable loss of precision during conversion (code 3003).
    #[error("precision loss: {0}")]
    PrecisionLoss(&'static str),

    // ----- 4000–4999: Pool-specific errors ---------------------------------
    /// Newton-Raphson iteration did not converge (code 4000).
    #[error("newton-raphson non-convergence: {0}")]
    NewtonRaphsonNonConvergence(&'static str),

    /// A tick spacing constraint was violated (code 4001).
    #[error("tick spacing violation: {0}")]
    TickSpacingViolation(&'static str),

    /// No liquidity is available at the requested tick (code 4002).
    #[error("no liquidity at tick")]
    NoLiquidityAtTick,

    /// The requested swap path is invalid or unsupported (code 4003).
    #[error("invalid swap path: {0}")]
    InvalidSwapPath(&'static str),
}

impl AmmError {
    /// Returns the numeric error code for this variant.
    ///
    /// Codes are organized into ranges:
    /// - 1000–1999 for validation errors
    /// - 2000–2999 for state errors
    /// - 3000–3999 for arithmetic errors
    /// - 4000–4999 for pool-specific errors
    #[must_use]
    pub const fn error_code(&self) -> u16 {
        match self {
            // Validation (1000–1999)
            Self::InvalidPrice(_) => 1000,
            Self::InvalidQuantity(_) => 1001,
            Self::InvalidTickRange(_) => 1002,
            Self::InvalidTick(_) => 1003,
            Self::InvalidLiquidity(_) => 1004,
            Self::InvalidFee(_) => 1005,
            Self::InvalidPrecision(_) => 1006,
            Self::InvalidConfiguration(_) => 1007,
            Self::InvalidToken(_) => 1008,
            Self::InvalidWeight(_) => 1009,

            // State (2000–2999)
            Self::PoolNotInitialized => 2000,
            Self::PositionNotFound => 2001,
            Self::InsufficientLiquidity => 2002,
            Self::InsufficientBalance => 2003,
            Self::PoolAlreadyInitialized => 2004,
            Self::PositionAlreadyExists => 2005,
            Self::ZeroReserve => 2006,
            Self::ReserveNotFound => 2007,

            // Arithmetic (3000–3999)
            Self::Overflow(_) => 3000,
            Self::Underflow(_) => 3001,
            Self::DivisionByZero => 3002,
            Self::PrecisionLoss(_) => 3003,

            // Pool-specific (4000–4999)
            Self::NewtonRaphsonNonConvergence(_) => 4000,
            Self::TickSpacingViolation(_) => 4001,
            Self::NoLiquidityAtTick => 4002,
            Self::InvalidSwapPath(_) => 4003,
        }
    }

    /// Returns `true` if this is a validation error (1000–1999).
    #[must_use]
    pub const fn is_validation(&self) -> bool {
        self.error_code() >= 1000 && self.error_code() < 2000
    }

    /// Returns `true` if this is a state error (2000–2999).
    #[must_use]
    pub const fn is_state(&self) -> bool {
        self.error_code() >= 2000 && self.error_code() < 3000
    }

    /// Returns `true` if this is an arithmetic error (3000–3999).
    #[must_use]
    pub const fn is_arithmetic(&self) -> bool {
        self.error_code() >= 3000 && self.error_code() < 4000
    }

    /// Returns `true` if this is a pool-specific error (4000–4999).
    #[must_use]
    pub const fn is_pool_specific(&self) -> bool {
        self.error_code() >= 4000 && self.error_code() < 5000
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- error_code ranges --------------------------------------------------

    #[test]
    fn validation_errors_have_1xxx_codes() {
        let cases: &[AmmError] = &[
            AmmError::InvalidPrice("p"),
            AmmError::InvalidQuantity("q"),
            AmmError::InvalidTickRange("r"),
            AmmError::InvalidTick("t"),
            AmmError::InvalidLiquidity("l"),
            AmmError::InvalidFee("f"),
            AmmError::InvalidPrecision("p"),
            AmmError::InvalidConfiguration("c"),
            AmmError::InvalidToken("t"),
            AmmError::InvalidWeight("w"),
        ];
        for err in cases {
            let code = err.error_code();
            assert!(
                (1000..2000).contains(&code),
                "expected 1xxx for {err}, got {code}"
            );
            assert!(err.is_validation());
            assert!(!err.is_state());
            assert!(!err.is_arithmetic());
            assert!(!err.is_pool_specific());
        }
    }

    #[test]
    fn state_errors_have_2xxx_codes() {
        let cases: &[AmmError] = &[
            AmmError::PoolNotInitialized,
            AmmError::PositionNotFound,
            AmmError::InsufficientLiquidity,
            AmmError::InsufficientBalance,
            AmmError::PoolAlreadyInitialized,
            AmmError::PositionAlreadyExists,
            AmmError::ZeroReserve,
            AmmError::ReserveNotFound,
        ];
        for err in cases {
            let code = err.error_code();
            assert!(
                (2000..3000).contains(&code),
                "expected 2xxx for {err}, got {code}"
            );
            assert!(err.is_state());
            assert!(!err.is_validation());
        }
    }

    #[test]
    fn arithmetic_errors_have_3xxx_codes() {
        let cases: &[AmmError] = &[
            AmmError::Overflow("o"),
            AmmError::Underflow("u"),
            AmmError::DivisionByZero,
            AmmError::PrecisionLoss("p"),
        ];
        for err in cases {
            let code = err.error_code();
            assert!(
                (3000..4000).contains(&code),
                "expected 3xxx for {err}, got {code}"
            );
            assert!(err.is_arithmetic());
            assert!(!err.is_validation());
        }
    }

    #[test]
    fn pool_specific_errors_have_4xxx_codes() {
        let cases: &[AmmError] = &[
            AmmError::NewtonRaphsonNonConvergence("n"),
            AmmError::TickSpacingViolation("t"),
            AmmError::NoLiquidityAtTick,
            AmmError::InvalidSwapPath("s"),
        ];
        for err in cases {
            let code = err.error_code();
            assert!(
                (4000..5000).contains(&code),
                "expected 4xxx for {err}, got {code}"
            );
            assert!(err.is_pool_specific());
            assert!(!err.is_arithmetic());
        }
    }

    // -- Display ------------------------------------------------------------

    #[test]
    fn display_includes_context_message() {
        let err = AmmError::InvalidPrice("must be positive");
        let msg = format!("{err}");
        assert!(
            msg.contains("must be positive"),
            "expected context in display: {msg}"
        );
    }

    #[test]
    fn display_unit_variants_are_readable() {
        let err = AmmError::DivisionByZero;
        let msg = format!("{err}");
        assert!(
            msg.contains("division by zero"),
            "expected readable message: {msg}"
        );
    }

    // -- Clone & PartialEq -------------------------------------------------

    #[test]
    fn clone_and_eq() {
        let a = AmmError::Overflow("test");
        let b = a.clone();
        assert_eq!(a, b);
    }

    #[test]
    fn different_variants_are_not_equal() {
        let a = AmmError::Overflow("x");
        let b = AmmError::Underflow("x");
        assert_ne!(a, b);
    }

    // -- Result alias -------------------------------------------------------

    #[test]
    fn result_alias_ok() {
        let r: Result<u32> = Ok(42);
        assert_eq!(r, Ok(42));
    }

    #[test]
    fn result_alias_err() {
        let r: Result<u32> = Err(AmmError::DivisionByZero);
        assert!(r.is_err());
    }

    // -- Specific error codes -----------------------------------------------

    #[test]
    fn specific_error_codes() {
        assert_eq!(AmmError::InvalidPrice("").error_code(), 1000);
        assert_eq!(AmmError::InvalidWeight("").error_code(), 1009);
        assert_eq!(AmmError::PoolNotInitialized.error_code(), 2000);
        assert_eq!(AmmError::ReserveNotFound.error_code(), 2007);
        assert_eq!(AmmError::Overflow("").error_code(), 3000);
        assert_eq!(AmmError::DivisionByZero.error_code(), 3002);
        assert_eq!(AmmError::NewtonRaphsonNonConvergence("").error_code(), 4000);
        assert_eq!(AmmError::InvalidSwapPath("").error_code(), 4003);
    }
}
