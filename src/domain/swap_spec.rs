//! Swap operation specification.

use core::fmt;

use super::Amount;
use crate::error::AmmError;

/// Descriptor for the type of swap constraint.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum SwapType {
    /// The input amount is fixed; output is computed.
    ExactIn = 0,
    /// The output amount is fixed; input is computed.
    ExactOut = 1,
}

impl fmt::Display for SwapType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ExactIn => write!(f, "ExactIn"),
            Self::ExactOut => write!(f, "ExactOut"),
        }
    }
}

/// Specifies what constraint drives a swap: either an exact input amount
/// or an exact output amount.
///
/// # Invariants
///
/// The contained amount is always non-zero.
///
/// # Examples
///
/// ```
/// use hydra_amm::domain::{Amount, SwapSpec};
///
/// let spec = SwapSpec::exact_in(Amount::new(1000));
/// assert!(spec.is_ok());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SwapSpec {
    /// The caller provides an exact input amount.
    ExactIn {
        /// The fixed input amount (always non-zero).
        amount_in: Amount,
    },
    /// The caller requests an exact output amount.
    ExactOut {
        /// The desired output amount (always non-zero).
        amount_out: Amount,
    },
}

impl SwapSpec {
    /// Creates an exact-input swap specification.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::InvalidQuantity`] if `amount` is zero.
    pub const fn exact_in(amount: Amount) -> crate::error::Result<Self> {
        if amount.is_zero() {
            return Err(AmmError::InvalidQuantity("swap amount must be non-zero"));
        }
        Ok(Self::ExactIn { amount_in: amount })
    }

    /// Creates an exact-output swap specification.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::InvalidQuantity`] if `amount` is zero.
    pub const fn exact_out(amount: Amount) -> crate::error::Result<Self> {
        if amount.is_zero() {
            return Err(AmmError::InvalidQuantity("swap amount must be non-zero"));
        }
        Ok(Self::ExactOut { amount_out: amount })
    }

    /// Returns `true` if this is an exact-input specification.
    #[must_use]
    pub const fn is_exact_in(&self) -> bool {
        matches!(self, Self::ExactIn { .. })
    }

    /// Returns `true` if this is an exact-output specification.
    #[must_use]
    pub const fn is_exact_out(&self) -> bool {
        matches!(self, Self::ExactOut { .. })
    }

    /// Extracts the amount regardless of variant.
    pub const fn amount(&self) -> Amount {
        match self {
            Self::ExactIn { amount_in } => *amount_in,
            Self::ExactOut { amount_out } => *amount_out,
        }
    }

    /// Returns the [`SwapType`] descriptor for this specification.
    #[must_use]
    pub const fn swap_type(&self) -> SwapType {
        match self {
            Self::ExactIn { .. } => SwapType::ExactIn,
            Self::ExactOut { .. } => SwapType::ExactOut,
        }
    }
}

impl fmt::Display for SwapSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ExactIn { amount_in } => write!(f, "ExactIn({amount_in})"),
            Self::ExactOut { amount_out } => write!(f, "ExactOut({amount_out})"),
        }
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;

    // -- Construction -------------------------------------------------------

    #[test]
    fn exact_in_valid() {
        let Ok(spec) = SwapSpec::exact_in(Amount::new(100)) else {
            panic!("expected Ok");
        };
        assert!(spec.is_exact_in());
        assert!(!spec.is_exact_out());
        assert_eq!(spec.amount(), Amount::new(100));
    }

    #[test]
    fn exact_out_valid() {
        let Ok(spec) = SwapSpec::exact_out(Amount::new(200)) else {
            panic!("expected Ok");
        };
        assert!(spec.is_exact_out());
        assert!(!spec.is_exact_in());
        assert_eq!(spec.amount(), Amount::new(200));
    }

    #[test]
    fn exact_in_zero_rejected() {
        assert!(SwapSpec::exact_in(Amount::ZERO).is_err());
    }

    #[test]
    fn exact_out_zero_rejected() {
        assert!(SwapSpec::exact_out(Amount::ZERO).is_err());
    }

    // -- swap_type ----------------------------------------------------------

    #[test]
    fn swap_type_exact_in() {
        let Ok(spec) = SwapSpec::exact_in(Amount::new(1)) else {
            panic!("expected Ok");
        };
        assert_eq!(spec.swap_type(), SwapType::ExactIn);
    }

    #[test]
    fn swap_type_exact_out() {
        let Ok(spec) = SwapSpec::exact_out(Amount::new(1)) else {
            panic!("expected Ok");
        };
        assert_eq!(spec.swap_type(), SwapType::ExactOut);
    }

    // -- Display ------------------------------------------------------------

    #[test]
    fn display_exact_in() {
        let Ok(spec) = SwapSpec::exact_in(Amount::new(42)) else {
            panic!("expected Ok");
        };
        assert_eq!(format!("{spec}"), "ExactIn(42)");
    }

    #[test]
    fn display_exact_out() {
        let Ok(spec) = SwapSpec::exact_out(Amount::new(99)) else {
            panic!("expected Ok");
        };
        assert_eq!(format!("{spec}"), "ExactOut(99)");
    }

    #[test]
    fn display_swap_type() {
        assert_eq!(format!("{}", SwapType::ExactIn), "ExactIn");
        assert_eq!(format!("{}", SwapType::ExactOut), "ExactOut");
    }

    // -- Copy ---------------------------------------------------------------

    #[test]
    fn copy_semantics() {
        let Ok(a) = SwapSpec::exact_in(Amount::new(10)) else {
            panic!("expected Ok");
        };
        let b = a;
        assert_eq!(a, b);
    }

    #[test]
    fn hash_consistency() {
        use core::hash::{Hash, Hasher};
        fn hash_of<T: Hash>(t: &T) -> u64 {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            t.hash(&mut h);
            h.finish()
        }
        let Ok(a) = SwapSpec::exact_in(Amount::new(100)) else {
            panic!("expected Ok");
        };
        let Ok(b) = SwapSpec::exact_in(Amount::new(100)) else {
            panic!("expected Ok");
        };
        assert_eq!(hash_of(&a), hash_of(&b));
    }

    #[test]
    fn exact_in_and_exact_out_not_equal() {
        let Ok(a) = SwapSpec::exact_in(Amount::new(100)) else {
            panic!("expected Ok");
        };
        let Ok(b) = SwapSpec::exact_out(Amount::new(100)) else {
            panic!("expected Ok");
        };
        assert_ne!(a, b);
    }

    #[test]
    fn debug_format() {
        let Ok(spec) = SwapSpec::exact_in(Amount::new(42)) else {
            panic!("expected Ok");
        };
        let dbg = format!("{spec:?}");
        assert!(dbg.contains("ExactIn"));
    }

    #[test]
    fn amount_extraction_exact_out() {
        let Ok(spec) = SwapSpec::exact_out(Amount::new(777)) else {
            panic!("expected Ok");
        };
        assert_eq!(spec.amount(), Amount::new(777));
    }
}
