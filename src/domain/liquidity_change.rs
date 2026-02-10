//! Mutations to a liquidity position.

use core::fmt;

use super::{Amount, Liquidity, Tick};
use crate::error::AmmError;

/// Descriptor for the type of liquidity change.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ChangeType {
    /// Adding liquidity to a position.
    Add = 0,
    /// Removing liquidity from a position.
    Remove = 1,
    /// Rebalancing a position to a new tick range.
    Rebalance = 2,
}

impl fmt::Display for ChangeType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Add => write!(f, "Add"),
            Self::Remove => write!(f, "Remove"),
            Self::Rebalance => write!(f, "Rebalance"),
        }
    }
}

/// Describes a mutation to a liquidity position: adding liquidity,
/// removing liquidity, or rebalancing to a new tick range.
///
/// # Examples
///
/// ```
/// use hydra_amm::domain::{Amount, LiquidityChange};
///
/// let change = LiquidityChange::add(Amount::new(100), Amount::new(200));
/// assert!(change.is_ok());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LiquidityChange {
    /// Add liquidity by depositing token amounts.
    Add {
        /// Amount of token A to deposit.
        amount_a: Amount,
        /// Amount of token B to deposit.
        amount_b: Amount,
    },
    /// Remove a specified amount of liquidity.
    Remove {
        /// Liquidity to withdraw.
        liquidity: Liquidity,
    },
    /// Rebalance the position to a new tick range.
    Rebalance {
        /// New lower tick boundary.
        new_lower: Tick,
        /// New upper tick boundary.
        new_upper: Tick,
    },
}

impl LiquidityChange {
    /// Creates an `Add` variant.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::InvalidQuantity`] if both amounts are zero.
    pub const fn add(amount_a: Amount, amount_b: Amount) -> crate::error::Result<Self> {
        if amount_a.is_zero() && amount_b.is_zero() {
            return Err(AmmError::InvalidQuantity(
                "at least one amount must be positive",
            ));
        }
        Ok(Self::Add { amount_a, amount_b })
    }

    /// Creates a `Remove` variant.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::InvalidLiquidity`] if liquidity is zero.
    pub const fn remove(liquidity: Liquidity) -> crate::error::Result<Self> {
        if liquidity.is_zero() {
            return Err(AmmError::InvalidLiquidity(
                "remove liquidity must be non-zero",
            ));
        }
        Ok(Self::Remove { liquidity })
    }

    /// Creates a `Rebalance` variant.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::InvalidTickRange`] if `new_lower >= new_upper`.
    pub const fn rebalance(new_lower: Tick, new_upper: Tick) -> crate::error::Result<Self> {
        if new_lower.get() >= new_upper.get() {
            return Err(AmmError::InvalidTickRange(
                "new lower tick must be less than new upper tick",
            ));
        }
        Ok(Self::Rebalance {
            new_lower,
            new_upper,
        })
    }

    /// Returns the [`ChangeType`] descriptor for this variant.
    #[must_use]
    pub const fn change_type(&self) -> ChangeType {
        match self {
            Self::Add { .. } => ChangeType::Add,
            Self::Remove { .. } => ChangeType::Remove,
            Self::Rebalance { .. } => ChangeType::Rebalance,
        }
    }

    /// Returns `true` if this change affects token A.
    #[must_use]
    pub const fn affects_amount_a(&self) -> bool {
        matches!(
            self,
            Self::Add { .. } | Self::Remove { .. } | Self::Rebalance { .. }
        )
    }

    /// Returns `true` if this change affects token B.
    #[must_use]
    pub const fn affects_amount_b(&self) -> bool {
        matches!(
            self,
            Self::Add { .. } | Self::Remove { .. } | Self::Rebalance { .. }
        )
    }

    /// Returns `true` if this is an `Add` variant.
    #[must_use]
    pub const fn is_add(&self) -> bool {
        matches!(self, Self::Add { .. })
    }

    /// Returns `true` if this is a `Remove` variant.
    #[must_use]
    pub const fn is_remove(&self) -> bool {
        matches!(self, Self::Remove { .. })
    }

    /// Returns `true` if this is a `Rebalance` variant.
    #[must_use]
    pub const fn is_rebalance(&self) -> bool {
        matches!(self, Self::Rebalance { .. })
    }
}

impl fmt::Display for LiquidityChange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Add { amount_a, amount_b } => {
                write!(f, "Add(a={amount_a}, b={amount_b})")
            }
            Self::Remove { liquidity } => {
                write!(f, "Remove(liquidity={liquidity})")
            }
            Self::Rebalance {
                new_lower,
                new_upper,
            } => {
                write!(f, "Rebalance([{new_lower}, {new_upper}))")
            }
        }
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;

    fn tick(v: i32) -> Tick {
        let Ok(t) = Tick::new(v) else {
            panic!("valid tick expected");
        };
        t
    }

    // -- Add ----------------------------------------------------------------

    #[test]
    fn add_valid_both() {
        let Ok(c) = LiquidityChange::add(Amount::new(100), Amount::new(200)) else {
            panic!("expected Ok");
        };
        assert!(c.is_add());
        assert!(!c.is_remove());
        assert!(!c.is_rebalance());
        assert_eq!(c.change_type(), ChangeType::Add);
    }

    #[test]
    fn add_valid_only_a() {
        let result = LiquidityChange::add(Amount::new(100), Amount::ZERO);
        assert!(result.is_ok());
    }

    #[test]
    fn add_valid_only_b() {
        let result = LiquidityChange::add(Amount::ZERO, Amount::new(100));
        assert!(result.is_ok());
    }

    #[test]
    fn add_both_zero_rejected() {
        assert!(LiquidityChange::add(Amount::ZERO, Amount::ZERO).is_err());
    }

    // -- Remove -------------------------------------------------------------

    #[test]
    fn remove_valid() {
        let Ok(c) = LiquidityChange::remove(Liquidity::new(500)) else {
            panic!("expected Ok");
        };
        assert!(c.is_remove());
        assert!(!c.is_add());
        assert!(!c.is_rebalance());
        assert_eq!(c.change_type(), ChangeType::Remove);
    }

    #[test]
    fn remove_zero_rejected() {
        assert!(LiquidityChange::remove(Liquidity::ZERO).is_err());
    }

    // -- Rebalance ----------------------------------------------------------

    #[test]
    fn rebalance_valid() {
        let Ok(c) = LiquidityChange::rebalance(tick(-50), tick(50)) else {
            panic!("expected Ok");
        };
        assert!(c.is_rebalance());
        assert!(!c.is_add());
        assert!(!c.is_remove());
        assert_eq!(c.change_type(), ChangeType::Rebalance);
    }

    #[test]
    fn rebalance_equal_ticks_rejected() {
        assert!(LiquidityChange::rebalance(tick(0), tick(0)).is_err());
    }

    #[test]
    fn rebalance_inverted_ticks_rejected() {
        assert!(LiquidityChange::rebalance(tick(50), tick(-50)).is_err());
    }

    // -- affects_amount -----------------------------------------------------

    #[test]
    fn add_affects_both() {
        let Ok(c) = LiquidityChange::add(Amount::new(1), Amount::new(1)) else {
            panic!("expected Ok");
        };
        assert!(c.affects_amount_a());
        assert!(c.affects_amount_b());
    }

    #[test]
    fn remove_affects_both() {
        let Ok(c) = LiquidityChange::remove(Liquidity::new(1)) else {
            panic!("expected Ok");
        };
        assert!(c.affects_amount_a());
        assert!(c.affects_amount_b());
    }

    #[test]
    fn rebalance_affects_both() {
        let Ok(c) = LiquidityChange::rebalance(tick(-10), tick(10)) else {
            panic!("expected Ok");
        };
        assert!(c.affects_amount_a());
        assert!(c.affects_amount_b());
    }

    // -- Display ------------------------------------------------------------

    #[test]
    fn display_add() {
        let Ok(c) = LiquidityChange::add(Amount::new(10), Amount::new(20)) else {
            panic!("expected Ok");
        };
        let s = format!("{c}");
        assert!(s.contains("Add"));
        assert!(s.contains("10"));
        assert!(s.contains("20"));
    }

    #[test]
    fn display_remove() {
        let Ok(c) = LiquidityChange::remove(Liquidity::new(500)) else {
            panic!("expected Ok");
        };
        let s = format!("{c}");
        assert!(s.contains("Remove"));
        assert!(s.contains("500"));
    }

    #[test]
    fn display_rebalance() {
        let Ok(c) = LiquidityChange::rebalance(tick(-100), tick(100)) else {
            panic!("expected Ok");
        };
        let s = format!("{c}");
        assert!(s.contains("Rebalance"));
    }

    #[test]
    fn display_change_type() {
        assert_eq!(format!("{}", ChangeType::Add), "Add");
        assert_eq!(format!("{}", ChangeType::Remove), "Remove");
        assert_eq!(format!("{}", ChangeType::Rebalance), "Rebalance");
    }

    // -- Copy ---------------------------------------------------------------

    #[test]
    fn copy_semantics() {
        let Ok(a) = LiquidityChange::add(Amount::new(1), Amount::new(2)) else {
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
        let Ok(a) = LiquidityChange::add(Amount::new(10), Amount::new(20)) else {
            panic!("expected Ok");
        };
        let Ok(b) = LiquidityChange::add(Amount::new(10), Amount::new(20)) else {
            panic!("expected Ok");
        };
        assert_eq!(hash_of(&a), hash_of(&b));
    }

    #[test]
    fn debug_format_add() {
        let Ok(c) = LiquidityChange::add(Amount::new(1), Amount::new(2)) else {
            panic!("expected Ok");
        };
        let dbg = format!("{c:?}");
        assert!(dbg.contains("Add"));
    }

    #[test]
    fn debug_format_remove() {
        let Ok(c) = LiquidityChange::remove(Liquidity::new(100)) else {
            panic!("expected Ok");
        };
        let dbg = format!("{c:?}");
        assert!(dbg.contains("Remove"));
    }

    #[test]
    fn debug_format_rebalance() {
        let Ok(c) = LiquidityChange::rebalance(tick(-10), tick(10)) else {
            panic!("expected Ok");
        };
        let dbg = format!("{c:?}");
        assert!(dbg.contains("Rebalance"));
    }

    #[test]
    fn remove_change_type() {
        let Ok(c) = LiquidityChange::remove(Liquidity::new(1)) else {
            panic!("expected Ok");
        };
        assert_eq!(c.change_type(), ChangeType::Remove);
    }

    #[test]
    fn rebalance_change_type() {
        let Ok(c) = LiquidityChange::rebalance(tick(-50), tick(50)) else {
            panic!("expected Ok");
        };
        assert_eq!(c.change_type(), ChangeType::Rebalance);
    }
}
