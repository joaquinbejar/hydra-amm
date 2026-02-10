//! Protocol fee tiers built on [`BasisPoints`].

use core::fmt;

use super::{Amount, BasisPoints, Rounding};

/// A protocol-specific fee tier wrapping [`BasisPoints`] with common presets.
///
/// Any `BasisPoints` value is accepted, but [`is_standard`](Self::is_standard)
/// indicates whether it matches one of the four well-known tiers used across
/// major AMM protocols.
///
/// # Examples
///
/// ```
/// use hydra_amm::domain::{BasisPoints, FeeTier};
///
/// let tier = FeeTier::TIER_0_30_PERCENT;
/// assert_eq!(tier.basis_points().get(), 30);
/// assert!(tier.is_standard());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FeeTier(BasisPoints);

impl FeeTier {
    /// 0.01% fee — ultra-concentrated, low-volume pairs (1 bp).
    pub const TIER_0_01_PERCENT: Self = Self(BasisPoints::new(1));

    /// 0.05% fee — stablecoin pairs (5 bp).
    pub const TIER_0_05_PERCENT: Self = Self(BasisPoints::new(5));

    /// 0.30% fee — standard volatile pairs (30 bp).
    pub const TIER_0_30_PERCENT: Self = Self(BasisPoints::new(30));

    /// 1.00% fee — high-fee trading pairs (100 bp).
    pub const TIER_1_00_PERCENT: Self = Self(BasisPoints::new(100));

    /// Creates a new `FeeTier` from arbitrary [`BasisPoints`].
    pub const fn new(basis_points: BasisPoints) -> Self {
        Self(basis_points)
    }

    /// Returns the underlying [`BasisPoints`].
    #[must_use]
    pub const fn basis_points(&self) -> BasisPoints {
        self.0
    }

    /// Computes the fee for a given `amount` using this tier's basis points.
    ///
    /// Delegates to [`BasisPoints::apply`].
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::Overflow`](crate::error::AmmError::Overflow) if the intermediate multiplication overflows.
    pub const fn apply_to_amount(
        &self,
        amount: Amount,
        rounding: Rounding,
    ) -> crate::error::Result<Amount> {
        self.0.apply(amount, rounding)
    }

    /// Returns `true` if this tier matches one of the four standard presets.
    #[must_use]
    pub const fn is_standard(&self) -> bool {
        matches!(self.0.get(), 1 | 5 | 30 | 100)
    }
}

impl fmt::Display for FeeTier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FeeTier({})", self.0)
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;

    // -- Construction & accessors -------------------------------------------

    #[test]
    fn new_and_basis_points() {
        let tier = FeeTier::new(BasisPoints::new(42));
        assert_eq!(tier.basis_points().get(), 42);
    }

    #[test]
    fn preset_values() {
        assert_eq!(FeeTier::TIER_0_01_PERCENT.basis_points().get(), 1);
        assert_eq!(FeeTier::TIER_0_05_PERCENT.basis_points().get(), 5);
        assert_eq!(FeeTier::TIER_0_30_PERCENT.basis_points().get(), 30);
        assert_eq!(FeeTier::TIER_1_00_PERCENT.basis_points().get(), 100);
    }

    // -- is_standard --------------------------------------------------------

    #[test]
    fn standard_tiers() {
        assert!(FeeTier::TIER_0_01_PERCENT.is_standard());
        assert!(FeeTier::TIER_0_05_PERCENT.is_standard());
        assert!(FeeTier::TIER_0_30_PERCENT.is_standard());
        assert!(FeeTier::TIER_1_00_PERCENT.is_standard());
    }

    #[test]
    fn non_standard_tier() {
        let tier = FeeTier::new(BasisPoints::new(42));
        assert!(!tier.is_standard());
    }

    // -- apply_to_amount ----------------------------------------------------

    #[test]
    fn apply_30bp_round_down() {
        // 30bp of 1_000_000 = 3_000
        let tier = FeeTier::TIER_0_30_PERCENT;
        let Ok(fee) = tier.apply_to_amount(Amount::new(1_000_000), Rounding::Down) else {
            panic!("expected Ok");
        };
        assert_eq!(fee, Amount::new(3_000));
    }

    #[test]
    fn apply_1bp_round_up_remainder() {
        // 1bp of 1 = 1 * 1 / 10_000 = 0.0001 → ceil = 1
        let tier = FeeTier::TIER_0_01_PERCENT;
        let Ok(fee) = tier.apply_to_amount(Amount::new(1), Rounding::Up) else {
            panic!("expected Ok");
        };
        assert_eq!(fee, Amount::new(1));
    }

    #[test]
    fn apply_zero_amount() {
        let tier = FeeTier::TIER_0_30_PERCENT;
        let Ok(fee) = tier.apply_to_amount(Amount::ZERO, Rounding::Down) else {
            panic!("expected Ok");
        };
        assert_eq!(fee, Amount::ZERO);
    }

    // -- Display ------------------------------------------------------------

    #[test]
    fn display() {
        assert_eq!(format!("{}", FeeTier::TIER_0_30_PERCENT), "FeeTier(30bp)");
    }

    // -- Ordering -----------------------------------------------------------

    #[test]
    fn ordering() {
        assert!(FeeTier::TIER_0_01_PERCENT < FeeTier::TIER_1_00_PERCENT);
    }

    // -- Copy ---------------------------------------------------------------

    #[test]
    fn copy_semantics() {
        let a = FeeTier::TIER_0_30_PERCENT;
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
        let a = FeeTier::TIER_0_30_PERCENT;
        let b = FeeTier::new(BasisPoints::new(30));
        assert_eq!(hash_of(&a), hash_of(&b));
    }

    #[test]
    fn apply_overflow() {
        let tier = FeeTier::new(BasisPoints::new(u32::MAX));
        let result = tier.apply_to_amount(Amount::MAX, Rounding::Down);
        assert!(result.is_err());
    }

    #[test]
    fn debug_format() {
        let tier = FeeTier::TIER_0_30_PERCENT;
        let dbg = format!("{tier:?}");
        assert!(dbg.contains("FeeTier"));
    }

    #[test]
    fn apply_1bp_round_down_small_amount() {
        // 1bp of 5000 = 5000 * 1 / 10_000 = 0.5 → floor = 0
        let tier = FeeTier::TIER_0_01_PERCENT;
        let Ok(fee) = tier.apply_to_amount(Amount::new(5_000), Rounding::Down) else {
            panic!("expected Ok");
        };
        assert_eq!(fee, Amount::ZERO);
    }
}
