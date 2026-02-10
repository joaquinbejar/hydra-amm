//! Explicit rounding direction for arithmetic operations.

/// Specifies the rounding direction for division and multiplication
/// operations on domain types.
///
/// All division in the AMM library requires an explicit `Rounding`
/// parameter to prevent silent precision loss.
///
/// # Examples
///
/// ```
/// use hydra_amm::domain::Rounding;
///
/// let r = Rounding::Up;
/// assert!(r.is_up());
/// assert!(!r.is_down());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Rounding {
    /// Round towards positive infinity (ceiling).
    Up,
    /// Round towards zero (floor).
    Down,
}

impl Rounding {
    /// Returns `true` if this is [`Rounding::Up`].
    #[must_use]
    pub const fn is_up(&self) -> bool {
        matches!(self, Self::Up)
    }

    /// Returns `true` if this is [`Rounding::Down`].
    #[must_use]
    pub const fn is_down(&self) -> bool {
        matches!(self, Self::Down)
    }

    /// Returns a human-readable description of the rounding direction.
    #[must_use]
    pub const fn description(&self) -> &'static str {
        match self {
            Self::Up => "round towards positive infinity",
            Self::Down => "round towards zero",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn up_is_up() {
        assert!(Rounding::Up.is_up());
        assert!(!Rounding::Up.is_down());
    }

    #[test]
    fn down_is_down() {
        assert!(Rounding::Down.is_down());
        assert!(!Rounding::Down.is_up());
    }

    #[test]
    fn description_up() {
        assert_eq!(
            Rounding::Up.description(),
            "round towards positive infinity"
        );
    }

    #[test]
    fn description_down() {
        assert_eq!(Rounding::Down.description(), "round towards zero");
    }

    #[test]
    fn equality() {
        assert_eq!(Rounding::Up, Rounding::Up);
        assert_eq!(Rounding::Down, Rounding::Down);
        assert_ne!(Rounding::Up, Rounding::Down);
    }

    #[test]
    fn copy_semantics() {
        let a = Rounding::Up;
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
        assert_eq!(hash_of(&Rounding::Up), hash_of(&Rounding::Up));
        assert_eq!(hash_of(&Rounding::Down), hash_of(&Rounding::Down));
        assert_ne!(hash_of(&Rounding::Up), hash_of(&Rounding::Down));
    }

    #[test]
    fn debug_format() {
        let dbg_up = format!("{:?}", Rounding::Up);
        let dbg_down = format!("{:?}", Rounding::Down);
        assert!(dbg_up.contains("Up"));
        assert!(dbg_down.contains("Down"));
    }
}
