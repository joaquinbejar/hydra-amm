//! Concentrated liquidity position.

use core::fmt;

use super::{Liquidity, Tick};
use crate::error::AmmError;

/// A concentrated liquidity position defining a tick range and liquidity amount.
///
/// Represents a liquidity provider's position within a specific price range,
/// defined by a lower and upper [`Tick`] boundary and the [`Liquidity`]
/// deposited in that range.
///
/// # Invariants
///
/// - `lower_tick < upper_tick` — the range must be non-empty.
/// - Both ticks must be within the valid tick range.
///
/// # Examples
///
/// ```
/// use hydra_amm::domain::{Liquidity, Position, Tick};
///
/// let lower = Tick::new(-100).unwrap_or(Tick::ZERO);
/// let upper = Tick::new(100).unwrap_or(Tick::ZERO);
/// let liq = Liquidity::new(1_000_000);
/// let pos = Position::new(lower, upper, liq);
/// assert!(pos.is_ok());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Position {
    lower_tick: Tick,
    upper_tick: Tick,
    liquidity: Liquidity,
}

impl Position {
    /// Creates a new `Position` with validated tick ordering.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::InvalidTickRange`] if `lower_tick >= upper_tick`.
    pub const fn new(
        lower_tick: Tick,
        upper_tick: Tick,
        liquidity: Liquidity,
    ) -> crate::error::Result<Self> {
        if lower_tick.get() >= upper_tick.get() {
            return Err(AmmError::InvalidTickRange(
                "lower tick must be less than upper tick",
            ));
        }
        Ok(Self {
            lower_tick,
            upper_tick,
            liquidity,
        })
    }

    /// Returns the lower tick boundary.
    #[must_use]
    pub const fn lower_tick(&self) -> Tick {
        self.lower_tick
    }

    /// Returns the upper tick boundary.
    #[must_use]
    pub const fn upper_tick(&self) -> Tick {
        self.upper_tick
    }

    /// Returns the liquidity in this position.
    #[must_use]
    pub const fn liquidity(&self) -> Liquidity {
        self.liquidity
    }

    /// Returns both tick bounds as a tuple `(lower, upper)`.
    #[must_use]
    pub const fn tick_range(&self) -> (Tick, Tick) {
        (self.lower_tick, self.upper_tick)
    }

    /// Returns the width of the tick range (`upper - lower`).
    ///
    /// Always positive for a valid position.
    #[must_use]
    pub const fn width(&self) -> i32 {
        self.upper_tick.get() - self.lower_tick.get()
    }

    /// Returns `true` if the given tick falls within this position's range.
    ///
    /// The check is `lower_tick <= current_tick < upper_tick` (lower-inclusive,
    /// upper-exclusive), following the Uniswap v3 convention.
    #[must_use]
    pub const fn is_in_range(&self, current_tick: Tick) -> bool {
        current_tick.get() >= self.lower_tick.get() && current_tick.get() < self.upper_tick.get()
    }
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Position([{}, {}), liquidity={})",
            self.lower_tick, self.upper_tick, self.liquidity
        )
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

    // -- Construction -------------------------------------------------------

    #[test]
    fn valid_position() {
        let Ok(pos) = Position::new(tick(-100), tick(100), Liquidity::new(1000)) else {
            panic!("expected Ok");
        };
        assert_eq!(pos.lower_tick(), tick(-100));
        assert_eq!(pos.upper_tick(), tick(100));
        assert_eq!(pos.liquidity(), Liquidity::new(1000));
    }

    #[test]
    fn valid_zero_liquidity() {
        let result = Position::new(tick(-100), tick(100), Liquidity::ZERO);
        assert!(result.is_ok());
    }

    #[test]
    fn invalid_equal_ticks() {
        let result = Position::new(tick(0), tick(0), Liquidity::new(100));
        assert!(result.is_err());
    }

    #[test]
    fn invalid_inverted_ticks() {
        let result = Position::new(tick(100), tick(-100), Liquidity::new(100));
        assert!(result.is_err());
    }

    // -- Accessors ----------------------------------------------------------

    #[test]
    fn tick_range() {
        let Ok(pos) = Position::new(tick(-50), tick(50), Liquidity::new(1)) else {
            panic!("expected Ok");
        };
        assert_eq!(pos.tick_range(), (tick(-50), tick(50)));
    }

    #[test]
    fn width() {
        let Ok(pos) = Position::new(tick(-100), tick(200), Liquidity::new(1)) else {
            panic!("expected Ok");
        };
        assert_eq!(pos.width(), 300);
    }

    #[test]
    fn width_narrow() {
        let Ok(pos) = Position::new(tick(0), tick(1), Liquidity::new(1)) else {
            panic!("expected Ok");
        };
        assert_eq!(pos.width(), 1);
    }

    // -- is_in_range --------------------------------------------------------

    #[test]
    fn in_range_middle() {
        let Ok(pos) = Position::new(tick(-100), tick(100), Liquidity::new(1)) else {
            panic!("expected Ok");
        };
        assert!(pos.is_in_range(tick(0)));
    }

    #[test]
    fn in_range_lower_inclusive() {
        let Ok(pos) = Position::new(tick(-100), tick(100), Liquidity::new(1)) else {
            panic!("expected Ok");
        };
        assert!(pos.is_in_range(tick(-100)));
    }

    #[test]
    fn in_range_upper_exclusive() {
        let Ok(pos) = Position::new(tick(-100), tick(100), Liquidity::new(1)) else {
            panic!("expected Ok");
        };
        assert!(!pos.is_in_range(tick(100)));
    }

    #[test]
    fn out_of_range_below() {
        let Ok(pos) = Position::new(tick(-100), tick(100), Liquidity::new(1)) else {
            panic!("expected Ok");
        };
        assert!(!pos.is_in_range(tick(-101)));
    }

    #[test]
    fn out_of_range_above() {
        let Ok(pos) = Position::new(tick(-100), tick(100), Liquidity::new(1)) else {
            panic!("expected Ok");
        };
        assert!(!pos.is_in_range(tick(101)));
    }

    // -- Display ------------------------------------------------------------

    #[test]
    fn display() {
        let Ok(pos) = Position::new(tick(-100), tick(100), Liquidity::new(500)) else {
            panic!("expected Ok");
        };
        let s = format!("{pos}");
        assert!(s.contains("-100"));
        assert!(s.contains("100"));
        assert!(s.contains("500"));
    }

    // -- Copy ---------------------------------------------------------------

    #[test]
    fn copy_semantics() {
        let Ok(a) = Position::new(tick(-10), tick(10), Liquidity::new(1)) else {
            panic!("expected Ok");
        };
        let b = a;
        assert_eq!(a, b);
    }
}
