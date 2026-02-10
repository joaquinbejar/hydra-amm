//! Tick-to-price and price-to-tick conversion functions for concentrated
//! liquidity market makers (CLMM).
//!
//! These helpers implement the standard relationship `price = 1.0001^tick`
//! used by Uniswap v3-style pools.
//!
//! # Functions
//!
//! - [`price_at_tick`] — computes `1.0001^tick` for a given [`Tick`].
//! - [`tick_at_price`] — computes the greatest tick whose price ≤ the
//!   given [`Price`].
//!
//! # Examples
//!
//! ```
//! use hydra_amm::domain::{Price, Tick};
//! use hydra_amm::math::{price_at_tick, tick_at_price};
//!
//! let tick = Tick::new(100).unwrap_or(Tick::ZERO);
//! let price = price_at_tick(tick).expect("valid tick produces valid price");
//! let round_trip = tick_at_price(price).expect("valid price produces valid tick");
//! assert_eq!(round_trip, tick);
//! ```
//!
//! # Precision
//!
//! The current implementation uses `f64` arithmetic (`powf`, `ln`).  A
//! future `fixed-point` variant may use lookup tables and iterative
//! methods for on-chain determinism.

use crate::domain::{Price, Tick};
use crate::error::AmmError;

/// Base of the tick-price exponential: `price = BASE^tick`.
const BASE: f64 = 1.0001;

/// Tolerance for snapping a floating-point tick value to the nearest
/// integer.  This prevents round-trip errors caused by IEEE 754
/// rounding when converting `tick → price → tick`.
const SNAP_EPSILON: f64 = 1e-9;

/// Computes the price at a given tick: `price = 1.0001^tick`.
///
/// All valid [`Tick`] values (in the range `[-887272, 887272]`) produce
/// finite, positive prices within the `f64` representable range.
///
/// # Errors
///
/// Returns [`AmmError::InvalidPrice`] if the computed price is not
/// finite or is negative (should not occur for valid ticks, but
/// guarded for safety).
///
/// # Examples
///
/// ```
/// use hydra_amm::domain::Tick;
/// use hydra_amm::math::price_at_tick;
///
/// let price = price_at_tick(Tick::ZERO).expect("tick 0 is valid");
/// assert!((price.get() - 1.0).abs() < f64::EPSILON);
/// ```
#[must_use = "this returns the computed price and does not modify state"]
pub fn price_at_tick(tick: Tick) -> Result<Price, AmmError> {
    #[allow(clippy::cast_lossless)]
    let price_f64 = BASE.powf(tick.get() as f64);
    Price::new(price_f64)
}

/// Computes the greatest tick whose price is ≤ the given price.
///
/// Implements `floor(log_{1.0001}(price))` with a snap-to-nearest
/// adjustment (within `SNAP_EPSILON`) to guarantee round-trip
/// correctness: `tick_at_price(price_at_tick(t)) == t` for all valid
/// ticks.
///
/// # Errors
///
/// - [`AmmError::InvalidPrice`] if `price` is zero (logarithm
///   undefined).
/// - [`AmmError::InvalidTick`] if the resulting tick falls outside
///   the valid range `[-887272, 887272]`.
///
/// # Examples
///
/// ```
/// use hydra_amm::domain::Price;
/// use hydra_amm::math::tick_at_price;
///
/// let tick = tick_at_price(Price::ONE).expect("price 1.0 is valid");
/// assert_eq!(tick.get(), 0);
/// ```
#[must_use = "this returns the computed tick and does not modify state"]
pub fn tick_at_price(price: Price) -> Result<Tick, AmmError> {
    let p = price.get();
    if p <= 0.0 {
        return Err(AmmError::InvalidPrice(
            "price must be positive for tick conversion",
        ));
    }

    let raw = p.ln() / BASE.ln();

    // Snap to nearest integer when within epsilon to avoid round-trip
    // errors from IEEE 754 imprecision.
    let rounded = raw.round();
    let tick_f64 = if (raw - rounded).abs() < SNAP_EPSILON {
        rounded
    } else {
        raw.floor()
    };

    // Guard against non-finite results (e.g. extremely large prices).
    if !tick_f64.is_finite() {
        return Err(AmmError::InvalidTick(
            "price produces non-finite tick value",
        ));
    }

    // Safe truncation: tick_f64 is finite and within a reasonable range
    // after the floor/round. Values outside i32 will be caught by
    // Tick::new().
    #[allow(clippy::cast_possible_truncation)]
    let tick_i32 = tick_f64 as i32;
    Tick::new(tick_i32)
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;

    // -- price_at_tick ------------------------------------------------------

    #[test]
    fn tick_zero_gives_price_one() {
        let Ok(price) = price_at_tick(Tick::ZERO) else {
            panic!("expected Ok");
        };
        assert!(
            (price.get() - 1.0).abs() < f64::EPSILON,
            "1.0001^0 should be exactly 1.0"
        );
    }

    #[test]
    fn positive_tick_gives_price_above_one() {
        let Ok(tick) = Tick::new(1000) else {
            panic!("expected Ok");
        };
        let Ok(price) = price_at_tick(tick) else {
            panic!("expected Ok");
        };
        assert!(price.get() > 1.0, "positive tick -> price > 1.0");
    }

    #[test]
    fn negative_tick_gives_price_below_one() {
        let Ok(tick) = Tick::new(-1000) else {
            panic!("expected Ok");
        };
        let Ok(price) = price_at_tick(tick) else {
            panic!("expected Ok");
        };
        assert!(
            price.get() > 0.0 && price.get() < 1.0,
            "negative tick -> 0 < price < 1"
        );
    }

    #[test]
    fn min_tick_produces_valid_price() {
        let Ok(price) = price_at_tick(Tick::MIN) else {
            panic!("expected Ok for MIN tick");
        };
        assert!(price.get() > 0.0, "MIN tick should produce positive price");
        assert!(price.is_finite(), "MIN tick price should be finite");
    }

    #[test]
    fn max_tick_produces_valid_price() {
        let Ok(price) = price_at_tick(Tick::MAX) else {
            panic!("expected Ok for MAX tick");
        };
        assert!(price.get() > 1.0, "MAX tick should produce price > 1");
        assert!(price.is_finite(), "MAX tick price should be finite");
    }

    #[test]
    fn tick_one_is_base() {
        let Ok(tick) = Tick::new(1) else {
            panic!("expected Ok");
        };
        let Ok(price) = price_at_tick(tick) else {
            panic!("expected Ok");
        };
        assert!(
            (price.get() - 1.0001).abs() < 1e-12,
            "1.0001^1 should equal 1.0001"
        );
    }

    #[test]
    fn tick_minus_one_is_inverse_base() {
        let Ok(tick) = Tick::new(-1) else {
            panic!("expected Ok");
        };
        let Ok(price) = price_at_tick(tick) else {
            panic!("expected Ok");
        };
        let expected = 1.0 / 1.0001;
        assert!(
            (price.get() - expected).abs() < 1e-12,
            "1.0001^(-1) should equal 1/1.0001"
        );
    }

    // -- tick_at_price ------------------------------------------------------

    #[test]
    fn price_one_gives_tick_zero() {
        let Ok(tick) = tick_at_price(Price::ONE) else {
            panic!("expected Ok");
        };
        assert_eq!(tick.get(), 0);
    }

    #[test]
    fn price_zero_is_error() {
        let result = tick_at_price(Price::ZERO);
        assert!(result.is_err(), "price 0 should fail");
    }

    #[test]
    fn price_above_one_gives_positive_tick() {
        let Ok(price) = Price::new(2.0) else {
            panic!("expected Ok");
        };
        let Ok(tick) = tick_at_price(price) else {
            panic!("expected Ok");
        };
        assert!(tick.get() > 0, "price > 1 -> positive tick");
    }

    #[test]
    fn price_below_one_gives_negative_tick() {
        let Ok(price) = Price::new(0.5) else {
            panic!("expected Ok");
        };
        let Ok(tick) = tick_at_price(price) else {
            panic!("expected Ok");
        };
        assert!(tick.get() < 0, "price < 1 -> negative tick");
    }

    #[test]
    fn price_at_base_gives_tick_one() {
        let Ok(price) = Price::new(1.0001) else {
            panic!("expected Ok");
        };
        let Ok(tick) = tick_at_price(price) else {
            panic!("expected Ok");
        };
        assert_eq!(tick.get(), 1);
    }

    // -- Round-trip ----------------------------------------------------------

    #[test]
    fn round_trip_tick_zero() {
        let Ok(price) = price_at_tick(Tick::ZERO) else {
            panic!("expected Ok");
        };
        let Ok(tick) = tick_at_price(price) else {
            panic!("expected Ok");
        };
        assert_eq!(tick, Tick::ZERO);
    }

    #[test]
    fn round_trip_positive_ticks() {
        for t in [1, 10, 100, 1_000, 10_000, 100_000, 500_000, 887_272] {
            let Ok(tick) = Tick::new(t) else {
                panic!("expected Ok for tick {t}");
            };
            let Ok(price) = price_at_tick(tick) else {
                panic!("expected Ok for price_at_tick({t})");
            };
            let Ok(rt) = tick_at_price(price) else {
                panic!("expected Ok for tick_at_price");
            };
            assert_eq!(rt, tick, "round-trip failed for tick {t}");
        }
    }

    #[test]
    fn round_trip_negative_ticks() {
        for t in [-1, -10, -100, -1_000, -10_000, -100_000, -500_000, -887_272] {
            let Ok(tick) = Tick::new(t) else {
                panic!("expected Ok for tick {t}");
            };
            let Ok(price) = price_at_tick(tick) else {
                panic!("expected Ok for price_at_tick({t})");
            };
            let Ok(rt) = tick_at_price(price) else {
                panic!("expected Ok for tick_at_price");
            };
            assert_eq!(rt, tick, "round-trip failed for tick {t}");
        }
    }

    // -- Monotonicity -------------------------------------------------------

    #[test]
    fn monotonicity_increasing() {
        let ticks: &[i32] = &[-887_272, -10_000, -1_000, -1, 0, 1, 1_000, 10_000, 887_272];
        let prices: Vec<f64> = ticks
            .iter()
            .map(|&t| {
                let Ok(tick) = Tick::new(t) else {
                    panic!("expected Ok");
                };
                let Ok(price) = price_at_tick(tick) else {
                    panic!("expected Ok");
                };
                price.get()
            })
            .collect();

        for pair in prices.windows(2) {
            let [prev, next] = pair else {
                panic!("windows(2) should yield pairs");
            };
            assert!(next > prev, "prices must be strictly increasing");
        }
    }

    // -- Floor convention ---------------------------------------------------

    #[test]
    fn tick_at_price_floors_non_aligned_price() {
        // A price between tick 0 (price 1.0) and tick 1 (price 1.0001)
        // should map to tick 0 (floor).
        let Ok(price) = Price::new(1.00005) else {
            panic!("expected Ok");
        };
        let Ok(tick) = tick_at_price(price) else {
            panic!("expected Ok");
        };
        assert_eq!(
            tick.get(),
            0,
            "price between tick 0 and 1 should floor to 0"
        );
    }

    #[test]
    fn tick_at_price_floors_negative_non_aligned() {
        // A price between tick -1 and tick 0 should map to tick -1.
        let Ok(price) = Price::new(0.99995) else {
            panic!("expected Ok");
        };
        let Ok(tick) = tick_at_price(price) else {
            panic!("expected Ok");
        };
        assert_eq!(
            tick.get(),
            -1,
            "price between tick -1 and 0 should floor to -1"
        );
    }

    // -- Known values -------------------------------------------------------

    #[test]
    fn price_at_tick_2000() {
        let Ok(tick) = Tick::new(2000) else {
            panic!("expected Ok");
        };
        let Ok(price) = price_at_tick(tick) else {
            panic!("expected Ok");
        };
        // 1.0001^2000 ≈ 1.2214...
        let expected = 1.0001_f64.powf(2000.0);
        assert!(
            (price.get() - expected).abs() < 1e-10,
            "price_at_tick(2000) should match direct computation"
        );
    }

    #[test]
    fn tick_at_known_price_2() {
        // log_{1.0001}(2) = ln(2) / ln(1.0001) ≈ 6931.47...
        // floor → 6931
        let Ok(price) = Price::new(2.0) else {
            panic!("expected Ok");
        };
        let Ok(tick) = tick_at_price(price) else {
            panic!("expected Ok");
        };
        assert_eq!(tick.get(), 6931);
    }

    // -- Adjacent tick round-trips ------------------------------------------

    #[test]
    fn round_trip_adjacent_positive_ticks() {
        // Test consecutive ticks around an interesting range
        for t in 99..=101 {
            let Ok(tick) = Tick::new(t) else {
                panic!("expected Ok for tick {t}");
            };
            let Ok(price) = price_at_tick(tick) else {
                panic!("expected Ok for price_at_tick({t})");
            };
            let Ok(rt) = tick_at_price(price) else {
                panic!("expected Ok for tick_at_price");
            };
            assert_eq!(rt, tick, "round-trip failed for adjacent tick {t}");
        }
    }

    #[test]
    fn round_trip_adjacent_negative_ticks() {
        for t in -101..=-99 {
            let Ok(tick) = Tick::new(t) else {
                panic!("expected Ok for tick {t}");
            };
            let Ok(price) = price_at_tick(tick) else {
                panic!("expected Ok for price_at_tick({t})");
            };
            let Ok(rt) = tick_at_price(price) else {
                panic!("expected Ok for tick_at_price");
            };
            assert_eq!(rt, tick, "round-trip failed for adjacent tick {t}");
        }
    }

    // -- Symmetry -----------------------------------------------------------

    #[test]
    fn price_symmetry_positive_negative() {
        // price_at_tick(t) * price_at_tick(-t) ≈ 1.0
        for t in [1, 10, 100, 1_000, 10_000] {
            let Ok(tick_pos) = Tick::new(t) else {
                panic!("expected Ok");
            };
            let Ok(tick_neg) = Tick::new(-t) else {
                panic!("expected Ok");
            };
            let Ok(p_pos) = price_at_tick(tick_pos) else {
                panic!("expected Ok");
            };
            let Ok(p_neg) = price_at_tick(tick_neg) else {
                panic!("expected Ok");
            };
            let product = p_pos.get() * p_neg.get();
            assert!(
                (product - 1.0).abs() < 1e-10,
                "symmetry failed for tick {t}: product = {product}"
            );
        }
    }

    // -- Precision ----------------------------------------------------------

    #[test]
    fn tick_at_price_near_boundary() {
        // Price just above tick 0 boundary (1.0 + tiny epsilon)
        let Ok(price) = Price::new(1.0 + 1e-15) else {
            panic!("expected Ok");
        };
        let Ok(tick) = tick_at_price(price) else {
            panic!("expected Ok");
        };
        // Should be tick 0 since the price is extremely close to 1.0
        assert_eq!(tick.get(), 0);
    }
}
