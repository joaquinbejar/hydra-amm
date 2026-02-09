//! Rounding helpers for integer division.
//!
//! This module provides [`div_round`], a free function that performs `u128`
//! division with an explicit [`Rounding`] direction.  It is the low-level
//! building block used by domain types such as [`Amount`](crate::domain::Amount)
//! and [`Liquidity`](crate::domain::Liquidity).
//!
//! # Convention
//!
//! **Always round against the user** (protocol-favorable):
//!
//! | Quantity | Direction | Rationale |
//! |----------|-----------|-----------|
//! | Output amount | [`Rounding::Down`] | User receives less |
//! | Input amount | [`Rounding::Up`] | User pays more |
//! | Fee amount | [`Rounding::Up`] | Protocol takes more |
//!
//! # Examples
//!
//! ```
//! use hydra_amm::domain::Rounding;
//! use hydra_amm::math::div_round;
//!
//! assert_eq!(div_round(10, 3, Rounding::Down), Some(3));
//! assert_eq!(div_round(10, 3, Rounding::Up), Some(4));
//! assert_eq!(div_round(0, 5, Rounding::Up), Some(0));
//! assert_eq!(div_round(10, 0, Rounding::Down), None);
//! ```

use crate::domain::Rounding;

/// Integer division of `u128` values with explicit rounding direction.
///
/// - [`Rounding::Down`]: floor division (round towards zero).
/// - [`Rounding::Up`]: ceiling division — returns the smallest integer
///   ≥ the exact quotient.
///
/// Returns [`None`] if `denominator` is zero.
///
/// # Examples
///
/// ```
/// use hydra_amm::domain::Rounding;
/// use hydra_amm::math::div_round;
///
/// // Exact division: both directions agree
/// assert_eq!(div_round(10, 5, Rounding::Down), Some(2));
/// assert_eq!(div_round(10, 5, Rounding::Up), Some(2));
///
/// // Non-exact division: Up rounds toward +∞
/// assert_eq!(div_round(7, 2, Rounding::Down), Some(3));
/// assert_eq!(div_round(7, 2, Rounding::Up), Some(4));
/// ```
#[must_use]
pub const fn div_round(numerator: u128, denominator: u128, rounding: Rounding) -> Option<u128> {
    if denominator == 0 {
        return None;
    }
    match rounding {
        Rounding::Down => Some(numerator / denominator),
        Rounding::Up => {
            // Ceiling division: (n + d - 1) / d
            // Guard against overflow of (n + d - 1).
            match numerator.checked_add(denominator - 1) {
                Some(adjusted) => Some(adjusted / denominator),
                None => {
                    // Fallback: ceil(n / d) = floor(n / d) + (n % d != 0) as u128
                    let q = numerator / denominator;
                    let r = numerator % denominator;
                    if r != 0 {
                        // q + 1 cannot overflow: if n == u128::MAX and d == 1 then
                        // r == 0, so we never reach this branch with q == u128::MAX.
                        Some(q + 1)
                    } else {
                        Some(q)
                    }
                }
            }
        }
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;

    // -- Division by zero ---------------------------------------------------

    #[test]
    fn div_by_zero_returns_none() {
        assert_eq!(div_round(100, 0, Rounding::Down), None);
        assert_eq!(div_round(100, 0, Rounding::Up), None);
        assert_eq!(div_round(0, 0, Rounding::Down), None);
    }

    // -- Zero numerator -----------------------------------------------------

    #[test]
    fn zero_numerator_down() {
        assert_eq!(div_round(0, 5, Rounding::Down), Some(0));
    }

    #[test]
    fn zero_numerator_up() {
        assert_eq!(div_round(0, 5, Rounding::Up), Some(0));
    }

    // -- Exact division (no remainder) --------------------------------------

    #[test]
    fn exact_division_down() {
        assert_eq!(div_round(100, 10, Rounding::Down), Some(10));
    }

    #[test]
    fn exact_division_up() {
        assert_eq!(div_round(100, 10, Rounding::Up), Some(10));
    }

    #[test]
    fn exact_division_by_one() {
        assert_eq!(div_round(42, 1, Rounding::Down), Some(42));
        assert_eq!(div_round(42, 1, Rounding::Up), Some(42));
    }

    // -- Non-exact division (remainder present) -----------------------------

    #[test]
    fn remainder_round_down() {
        assert_eq!(div_round(10, 3, Rounding::Down), Some(3));
    }

    #[test]
    fn remainder_round_up() {
        assert_eq!(div_round(10, 3, Rounding::Up), Some(4));
    }

    #[test]
    fn remainder_one_less_round_down() {
        // 9 / 10 = 0 remainder 9
        assert_eq!(div_round(9, 10, Rounding::Down), Some(0));
    }

    #[test]
    fn remainder_one_less_round_up() {
        // 9 / 10 → ceil = 1
        assert_eq!(div_round(9, 10, Rounding::Up), Some(1));
    }

    #[test]
    fn remainder_one_round_up() {
        // 1 / u128::MAX → ceil = 1
        assert_eq!(div_round(1, u128::MAX, Rounding::Up), Some(1));
    }

    // -- Large values -------------------------------------------------------

    #[test]
    fn max_divided_by_one() {
        assert_eq!(div_round(u128::MAX, 1, Rounding::Down), Some(u128::MAX));
        assert_eq!(div_round(u128::MAX, 1, Rounding::Up), Some(u128::MAX));
    }

    #[test]
    fn max_divided_by_two_down() {
        // floor(MAX / 2) = 170141183460469231731687303715884105727
        let expected = u128::MAX / 2;
        assert_eq!(div_round(u128::MAX, 2, Rounding::Down), Some(expected));
    }

    #[test]
    fn max_divided_by_two_up() {
        // ceil(MAX / 2) = floor(MAX / 2) + 1
        let expected = u128::MAX / 2 + 1;
        assert_eq!(div_round(u128::MAX, 2, Rounding::Up), Some(expected));
    }

    #[test]
    fn max_divided_by_max() {
        assert_eq!(div_round(u128::MAX, u128::MAX, Rounding::Down), Some(1));
        assert_eq!(div_round(u128::MAX, u128::MAX, Rounding::Up), Some(1));
    }

    #[test]
    fn max_divided_by_max_minus_one_up() {
        // MAX / (MAX - 1): quotient = 1, remainder = 1 → ceil = 2
        assert_eq!(div_round(u128::MAX, u128::MAX - 1, Rounding::Up), Some(2));
    }

    // -- Overflow fallback path in ceiling division -------------------------

    #[test]
    fn ceiling_overflow_fallback_with_remainder() {
        // numerator = MAX, denominator = 3
        // (MAX + 2) overflows, so fallback path is used.
        // floor(MAX / 3) = 113427455640312821154458202477256070485
        // MAX % 3 = 0? Let's check: MAX = 2^128 - 1 = 340282366920938463463374607431768211455
        // 340282366920938463463374607431768211455 / 3 = 113427455640312821154458202477256070485
        // 113427455640312821154458202477256070485 * 3 = 340282366920938463463374607431768211455
        // remainder = 0, so exact. Let's use a denominator that gives a remainder.
        // MAX / (MAX / 2) where MAX is odd:
        // MAX = 340282366920938463463374607431768211455
        // MAX / 2 = 170141183460469231731687303715884105727
        // MAX / 170141183460469231731687303715884105727 = 2, remainder = 1
        let d = u128::MAX / 2;
        assert_eq!(div_round(u128::MAX, d, Rounding::Down), Some(2));
        assert_eq!(div_round(u128::MAX, d, Rounding::Up), Some(3));
    }

    #[test]
    fn ceiling_overflow_fallback_exact() {
        // Use a large denominator that divides MAX evenly.
        // MAX + 1 = 2^128, so MAX = 2^128 - 1. No power of 2 divides MAX evenly.
        // But (MAX / 5) * 5 might equal MAX if MAX % 5 == 0.
        // 340282366920938463463374607431768211455 % 5 = 0 (since 2^128 - 1 = ...5)
        let d = u128::MAX / 5;
        // d * 5 = MAX (verify by checking remainder)
        let remainder = u128::MAX - d * 5;
        assert_eq!(remainder, 0, "precondition: MAX is divisible by 5");
        assert_eq!(div_round(u128::MAX, d, Rounding::Down), Some(5));
        assert_eq!(div_round(u128::MAX, d, Rounding::Up), Some(5));
    }

    // -- Protocol convention examples ---------------------------------------

    #[test]
    fn protocol_convention_output_rounds_down() {
        // User gets 3 tokens out of 10/3
        assert_eq!(div_round(10, 3, Rounding::Down), Some(3));
    }

    #[test]
    fn protocol_convention_fee_rounds_up() {
        // Protocol collects 4 fee units out of 10/3
        assert_eq!(div_round(10, 3, Rounding::Up), Some(4));
    }
}
