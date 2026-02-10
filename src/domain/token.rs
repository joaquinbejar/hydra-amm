//! Token identity type.

use super::{Decimals, TokenAddress};
use crate::error::AmmError;

/// The canonical identity of a token on a given chain.
///
/// Combines a [`TokenAddress`] with its [`Decimals`] to fully describe
/// a token. Two tokens are considered equal only if both address and
/// decimals match.
///
/// # Examples
///
/// ```
/// use hydra_amm::domain::{Decimals, Token, TokenAddress};
///
/// let addr = TokenAddress::from_bytes([1u8; 32]);
/// let dec  = Decimals::new(6).expect("valid");
/// let tok  = Token::new(addr, dec);
///
/// assert_eq!(tok.address(), addr);
/// assert_eq!(tok.decimals(), dec);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Token {
    address: TokenAddress,
    decimals: Decimals,
}

impl Token {
    /// Creates a new `Token`.
    ///
    /// Construction is infallible because both components are already
    /// validated at their own construction site.
    #[must_use]
    pub const fn new(address: TokenAddress, decimals: Decimals) -> Self {
        Self { address, decimals }
    }

    /// Returns the token address.
    #[must_use]
    pub const fn address(&self) -> TokenAddress {
        self.address
    }

    /// Returns the token decimals.
    #[must_use]
    pub const fn decimals(&self) -> Decimals {
        self.decimals
    }

    /// Converts a human-readable amount to the smallest raw unit
    /// for this token.
    ///
    /// For example, `1` USDC (decimals=6) becomes `1_000_000`.
    #[must_use]
    pub const fn to_raw_amount(&self, human: u64) -> u128 {
        self.decimals.scale_up(human)
    }

    /// Converts raw units back to a human-readable amount for this token.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::Overflow`] if the result does not fit in `u64`.
    pub const fn from_raw_amount(&self, raw: u128) -> Result<u64, AmmError> {
        self.decimals.scale_down(raw)
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;

    fn sample_token(addr_byte: u8, dec: u8) -> Token {
        let Ok(d) = Decimals::new(dec) else {
            panic!("invalid decimals in test: {dec}");
        };
        Token::new(TokenAddress::from_bytes([addr_byte; 32]), d)
    }

    #[test]
    fn accessors() {
        let tok = sample_token(1, 6);
        assert_eq!(tok.address(), TokenAddress::from_bytes([1u8; 32]));
        assert_eq!(tok.decimals().get(), 6);
    }

    #[test]
    fn to_raw_amount_usdc() {
        let tok = sample_token(1, 6);
        assert_eq!(tok.to_raw_amount(5), 5_000_000);
    }

    #[test]
    fn from_raw_amount_usdc() {
        let tok = sample_token(1, 6);
        assert_eq!(tok.from_raw_amount(5_000_000), Ok(5));
    }

    #[test]
    fn round_trip() {
        let tok = sample_token(1, 18);
        let raw = tok.to_raw_amount(100);
        let human = tok.from_raw_amount(raw);
        assert_eq!(human, Ok(100));
    }

    #[test]
    fn equality_requires_both_fields() {
        let a = sample_token(1, 6);
        let b = sample_token(1, 8);
        assert_ne!(a, b);
    }

    #[test]
    fn same_token_is_equal() {
        let a = sample_token(1, 6);
        let b = sample_token(1, 6);
        assert_eq!(a, b);
    }

    #[test]
    fn copy_semantics() {
        let a = sample_token(1, 6);
        let b = a;
        assert_eq!(a, b);
    }

    #[test]
    fn debug_format() {
        let tok = sample_token(1, 6);
        let dbg = format!("{tok:?}");
        assert!(dbg.contains("Token"));
    }

    #[test]
    fn hash_consistency() {
        use core::hash::{Hash, Hasher};
        fn hash_of<T: Hash>(t: &T) -> u64 {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            t.hash(&mut h);
            h.finish()
        }
        let a = sample_token(1, 6);
        let b = sample_token(1, 6);
        assert_eq!(hash_of(&a), hash_of(&b));
    }

    #[test]
    fn from_raw_amount_overflow() {
        // u128::MAX with zero decimals => u128::MAX > u64::MAX
        let tok = sample_token(1, 0);
        let result = tok.from_raw_amount(u128::MAX);
        assert!(result.is_err());
    }

    #[test]
    fn to_raw_amount_zero() {
        let tok = sample_token(1, 18);
        assert_eq!(tok.to_raw_amount(0), 0);
    }

    #[test]
    fn different_address_not_equal() {
        let a = sample_token(1, 6);
        let b = sample_token(2, 6);
        assert_ne!(a, b);
    }
}
