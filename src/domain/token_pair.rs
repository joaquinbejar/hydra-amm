//! Ordered pair of distinct tokens.

use super::Token;
use crate::error::AmmError;

/// An ordered pair of distinct tokens, canonically sorted by address.
///
/// The canonical ordering guarantees that `token_a.address() < token_b.address()`,
/// preventing duplicate pairs such as `(A, B)` and `(B, A)`.
///
/// # Examples
///
/// ```
/// use hydra_amm::domain::{Decimals, Token, TokenAddress, TokenPair};
///
/// let tok_a = Token::new(TokenAddress::from_bytes([1u8; 32]), Decimals::new(6).expect("valid"));
/// let tok_b = Token::new(TokenAddress::from_bytes([2u8; 32]), Decimals::new(18).expect("valid"));
///
/// // Order is enforced automatically:
/// let pair = TokenPair::new(tok_b, tok_a).expect("distinct tokens");
/// assert_eq!(pair.first(), tok_a);
/// assert_eq!(pair.second(), tok_b);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TokenPair {
    token_a: Token,
    token_b: Token,
}

impl TokenPair {
    /// Creates a new canonically-ordered `TokenPair`.
    ///
    /// The two tokens are automatically sorted so that
    /// `token_a.address() < token_b.address()`.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::InvalidToken`] if both tokens have the same address.
    pub fn new(token1: Token, token2: Token) -> Result<Self, AmmError> {
        if token1.address() == token2.address() {
            return Err(AmmError::InvalidToken(
                "token pair requires two distinct addresses",
            ));
        }

        let (token_a, token_b) = if token1.address() < token2.address() {
            (token1, token2)
        } else {
            (token2, token1)
        };

        Ok(Self { token_a, token_b })
    }

    /// Returns the first token (lower address).
    #[must_use]
    pub const fn first(&self) -> Token {
        self.token_a
    }

    /// Returns the second token (higher address).
    #[must_use]
    pub const fn second(&self) -> Token {
        self.token_b
    }

    /// Returns `true` if the given token is part of this pair.
    #[must_use]
    pub fn contains(&self, token: &Token) -> bool {
        self.token_a == *token || self.token_b == *token
    }

    /// Returns the counterpart of `token` in this pair.
    ///
    /// # Errors
    ///
    /// Returns [`AmmError::InvalidToken`] if `token` is not in the pair.
    pub fn other(&self, token: &Token) -> Result<Token, AmmError> {
        if *token == self.token_a {
            Ok(self.token_b)
        } else if *token == self.token_b {
            Ok(self.token_a)
        } else {
            Err(AmmError::InvalidToken("token is not part of this pair"))
        }
    }

    /// Returns `true` if the pair is in canonical order.
    ///
    /// Always returns `true` for a validly constructed `TokenPair`.
    #[must_use]
    pub fn is_ordered_correctly(&self) -> bool {
        self.token_a.address() < self.token_b.address()
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;
    use crate::domain::{Decimals, TokenAddress};

    fn tok(addr_byte: u8, dec: u8) -> Token {
        let Ok(d) = Decimals::new(dec) else {
            panic!("invalid decimals in test: {dec}");
        };
        Token::new(TokenAddress::from_bytes([addr_byte; 32]), d)
    }

    #[test]
    fn valid_pair_preserves_order() {
        let a = tok(1, 6);
        let b = tok(2, 18);
        let Ok(pair) = TokenPair::new(a, b) else {
            panic!("expected Ok");
        };
        assert_eq!(pair.first(), a);
        assert_eq!(pair.second(), b);
    }

    #[test]
    fn auto_sorts_reversed_input() {
        let a = tok(1, 6);
        let b = tok(2, 18);
        let Ok(pair) = TokenPair::new(b, a) else {
            panic!("expected Ok");
        };
        assert_eq!(pair.first(), a);
        assert_eq!(pair.second(), b);
        assert!(pair.is_ordered_correctly());
    }

    #[test]
    fn rejects_same_address() {
        let a = tok(1, 6);
        let b = tok(1, 18);
        let Err(e) = TokenPair::new(a, b) else {
            panic!("expected Err");
        };
        assert_eq!(
            e,
            AmmError::InvalidToken("token pair requires two distinct addresses")
        );
    }

    #[test]
    fn contains_first() {
        let a = tok(1, 6);
        let b = tok(2, 18);
        let Ok(pair) = TokenPair::new(a, b) else {
            panic!("expected Ok");
        };
        assert!(pair.contains(&a));
    }

    #[test]
    fn contains_second() {
        let a = tok(1, 6);
        let b = tok(2, 18);
        let Ok(pair) = TokenPair::new(a, b) else {
            panic!("expected Ok");
        };
        assert!(pair.contains(&b));
    }

    #[test]
    fn does_not_contain_foreign() {
        let a = tok(1, 6);
        let b = tok(2, 18);
        let c = tok(3, 8);
        let Ok(pair) = TokenPair::new(a, b) else {
            panic!("expected Ok");
        };
        assert!(!pair.contains(&c));
    }

    #[test]
    fn other_returns_counterpart() {
        let a = tok(1, 6);
        let b = tok(2, 18);
        let Ok(pair) = TokenPair::new(a, b) else {
            panic!("expected Ok");
        };
        assert_eq!(pair.other(&a), Ok(b));
        assert_eq!(pair.other(&b), Ok(a));
    }

    #[test]
    fn other_rejects_foreign() {
        let a = tok(1, 6);
        let b = tok(2, 18);
        let c = tok(3, 8);
        let Ok(pair) = TokenPair::new(a, b) else {
            panic!("expected Ok");
        };
        assert!(pair.other(&c).is_err());
    }

    #[test]
    fn equality_of_pairs() {
        let a = tok(1, 6);
        let b = tok(2, 18);
        let (Ok(p1), Ok(p2)) = (TokenPair::new(a, b), TokenPair::new(b, a)) else {
            panic!("expected Ok");
        };
        assert_eq!(p1, p2);
    }

    #[test]
    fn copy_semantics() {
        let a = tok(1, 6);
        let b = tok(2, 18);
        let Ok(p) = TokenPair::new(a, b) else {
            panic!("expected Ok");
        };
        let p2 = p;
        assert_eq!(p, p2);
    }
}
