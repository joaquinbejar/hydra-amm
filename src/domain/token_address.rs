//! Chain-agnostic token address.

/// A generic, chain-agnostic address representing a token on any blockchain.
///
/// Wraps a fixed-size `[u8; 32]` byte array. All 32-byte sequences are
/// considered valid addresses, so construction is infallible.
///
/// # Examples
///
/// ```
/// use hydra_amm::domain::TokenAddress;
///
/// let addr = TokenAddress::from_bytes([1u8; 32]);
/// assert_eq!(addr.as_bytes(), [1u8; 32]);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TokenAddress([u8; 32]);

impl TokenAddress {
    /// Creates a `TokenAddress` from raw bytes.
    #[must_use]
    pub const fn from_bytes(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    /// Returns the underlying 32-byte representation.
    #[must_use]
    pub const fn as_bytes(&self) -> [u8; 32] {
        self.0
    }

    /// Returns the all-zero address.
    ///
    /// Useful as a sentinel or placeholder value; use sparingly.
    #[must_use]
    pub const fn zero() -> Self {
        Self([0u8; 32])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_bytes_round_trip() {
        let bytes = [42u8; 32];
        let addr = TokenAddress::from_bytes(bytes);
        assert_eq!(addr.as_bytes(), bytes);
    }

    #[test]
    fn zero_is_all_zeros() {
        let addr = TokenAddress::zero();
        assert_eq!(addr.as_bytes(), [0u8; 32]);
    }

    #[test]
    fn equality_same_bytes() {
        let a = TokenAddress::from_bytes([1u8; 32]);
        let b = TokenAddress::from_bytes([1u8; 32]);
        assert_eq!(a, b);
    }

    #[test]
    fn inequality_different_bytes() {
        let a = TokenAddress::from_bytes([1u8; 32]);
        let b = TokenAddress::from_bytes([2u8; 32]);
        assert_ne!(a, b);
    }

    #[test]
    fn ordering_is_lexicographic() {
        let lo = TokenAddress::from_bytes([0u8; 32]);
        let hi = TokenAddress::from_bytes([1u8; 32]);
        assert!(lo < hi);
    }

    #[test]
    fn copy_semantics() {
        let a = TokenAddress::from_bytes([5u8; 32]);
        let b = a;
        assert_eq!(a, b);
    }

    #[test]
    fn debug_format() {
        let addr = TokenAddress::zero();
        let dbg = format!("{addr:?}");
        assert!(dbg.contains("TokenAddress"));
    }
}
