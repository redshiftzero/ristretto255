use rand_core::{CryptoRng, RngCore};
use zeroize::Zeroize;

/// A scalar value for the ristretto255 group.
///
/// Scalars are integers mod ℓ, where ℓ is the order of the ristretto255 group.
#[derive(Clone, Debug, Zeroize, PartialEq, Eq)]
pub struct Scalar([u8; 32]);

impl Scalar {
    /// Generate a random scalar using the provided RNG.
    pub fn random<R: RngCore + CryptoRng>(_rng: &mut R) -> Self {
        unimplemented!()
    }

    /// Attempt to construct a scalar from a canonical byte representation.
    ///
    /// Returns `None` if the bytes do not represent a canonical scalar
    /// (i.e. the value is >= ℓ).
    pub fn from_bytes_checked(_bytes: &[u8; 32]) -> Option<Self> {
        unimplemented!()
    }

    /// Construct a scalar by reducing a 256-bit little-endian integer modulo ℓ.
    ///
    /// Unlike [`from_bytes_checked`](Self::from_bytes_checked), this always
    /// succeeds by reducing the input mod the group order.
    pub fn from_bytes_mod_order(_bytes: &[u8; 32]) -> Self {
        unimplemented!()
    }

    /// Serialize this scalar to a 32-byte little-endian array.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0
    }
}
