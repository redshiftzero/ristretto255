//! Ristretto255 is an implementation of the Ristretto255 prime-order group
//! based on the libcrux family of crates.
//!
//! It is designed to be a drop-in replacement for the `curve25519-dalek` crate.

use curve25519_dalek::traits::Identity;

// TODO Make no_std compatible.
use std::array::TryFromSliceError;

use subtle::{Choice, ConstantTimeEq};

/// A compressed Ristretto255 point.
#[derive(Copy, Clone, Eq, Hash)]
pub struct CompressedRistretto(pub [u8; 32]);

impl PartialEq for CompressedRistretto {
    fn eq(&self, other: &Self) -> bool {
        self.0.ct_eq(&other.0).into()
    }
}

impl ConstantTimeEq for CompressedRistretto {
    fn ct_eq(&self, other: &CompressedRistretto) -> Choice {
        self.as_bytes().ct_eq(other.as_bytes())
    }
}

#[hax_lib::attributes]
impl CompressedRistretto {
    /// Copy the bytes of this `CompressedRistretto`.
    pub const fn to_bytes(&self) -> [u8; 32] {
        self.0
    }

    /// View this `CompressedRistretto` as an array of bytes.
    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    /// Construct a `CompressedRistretto` from a slice of bytes.
    ///
    /// # Errors
    ///
    /// Returns [`TryFromSliceError`] if the input `bytes` slice does not have
    /// a length of 32.
    #[hax_lib::requires(bytes.len() == 32)]
    #[hax_lib::ensures(|r| r.is_ok())]
    pub fn from_slice(bytes: &[u8]) -> Result<CompressedRistretto, TryFromSliceError> {
        bytes.try_into().map(CompressedRistretto)
    }
}

impl Identity for CompressedRistretto {
    fn identity() -> CompressedRistretto {
        CompressedRistretto([0u8; 32])
    }
}

impl Default for CompressedRistretto {
    fn default() -> CompressedRistretto {
        CompressedRistretto::identity()
    }
}

impl TryFrom<&[u8]> for CompressedRistretto {
    type Error = TryFromSliceError;

    fn try_from(slice: &[u8]) -> Result<CompressedRistretto, TryFromSliceError> {
        Self::from_slice(slice)
    }
}
