#![deny(clippy::unwrap_used)]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]

use std::convert::{TryFrom, TryInto};

use rand_core::{CryptoRng, RngCore};
use zeroize::Zeroize;

/// A public key sent to the counterparty in the key agreement protocol.
///
/// This is a refinement type around `[u8; 32]` that marks the bytes as being a
/// public key.  Not all 32-byte arrays are valid public keys; invalid public
/// keys will error during key agreement.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Public(pub [u8; 32]);

/// A secret key used to perform key agreement using the counterparty's public key.
#[derive(Clone, Zeroize, PartialEq, Eq)]
#[zeroize(drop)]
pub struct Secret(ristretto255::Scalar);

/// The shared secret derived at the end of the key agreement protocol.
#[derive(PartialEq, Eq, Clone, Zeroize)]
#[zeroize(drop)]
pub struct SharedSecret(pub [u8; 32]);

/// An error during key agreement.
#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Invalid public key")]
    InvalidPublic(Public),
    #[error("Invalid secret key")]
    InvalidSecret,
    #[error("Supplied bytes are incorrect length")]
    SliceLenError,
}

impl Secret {
    /// Generate a new secret key using `rng`.
    pub fn new<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        Self(ristretto255::Scalar::random(rng))
    }

    /// Use the supplied scalar as the secret key directly.
    ///
    /// # Warning
    ///
    /// This function exists to allow custom key derivation; it's the caller's
    /// responsibility to ensure that the input was generated securely.
    pub fn new_from_field(sk: ristretto255::Scalar) -> Self {
        Self(sk)
    }

    /// Derive a public key for this secret key, using the conventional
    /// ristretto255 basepoint.
    pub fn public(&self) -> Public {
        self.public_with_generator(&ristretto255::RistrettoPoint::basepoint())
    }

    /// Derive a public key for this secret key, using the provided `generator`.
    pub fn public_with_generator(&self, generator: &ristretto255::RistrettoPoint) -> Public {
        Public((&self.0 * generator).compress().into())
    }

    /// Perform key agreement with the provided public key.
    ///
    /// Fails if the provided public key is invalid.
    pub fn key_agreement_with(&self, other: &Public) -> Result<SharedSecret, Error> {
        let pk = ristretto255::CompressedRistretto(other.0)
            .decompress()
            .ok_or(Error::InvalidPublic(*other))?;

        Ok(SharedSecret((&self.0 * &pk).compress().into()))
    }

    /// Convert this shared secret to bytes.
    ///
    /// Convenience wrapper around an [`Into`] impl.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.into()
    }
}

impl std::fmt::Debug for Public {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "ristretto255_ka::Public({})",
            hex::encode(self.0)
        ))
    }
}

impl std::fmt::Debug for Secret {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let bytes = self.0.to_bytes();
        f.write_fmt(format_args!(
            "ristretto255_ka::Secret({})",
            hex::encode(bytes)
        ))
    }
}

impl std::fmt::Debug for SharedSecret {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "ristretto255_ka::SharedSecret({})",
            hex::encode(self.0)
        ))
    }
}

impl TryFrom<&[u8]> for Public {
    type Error = Error;

    fn try_from(slice: &[u8]) -> Result<Public, Error> {
        let bytes: [u8; 32] = slice.try_into().map_err(|_| Error::SliceLenError)?;
        Ok(Public(bytes))
    }
}

impl TryFrom<&[u8]> for Secret {
    type Error = Error;

    fn try_from(slice: &[u8]) -> Result<Secret, Error> {
        let bytes: [u8; 32] = slice.try_into().map_err(|_| Error::SliceLenError)?;
        bytes.try_into()
    }
}

impl TryFrom<[u8; 32]> for Secret {
    type Error = Error;
    fn try_from(bytes: [u8; 32]) -> Result<Secret, Error> {
        let x = ristretto255::Scalar::from_bytes_checked(&bytes).ok_or(Error::InvalidSecret)?;
        Ok(Secret(x))
    }
}

impl TryFrom<[u8; 32]> for SharedSecret {
    type Error = Error;
    fn try_from(bytes: [u8; 32]) -> Result<SharedSecret, Error> {
        ristretto255::CompressedRistretto(bytes)
            .decompress()
            .ok_or(Error::InvalidSecret)?;

        Ok(SharedSecret(bytes))
    }
}

impl From<&Secret> for [u8; 32] {
    fn from(s: &Secret) -> Self {
        s.0.to_bytes()
    }
}
