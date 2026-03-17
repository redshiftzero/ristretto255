#![deny(clippy::unwrap_used)]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]
// Modeled after https://github.com/penumbra-zone/penumbra/tree/main/crates/crypto/decaf377-ka/src

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

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn scalar_strategy() -> BoxedStrategy<ristretto255::Scalar> {
        any::<[u8; 32]>()
            .prop_map(|bytes| ristretto255::Scalar::from_bytes_mod_order(&bytes))
            .boxed()
    }

    fn point_strategy() -> BoxedStrategy<ristretto255::RistrettoPoint> {
        any::<[u8; 64]>()
            .prop_map(|bytes| ristretto255::RistrettoPoint::from_uniform_bytes(&bytes))
            .boxed()
    }

    proptest! {
        #[test]
        fn key_agreement_works(
            alice_sk in scalar_strategy(),
            bob_sk in scalar_strategy(),
        ) {
            let alice_sk = Secret::new_from_field(alice_sk);
            let bob_sk = Secret::new_from_field(bob_sk);

            let alice_pk = alice_sk.public();
            let bob_pk = bob_sk.public();

            let alice_ss = alice_sk.key_agreement_with(&bob_pk).expect("alice key agreement");
            let bob_ss = bob_sk.key_agreement_with(&alice_pk).expect("bob key agreement");

            prop_assert_eq!(alice_ss, bob_ss);
        }

        #[test]
        fn key_agreement_with_generator_works(
            alice_sk in scalar_strategy(),
            bob_sk in scalar_strategy(),
            gen1 in point_strategy(),
            gen2 in point_strategy(),
        ) {
            let alice_sk = Secret::new_from_field(alice_sk);
            let bob_sk = Secret::new_from_field(bob_sk);

            let alice_pk1 = alice_sk.public_with_generator(&gen1);
            let alice_pk2 = alice_sk.public_with_generator(&gen2);

            let bob_pk1 = bob_sk.public_with_generator(&gen1);
            let bob_pk2 = bob_sk.public_with_generator(&gen2);

            let bob_ss1 = bob_sk.key_agreement_with(&alice_pk1).expect("bob ka gen1");
            let bob_ss2 = bob_sk.key_agreement_with(&alice_pk2).expect("bob ka gen2");

            let alice_ss1 = alice_sk.key_agreement_with(&bob_pk1).expect("alice ka gen1");
            let alice_ss2 = alice_sk.key_agreement_with(&bob_pk2).expect("alice ka gen2");

            prop_assert_eq!(alice_ss1, bob_ss1);
            prop_assert_eq!(alice_ss2, bob_ss2);
        }
    }
}
