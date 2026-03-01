//! Ristretto255 is an implementation of the Ristretto255 prime-order group
//! based on the libcrux family of crates.
//!
//! It is designed to be a drop-in replacement for the `curve25519-dalek` crate.

use curve25519_dalek::traits::Identity;

// TODO Make no_std compatible.
use std::array::TryFromSliceError;

use subtle::{Choice, ConstantTimeEq};

pub use field::FieldElement;
mod field;

pub mod constants;

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

    /// Attempt to decompress to an `RistrettoPoint`.
    ///
    /// # Return
    ///
    /// - `Some(RistrettoPoint)` if `self` was the canonical encoding of a point;
    ///
    /// - `None` if `self` was not the canonical encoding of a point.
    pub fn decompress(&self) -> Option<RistrettoPoint> {
        let (s_encoding_is_canonical, s_is_negative, s) = decompress::step_1(self);

        if (!s_encoding_is_canonical | s_is_negative).into() {
            return None;
        }

        let (ok, t_is_negative, y_is_zero, res) = decompress::step_2(s);

        if (!ok | t_is_negative | y_is_zero).into() {
            None
        } else {
            Some(res)
        }
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

mod decompress {
    use super::*;

    pub(super) fn step_1(repr: &CompressedRistretto) -> (Choice, Choice, FieldElement) {
        // Step 1. Check s for validity:
        // 1.a) s must be 32 bytes
        // 1.b) s < p
        // 1.c) s is nonnegative
        let s = FieldElement::from_bytes(repr.as_bytes());
        let s_bytes_check = s.to_bytes();
        let s_encoding_is_canonical = s_bytes_check[..].ct_eq(repr.as_bytes());
        let s_is_negative = s.is_negative();

        (s_encoding_is_canonical, s_is_negative, s)
    }

        pub(super) fn step_2(s: FieldElement) -> (Choice, Choice, Choice, RistrettoPoint) {
            // Step 2.  Compute (X:Y:Z:T).
            let one = FieldElement::ONE;
            let ss = s.square();
            let u1 = &one - &ss; //  1 + as²
            let u2 = &one + &ss; //  1 - as²    where a=-1
            let u2_sqr = u2.square(); // (1 - as²)²

            // v == ad(1+as²)² - (1-as²)²            where d=-121665/121666
            let v = &(&(-&constants::EDWARDS_D) * &u1.square()) - &u2_sqr;

            let (ok, I) = (&v * &u2_sqr).invsqrt(); // 1/sqrt(v*u_2²)

            let Dx = &I * &u2; // 1/sqrt(v)
            let Dy = &I * &(&Dx * &v); // 1/u2

            // x == | 2s/sqrt(v) | == + sqrt(4s²/(ad(1+as²)² - (1-as²)²))
            let mut x = &(&s + &s) * &Dx;
            let x_neg = x.is_negative();
            x.conditional_negate(x_neg);

            // y == (1-as²)/(1+as²)
            let y = &u1 * &Dy;

            // t == ((1+as²) sqrt(4s²/(ad(1+as²)² - (1-as²)²)))/(1-as²)
            let t = &x * &y;

            (
                ok,
                t.is_negative(),
                y.is_zero(),
                RistrettoPoint(EdwardsPoint {
                    X: x,
                    Y: y,
                    Z: one,
                    T: t,
                }),
            )
        }
}

// TODO: These might go away
struct RistrettoPoint(pub EdwardsPoint);

struct EdwardsPoint {
    X: FieldElement,
    Y: FieldElement,
    Z: FieldElement,
    T: FieldElement,
}
