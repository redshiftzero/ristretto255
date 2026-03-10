//! Ristretto255 is an implementation of the Ristretto255 prime-order group
//! based on the libcrux family of crates.
//!
//! It is designed to be a drop-in replacement for the `curve25519-dalek` crate.

// TODO Make no_std compatible.
use std::array::TryFromSliceError;

use subtle::{Choice, ConstantTimeEq};

use field::FieldElement;
mod field;

mod traits;
pub use traits::Identity;

pub mod constants;

/// A compressed Ristretto255 point.
#[derive(Copy, Clone, Eq, Hash)]
pub struct CompressedRistretto(pub [u8; 32]);

#[hax_lib::attributes]
#[hax_lib::fstar::verification_status(lax)]
impl PartialEq for CompressedRistretto {
    fn eq(&self, other: &Self) -> bool {
        self.0.ct_eq(&other.0).into()
    }
}

#[hax_lib::attributes]
#[hax_lib::fstar::verification_status(lax)]
impl ConstantTimeEq for CompressedRistretto {
    fn ct_eq(&self, other: &CompressedRistretto) -> Choice {
        self.as_bytes().ct_eq(other.as_bytes())
    }
}

#[hax_lib::attributes]
#[hax_lib::fstar::verification_status(lax)]
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
    #[hax_lib::requires(fstar!("True"))]
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

#[hax_lib::attributes]
#[hax_lib::fstar::verification_status(lax)]
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn upstream_small_multiples_decompress() {
        // Upstream encodings of i*basepoint for i = 0..15.
        // We currently only test decompression validity since point
        // addition/compression APIs are not implemented yet.
        let compressed = [
            CompressedRistretto([
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0,
            ]),
            CompressedRistretto([
                226, 242, 174, 10, 106, 188, 78, 113, 168, 132, 169, 97, 197, 0, 81, 95, 88, 227,
                11, 106, 165, 130, 221, 141, 182, 166, 89, 69, 224, 141, 45, 118,
            ]),
            CompressedRistretto([
                106, 73, 50, 16, 247, 73, 156, 209, 127, 236, 181, 16, 174, 12, 234, 35, 161, 16,
                232, 213, 185, 1, 248, 172, 173, 211, 9, 92, 115, 163, 185, 25,
            ]),
            CompressedRistretto([
                148, 116, 31, 93, 93, 82, 117, 94, 206, 79, 35, 240, 68, 238, 39, 213, 209, 234,
                30, 43, 209, 150, 180, 98, 22, 107, 22, 21, 42, 157, 2, 89,
            ]),
            CompressedRistretto([
                218, 128, 134, 39, 115, 53, 139, 70, 111, 250, 223, 224, 179, 41, 58, 179, 217,
                253, 83, 197, 234, 108, 149, 83, 88, 245, 104, 50, 45, 175, 106, 87,
            ]),
            CompressedRistretto([
                232, 130, 177, 49, 1, 107, 82, 193, 211, 51, 112, 128, 24, 124, 247, 104, 66, 62,
                252, 203, 181, 23, 187, 73, 90, 184, 18, 196, 22, 15, 244, 78,
            ]),
            CompressedRistretto([
                246, 71, 70, 211, 201, 43, 19, 5, 14, 216, 216, 2, 54, 167, 240, 0, 124, 59, 63,
                150, 47, 91, 167, 147, 209, 154, 96, 30, 187, 29, 244, 3,
            ]),
            CompressedRistretto([
                68, 245, 53, 32, 146, 110, 200, 31, 189, 90, 56, 120, 69, 190, 183, 223, 133, 169,
                106, 36, 236, 225, 135, 56, 189, 207, 166, 167, 130, 42, 23, 109,
            ]),
            CompressedRistretto([
                144, 50, 147, 216, 242, 40, 126, 190, 16, 226, 55, 77, 193, 165, 62, 11, 200, 135,
                229, 146, 105, 159, 2, 208, 119, 213, 38, 60, 221, 85, 96, 28,
            ]),
            CompressedRistretto([
                2, 98, 42, 206, 143, 115, 3, 163, 28, 175, 198, 63, 143, 196, 143, 220, 22, 225,
                200, 200, 210, 52, 178, 240, 214, 104, 82, 130, 169, 7, 96, 49,
            ]),
            CompressedRistretto([
                32, 112, 111, 215, 136, 178, 114, 10, 30, 210, 165, 218, 212, 149, 43, 1, 244, 19,
                188, 240, 231, 86, 77, 232, 205, 200, 22, 104, 158, 45, 185, 95,
            ]),
            CompressedRistretto([
                188, 232, 63, 139, 165, 221, 47, 165, 114, 134, 76, 36, 186, 24, 16, 249, 82, 43,
                198, 0, 74, 254, 149, 135, 122, 199, 50, 65, 202, 253, 171, 66,
            ]),
            CompressedRistretto([
                228, 84, 158, 225, 107, 154, 160, 48, 153, 202, 32, 140, 103, 173, 175, 202, 250,
                76, 63, 62, 78, 83, 3, 222, 96, 38, 227, 202, 143, 248, 68, 96,
            ]),
            CompressedRistretto([
                170, 82, 224, 0, 223, 46, 22, 245, 95, 177, 3, 47, 195, 59, 196, 39, 66, 218, 214,
                189, 90, 143, 192, 190, 1, 103, 67, 108, 89, 72, 80, 31,
            ]),
            CompressedRistretto([
                70, 55, 107, 128, 244, 9, 178, 157, 194, 181, 246, 240, 197, 37, 145, 153, 8, 150,
                229, 113, 111, 65, 71, 124, 211, 0, 133, 171, 127, 16, 48, 30,
            ]),
            CompressedRistretto([
                224, 196, 24, 247, 200, 217, 196, 205, 215, 57, 91, 147, 234, 18, 79, 58, 217, 144,
                33, 187, 104, 29, 252, 51, 2, 169, 217, 154, 46, 83, 230, 78,
            ]),
        ];

        for point in compressed {
            assert!(point.decompress().is_some());
        }
    }
}
