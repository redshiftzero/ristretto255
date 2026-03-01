use curve25519_dalek::traits::Identity;
use std::ops::{Add, Mul, Neg, Sub};
use subtle::{Choice, ConstantTimeEq};

// To get access to the field element functions (represented upstream in the verified
// core as 5 u64 limbs), we need to use the hacl-rs crate directly.
pub use libcrux_hacl_rs::bignum25519_51 as hacl;
use libcrux_hacl_rs::fstar::uint128;

use crate::constants;

// TODO: Make FieldElement pub(crate)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldElement(pub [u64; 5]);

impl Identity for FieldElement {
    fn identity() -> Self {
        Self([0; 5])
    }
}

impl ConstantTimeEq for FieldElement {
    /// Test equality between two `FieldElement`s. Since the internal
    /// representation is not canonical, normalize to wire format first.
    fn ct_eq(&self, other: &FieldElement) -> Choice {
        self.to_bytes().ct_eq(&other.to_bytes())
    }
}

impl Add for FieldElement {
    type Output = FieldElement;

    fn add(self, rhs: Self) -> Self::Output {
        let mut out = [0u64; 5];
        hacl::fadd(&mut out, &self.0, &rhs.0);
        FieldElement(out)
    }
}

impl Sub for FieldElement {
    type Output = FieldElement;

    fn sub(self, rhs: Self) -> Self::Output {
        let mut out = [0u64; 5];
        hacl::fsub(&mut out, &self.0, &rhs.0);
        FieldElement(out)
    }
}

impl Mul<u64> for FieldElement {
    type Output = FieldElement;

    fn mul(self, rhs: u64) -> Self::Output {
        let mut out = [0u64; 5];
        hacl::fmul1(&mut out, &self.0, rhs);
        FieldElement(out)
    }
}

impl Mul for FieldElement {
    type Output = FieldElement;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut out = [0u64; 5];
        let tmp: [uint128::uint128; 10] = [uint128::uint64_to_uint128(0u64); 10];
        hacl::fmul(&mut out, &self.0, &rhs.0, &tmp);
        FieldElement(out)
    }
}

impl FieldElement {
    pub const ONE: Self = Self([1, 0, 0, 0, 0]);

    /// Load a field element from the low 255 bits of a 32-byte input.
    ///
    /// This is intentionally non-canonical: it masks the top bit and does not
    /// reject inputs >= p.
    ///
    /// Adapted from the `curve25519-dalek` crate.
    pub const fn from_bytes(bytes: &[u8; 32]) -> Self {
        const fn load8_at(input: &[u8; 32], i: usize) -> u64 {
            (input[i] as u64)
                | ((input[i + 1] as u64) << 8)
                | ((input[i + 2] as u64) << 16)
                | ((input[i + 3] as u64) << 24)
                | ((input[i + 4] as u64) << 32)
                | ((input[i + 5] as u64) << 40)
                | ((input[i + 6] as u64) << 48)
                | ((input[i + 7] as u64) << 56)
        }

        let low_51_bit_mask = (1u64 << 51) - 1;
        Self([
            load8_at(bytes, 0) & low_51_bit_mask,
            (load8_at(bytes, 6) >> 3) & low_51_bit_mask,
            (load8_at(bytes, 12) >> 6) & low_51_bit_mask,
            (load8_at(bytes, 19) >> 1) & low_51_bit_mask,
            (load8_at(bytes, 24) >> 12) & low_51_bit_mask,
        ])
    }

    /// Serialize this field element to canonical 32-byte encoding.
    ///
    /// Adapted from the `curve25519-dalek` crate.
    #[rustfmt::skip]
    pub fn to_bytes(self) -> [u8; 32] {
        let low_51_bit_mask = (1u64 << 51) - 1;
        let mut limbs = self.0;

        // Reduce limbs to keep h < 2p before canonicalization.
        limbs[1] += limbs[0] >> 51;
        limbs[0] &= low_51_bit_mask;
        limbs[2] += limbs[1] >> 51;
        limbs[1] &= low_51_bit_mask;
        limbs[3] += limbs[2] >> 51;
        limbs[2] &= low_51_bit_mask;
        limbs[4] += limbs[3] >> 51;
        limbs[3] &= low_51_bit_mask;
        limbs[0] += (limbs[4] >> 51) * 19;
        limbs[4] &= low_51_bit_mask;
        limbs[1] += limbs[0] >> 51;
        limbs[0] &= low_51_bit_mask;

        let mut q = (limbs[0] + 19) >> 51;
        q = (limbs[1] + q) >> 51;
        q = (limbs[2] + q) >> 51;
        q = (limbs[3] + q) >> 51;
        q = (limbs[4] + q) >> 51;

        limbs[0] += 19 * q;

        limbs[1] += limbs[0] >> 51;
        limbs[0] &= low_51_bit_mask;
        limbs[2] += limbs[1] >> 51;
        limbs[1] &= low_51_bit_mask;
        limbs[3] += limbs[2] >> 51;
        limbs[2] &= low_51_bit_mask;
        limbs[4] += limbs[3] >> 51;
        limbs[3] &= low_51_bit_mask;
        limbs[4] &= low_51_bit_mask;

        let mut s = [0u8; 32];
        s[ 0] =   limbs[0]                           as u8;
        s[ 1] =  (limbs[0] >>  8)                    as u8;
        s[ 2] =  (limbs[0] >> 16)                    as u8;
        s[ 3] =  (limbs[0] >> 24)                    as u8;
        s[ 4] =  (limbs[0] >> 32)                    as u8;
        s[ 5] =  (limbs[0] >> 40)                    as u8;
        s[ 6] = ((limbs[0] >> 48) | (limbs[1] << 3)) as u8;
        s[ 7] =  (limbs[1] >>  5)                    as u8;
        s[ 8] =  (limbs[1] >> 13)                    as u8;
        s[ 9] =  (limbs[1] >> 21)                    as u8;
        s[10] =  (limbs[1] >> 29)                    as u8;
        s[11] =  (limbs[1] >> 37)                    as u8;
        s[12] = ((limbs[1] >> 45) | (limbs[2] << 6)) as u8;
        s[13] =  (limbs[2] >>  2)                    as u8;
        s[14] =  (limbs[2] >> 10)                    as u8;
        s[15] =  (limbs[2] >> 18)                    as u8;
        s[16] =  (limbs[2] >> 26)                    as u8;
        s[17] =  (limbs[2] >> 34)                    as u8;
        s[18] =  (limbs[2] >> 42)                    as u8;
        s[19] = ((limbs[2] >> 50) | (limbs[3] << 1)) as u8;
        s[20] =  (limbs[3] >>  7)                    as u8;
        s[21] =  (limbs[3] >> 15)                    as u8;
        s[22] =  (limbs[3] >> 23)                    as u8;
        s[23] =  (limbs[3] >> 31)                    as u8;
        s[24] =  (limbs[3] >> 39)                    as u8;
        s[25] = ((limbs[3] >> 47) | (limbs[4] << 4)) as u8;
        s[26] =  (limbs[4] >>  4)                    as u8;
        s[27] =  (limbs[4] >> 12)                    as u8;
        s[28] =  (limbs[4] >> 20)                    as u8;
        s[29] =  (limbs[4] >> 28)                    as u8;
        s[30] =  (limbs[4] >> 36)                    as u8;
        s[31] =  (limbs[4] >> 44)                    as u8;

        debug_assert!((s[31] & 0b1000_0000u8) == 0u8);
        s
    }

    #[inline]
    pub fn square(self) -> Self {
        let mut out: [u64; 5] = [0u64; 5];
        // This third tmp argument seems to be an unused
        // argument in the upstream verified crate for this function.
        let tmp: [uint128::uint128; 10] = [uint128::uint64_to_uint128(0u64); 10];
        hacl::fsqr(&mut out, &self.0, &tmp);
        FieldElement(out)
    }

    #[inline]
    pub fn is_negative(&self) -> Choice {
        let bytes = self.to_bytes();
        (bytes[0] & 1).into()
    }

    #[inline]
    pub fn is_zero(&self) -> Choice {
        let zero = [0u8; 32];
        let bytes = self.to_bytes();
        bytes.ct_eq(&zero)
    }

    #[inline]
    pub fn conditional_negate(&mut self, choice: Choice) {
        let neg = FieldElement::identity() - *self;
        let mask = (0u64).wrapping_sub(choice.unwrap_u8() as u64);
        for i in 0..5 {
            self.0[i] ^= mask & (self.0[i] ^ neg.0[i]);
        }
    }

    #[inline]
    pub fn conditional_assign(&mut self, other: &FieldElement, choice: Choice) {
        let mask = (0u64).wrapping_sub(choice.unwrap_u8() as u64);
        for i in 0..5 {
            self.0[i] ^= mask & (self.0[i] ^ other.0[i]);
        }
    }

    /// Attempt to compute `sqrt(1/self)` in constant time.
    ///
    /// Convenience wrapper around `sqrt_ratio_i`.
    ///
    /// This function always returns the nonnegative square root.
    ///
    /// # Return
    ///
    /// - `(Choice(1), +sqrt(1/self))  ` if `self` is a nonzero square;
    /// - `(Choice(0), zero)           ` if `self` is zero;
    /// - `(Choice(0), +sqrt(i/self))  ` if `self` is a nonzero nonsquare;
    ///
    pub(crate) fn invsqrt(&self) -> (Choice, FieldElement) {
        FieldElement::sqrt_ratio_i(&FieldElement::ONE, self)
    }

    /// Given `FieldElements` `u` and `v`, compute either `sqrt(u/v)`
    /// or `sqrt(i*u/v)` in constant time.
    ///
    /// This function always returns the nonnegative square root.
    ///
    /// # Return
    ///
    /// - `(Choice(1), +sqrt(u/v))  ` if `v` is nonzero and `u/v` is square;
    /// - `(Choice(1), zero)        ` if `u` is zero;
    /// - `(Choice(0), zero)        ` if `v` is zero and `u` is nonzero;
    /// - `(Choice(0), +sqrt(i*u/v))` if `u/v` is nonsquare (so `i*u/v` is square).
    ///
    pub(crate) fn sqrt_ratio_i(u: &FieldElement, v: &FieldElement) -> (Choice, FieldElement) {
        // Using the same trick as in ed25519 decoding, we merge the
        // inversion, the square root, and the square test as follows.
        //
        // To compute sqrt(α), we can compute β = α^((p+3)/8).
        // Then β^2 = ±α, so multiplying β by sqrt(-1) if necessary
        // gives sqrt(α).
        //
        // To compute 1/sqrt(α), we observe that
        //    1/β = α^(p-1 - (p+3)/8) = α^((7p-11)/8)
        //                            = α^3 * (α^7)^((p-5)/8).
        //
        // We can therefore compute sqrt(u/v) = sqrt(u)/sqrt(v)
        // by first computing
        //    r = u^((p+3)/8) v^(p-1-(p+3)/8)
        //      = u u^((p-5)/8) v^3 (v^7)^((p-5)/8)
        //      = (uv^3) (uv^7)^((p-5)/8).
        //
        // If v is nonzero and u/v is square, then r^2 = ±u/v,
        //                                     so vr^2 = ±u.
        // If vr^2 =  u, then sqrt(u/v) = r.
        // If vr^2 = -u, then sqrt(u/v) = r*sqrt(-1).
        //
        // If v is zero, r is also zero.

        let v3 = &v.square() * v;
        let v7 = &v3.square() * v;
        let mut r = &(u * &v3) * &(u * &v7).pow_p58();
        let check = v * &r.square();

        let i = &constants::SQRT_M1;

        let correct_sign_sqrt = check.ct_eq(u);
        let flipped_sign_sqrt = check.ct_eq(&(-u));
        let flipped_sign_sqrt_i = check.ct_eq(&(&(-u) * i));

        let r_prime = &constants::SQRT_M1 * &r;
        r.conditional_assign(&r_prime, flipped_sign_sqrt | flipped_sign_sqrt_i);

        // Choose the nonnegative square root.
        let r_is_negative = r.is_negative();
        r.conditional_negate(r_is_negative);

        let was_nonzero_square = correct_sign_sqrt | flipped_sign_sqrt;

        (was_nonzero_square, r)
    }

    /// Raise this field element to the power (p-5)/8 = 2^252 - 3.
    pub(crate) fn pow_p58(&self) -> FieldElement {
        let mut acc = FieldElement::ONE;

        // Bits of 2^252 - 3 are 1 for positions 251..=2 and 0.
        for i in (0..252).rev() {
            acc = acc.square();
            if i != 1 {
                acc = &acc * self;
            }
        }

        acc
    }
}

impl Add<&FieldElement> for &FieldElement {
    type Output = FieldElement;

    fn add(self, rhs: &FieldElement) -> Self::Output {
        (*self) + (*rhs)
    }
}

impl Sub<&FieldElement> for &FieldElement {
    type Output = FieldElement;

    fn sub(self, rhs: &FieldElement) -> Self::Output {
        (*self) - (*rhs)
    }
}

impl Mul<&FieldElement> for &FieldElement {
    type Output = FieldElement;

    fn mul(self, rhs: &FieldElement) -> Self::Output {
        (*self) * (*rhs)
    }
}

impl Neg for FieldElement {
    type Output = FieldElement;

    fn neg(self) -> Self::Output {
        FieldElement::identity() - self
    }
}

impl Neg for &FieldElement {
    type Output = FieldElement;

    fn neg(self) -> Self::Output {
        -*self
    }
}
