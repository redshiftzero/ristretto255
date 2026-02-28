use curve25519_dalek::traits::Identity;
use std::ops::{Add, Mul, Sub};

// To get access to the field element functions (represented upstream in the verified
// core as 5 u64 limbs), we need to use the hacl-rs crate directly.
pub use libcrux_hacl_rs::bignum25519_51 as hacl;
use libcrux_hacl_rs::fstar::uint128;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldElement(pub [u64; 5]);

impl Identity for FieldElement {
    fn identity() -> Self {
        Self([0; 5])
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

impl FieldElement {
    pub const ONE: Self = Self([1, 0, 0, 0, 0]);

    #[inline]
    pub fn square(self) -> Self {
        let mut out: [u64; 5] = [0u64; 5];
        // This third tmp argument seems to be an unused
        // argument in the upstream verified crate for this function.
        let tmp: [uint128::uint128; 10] = [uint128::uint64_to_uint128(0u64); 10];
        hacl::fsqr(&mut out, &self.0, &tmp);
        FieldElement(out)
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
