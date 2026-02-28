use curve25519_dalek::traits::Identity;
use std::ops::{Add, Sub};

// To get access to the field element functions (represented upstream in the verified
// core as 5 u64 limbs), we need to use the hacl-rs crate directly.
pub use libcrux_hacl_rs::bignum25519_51 as hacl;

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
