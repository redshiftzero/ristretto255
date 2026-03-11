/// This module contains the constants for the Ristretto255 group, taken
/// from `curve25519-dalek` crate, but using the `FieldElement` type from this crate,
/// which internally uses verified Rust code, generated from the HACL* project.
use crate::FieldElement;

/// Edwards `d` value, equal to `-121665/121666 mod p`.
pub(crate) const EDWARDS_D: FieldElement = FieldElement([
    929955233495203,
    466365720129213,
    1662059464998953,
    2033849074728123,
    1442794654840575,
]);

/// Precomputed value of one of the square roots of -1 (mod p).
pub(crate) const SQRT_M1: FieldElement = FieldElement([
    1718705420411056,
    234908883556509,
    2233514472574048,
    2117202627021982,
    765476049583133,
]);

/// `= 1/sqrt(a-d)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.
pub(crate) const INVSQRT_A_MINUS_D: FieldElement = FieldElement([
    278908739862762,
    821645201101625,
    8113234426968,
    1777959178193151,
    2118520810568447,
]);
