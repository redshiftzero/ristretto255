/// This module contains the constants for the Ristretto255 group, taken
/// from `curve25519-dalek` crate, but using the `FieldElement` type from this crate,
/// which internally uses verified Rust code, generated from the HACL* project.
#[cfg(test)]
use crate::backend::EdwardsPoint;
use crate::{CompressedRistretto, FieldElement};

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

/// One minus edwards `d` value squared, equal to `(1 - (-121665/121666) mod p) pow 2`
pub(crate) const ONE_MINUS_EDWARDS_D_SQUARED: FieldElement = FieldElement([
    1136626929484150,
    1998550399581263,
    496427632559748,
    118527312129759,
    45110755273534,
]);

/// Edwards `d` value minus one squared, equal to `(((-121665/121666) mod p) - 1) pow 2`
pub(crate) const EDWARDS_D_MINUS_ONE_SQUARED: FieldElement = FieldElement([
    1507062230895904,
    1572317787530805,
    683053064812840,
    317374165784489,
    1572899562415810,
]);

/// `= sqrt(a*d - 1)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.
pub(crate) const SQRT_AD_MINUS_ONE: FieldElement = FieldElement([
    2241493124984347,
    425987919032274,
    2207028919301688,
    1220490630685848,
    974799131293748,
]);

/// The value of minus one, equal to `-&FieldElement::ONE`
pub(crate) const MINUS_ONE: FieldElement = FieldElement([
    2251799813685228,
    2251799813685247,
    2251799813685247,
    2251799813685247,
    2251799813685247,
]);

/// Edwards `2*d` value, equal to `2*(-121665/121666) mod p`.
pub(crate) const EDWARDS_D2: FieldElement = FieldElement([
    1859910466990425,
    932731440258426,
    1072319116312658,
    1815898335770999,
    633789495995903,
]);

/// The compressed Ristretto255 basepoint (i.e. 1 * generator).
pub const RISTRETTO_BASEPOINT_COMPRESSED: CompressedRistretto = CompressedRistretto([
    226, 242, 174, 10, 106, 188, 78, 113, 168, 132, 169, 97, 197, 0, 81, 95, 88, 227, 11, 106, 165,
    130, 221, 141, 182, 166, 89, 69, 224, 141, 45, 118,
]);

/// The 8-torsion subgroup \\(\mathcal E \[8\]\\).
///
/// In the case of Curve25519, it is cyclic; the \\(i\\)-th element of
/// the array is \\(\[i\]P\\), where \\(P\\) is a point of order \\(8\\)
/// generating \\(\mathcal E\[8\]\\).
///
/// Thus \\(\mathcal E\[4\]\\) is the points indexed by `0,2,4,6`, and
/// \\(\mathcal E\[2\]\\) is the points indexed by `0,4`.
#[cfg(test)]
pub const EIGHT_TORSION: [EdwardsPoint; 8] = EIGHT_TORSION_INNER_DOC_HIDDEN;

/// Inner item used to hide limb constants from cargo doc output.
#[cfg(test)]
#[doc(hidden)]
pub const EIGHT_TORSION_INNER_DOC_HIDDEN: [EdwardsPoint; 8] = [
    EdwardsPoint {
        X: FieldElement([0, 0, 0, 0, 0]),
        Y: FieldElement([1, 0, 0, 0, 0]),
        Z: FieldElement([1, 0, 0, 0, 0]),
        T: FieldElement([0, 0, 0, 0, 0]),
    },
    EdwardsPoint {
        X: FieldElement([
            358744748052810,
            1691584618240980,
            977650209285361,
            1429865912637724,
            560044844278676,
        ]),
        Y: FieldElement([
            84926274344903,
            473620666599931,
            365590438845504,
            1028470286882429,
            2146499180330972,
        ]),
        Z: FieldElement([1, 0, 0, 0, 0]),
        T: FieldElement([
            1448326834587521,
            1857896831960481,
            1093722731865333,
            1677408490711241,
            1915505153018406,
        ]),
    },
    EdwardsPoint {
        X: FieldElement([
            533094393274173,
            2016890930128738,
            18285341111199,
            134597186663265,
            1486323764102114,
        ]),
        Y: FieldElement([0, 0, 0, 0, 0]),
        Z: FieldElement([1, 0, 0, 0, 0]),
        T: FieldElement([0, 0, 0, 0, 0]),
    },
    EdwardsPoint {
        X: FieldElement([
            358744748052810,
            1691584618240980,
            977650209285361,
            1429865912637724,
            560044844278676,
        ]),
        Y: FieldElement([
            2166873539340326,
            1778179147085316,
            1886209374839743,
            1223329526802818,
            105300633354275,
        ]),
        Z: FieldElement([1, 0, 0, 0, 0]),
        T: FieldElement([
            803472979097708,
            393902981724766,
            1158077081819914,
            574391322974006,
            336294660666841,
        ]),
    },
    EdwardsPoint {
        X: FieldElement([0, 0, 0, 0, 0]),
        Y: FieldElement([
            2251799813685228,
            2251799813685247,
            2251799813685247,
            2251799813685247,
            2251799813685247,
        ]),
        Z: FieldElement([1, 0, 0, 0, 0]),
        T: FieldElement([0, 0, 0, 0, 0]),
    },
    EdwardsPoint {
        X: FieldElement([
            1893055065632419,
            560215195444267,
            1274149604399886,
            821933901047523,
            1691754969406571,
        ]),
        Y: FieldElement([
            2166873539340326,
            1778179147085316,
            1886209374839743,
            1223329526802818,
            105300633354275,
        ]),
        Z: FieldElement([1, 0, 0, 0, 0]),
        T: FieldElement([
            1448326834587521,
            1857896831960481,
            1093722731865333,
            1677408490711241,
            1915505153018406,
        ]),
    },
    EdwardsPoint {
        X: FieldElement([
            1718705420411056,
            234908883556509,
            2233514472574048,
            2117202627021982,
            765476049583133,
        ]),
        Y: FieldElement([0, 0, 0, 0, 0]),
        Z: FieldElement([1, 0, 0, 0, 0]),
        T: FieldElement([0, 0, 0, 0, 0]),
    },
    EdwardsPoint {
        X: FieldElement([
            1893055065632419,
            560215195444267,
            1274149604399886,
            821933901047523,
            1691754969406571,
        ]),
        Y: FieldElement([
            84926274344903,
            473620666599931,
            365590438845504,
            1028470286882429,
            2146499180330972,
        ]),
        Z: FieldElement([1, 0, 0, 0, 0]),
        T: FieldElement([
            803472979097708,
            393902981724766,
            1158077081819914,
            574391322974006,
            336294660666841,
        ]),
    },
];
