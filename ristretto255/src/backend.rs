use std::ops::Add;

use subtle::{Choice, ConstantTimeEq};

use crate::constants;
use crate::field::FieldElement;
use crate::traits::Identity;

/// An `EdwardsPoint` represents a point on the Edwards form of Curve25519
/// in extended coordinates \\((X:Y:Z:T)\\) with \\(x = X/Z\\), \\(y = Y/Z\\),
/// \\(xy = T/Z\\).
#[derive(Copy, Clone)]
pub(crate) struct EdwardsPoint {
    pub(crate) X: FieldElement,
    pub(crate) Y: FieldElement,
    pub(crate) Z: FieldElement,
    pub(crate) T: FieldElement,
}

impl Identity for EdwardsPoint {
    fn identity() -> EdwardsPoint {
        EdwardsPoint {
            X: FieldElement::ZERO,
            Y: FieldElement::ONE,
            Z: FieldElement::ONE,
            T: FieldElement::ZERO,
        }
    }
}

impl ConstantTimeEq for EdwardsPoint {
    fn ct_eq(&self, other: &EdwardsPoint) -> Choice {
        // We would like to check that the point (X/Z, Y/Z) is equal to
        // the point (X'/Z', Y'/Z') without converting into affine
        // coordinates (x, y) and (x', y'), which requires two inversions.
        // We have that X = xZ and X' = x'Z'. Thus, x = x' is equivalent to
        // (xZ)Z' = (x'Z')Z, and similarly for the y-coordinate.

        (&self.X * &other.Z).ct_eq(&(&other.X * &self.Z))
            & (&self.Y * &other.Z).ct_eq(&(&other.Y * &self.Z))
    }
}

impl PartialEq for EdwardsPoint {
    fn eq(&self, other: &EdwardsPoint) -> bool {
        self.ct_eq(other).into()
    }
}

impl Eq for EdwardsPoint {}

impl EdwardsPoint {
    /// Convert to a ProjectiveNielsPoint
    pub(crate) fn as_projective_niels(&self) -> ProjectiveNielsPoint {
        ProjectiveNielsPoint {
            Y_plus_X: &self.Y + &self.X,
            Y_minus_X: &self.Y - &self.X,
            Z: self.Z,
            T2d: &self.T * &constants::EDWARDS_D2,
        }
    }

    /// Convert this point from the \\( \mathbb P\^1 \times \mathbb P\^1
    /// \\) model to the \\( \mathbb P\^3 \\) model.
    ///
    /// This costs \\(4 \mathrm M \\).
    pub fn as_extended(&self) -> EdwardsPoint {
        EdwardsPoint {
            X: &self.X * &self.T,
            Y: &self.Y * &self.Z,
            Z: &self.Z * &self.T,
            T: &self.X * &self.Y,
        }
    }
}

/// A `CompletedPoint` is a point \\(((X:Z), (Y:T))\\) on the
/// \\(\mathbb P^1 \times \mathbb P^1\\) model of the curve.
/// A point (x,y) in the affine model corresponds to \\(((x:1),(y:1))\\).
#[derive(Copy, Clone)]
pub(crate) struct CompletedPoint {
    pub(crate) X: FieldElement,
    pub(crate) Y: FieldElement,
    pub(crate) Z: FieldElement,
    pub(crate) T: FieldElement,
}

impl CompletedPoint {
    /// Convert from the \\(\mathbb P^1 \times \mathbb P^1\\) model to
    /// the \\(\mathbb P^3\\) (extended) model.
    ///
    /// Cost: \\(4 \mathrm M\\).
    pub(crate) fn as_extended(&self) -> EdwardsPoint {
        EdwardsPoint {
            X: &self.X * &self.T,
            Y: &self.Y * &self.Z,
            Z: &self.Z * &self.T,
            T: &self.X * &self.Y,
        }
    }
}

impl EdwardsPoint {
    /// Double this point. (for perf we should not go through the projective)
    pub(crate) fn double(&self) -> EdwardsPoint {
        (self + &self.as_projective_niels()).as_extended()
    }
}

/// A pre-computed point on the \\( \mathbb P\^3 \\) model for the
/// curve, represented as \\((Y+X, Y-X, Z, 2dXY)\\) in "Niels coordinates".
#[derive(Copy, Clone)]
#[allow(missing_docs)]
pub struct ProjectiveNielsPoint {
    pub Y_plus_X: FieldElement,
    pub Y_minus_X: FieldElement,
    pub Z: FieldElement,
    pub T2d: FieldElement,
}

impl<'a> Add<&'a ProjectiveNielsPoint> for &EdwardsPoint {
    type Output = CompletedPoint;

    fn add(self, other: &'a ProjectiveNielsPoint) -> CompletedPoint {
        let Y_plus_X = &self.Y + &self.X;
        let Y_minus_X = &self.Y - &self.X;
        let PP = &Y_plus_X * &other.Y_plus_X;
        let MM = &Y_minus_X * &other.Y_minus_X;
        let TT2d = &self.T * &other.T2d;
        let ZZ = &self.Z * &other.Z;
        let ZZ2 = &ZZ + &ZZ;

        CompletedPoint {
            X: &PP - &MM,
            Y: &PP + &MM,
            Z: &ZZ2 + &TT2d,
            T: &ZZ2 - &TT2d,
        }
    }
}
