// The `Scalar52` backend and the Montgomery-form scalar constants below are
// ported from the `curve25519-dalek` crate (MIT/Apache-2.0).

use rand_core::{CryptoRng, RngCore};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
#[cfg(not(hax))]
use zeroize::Zeroize;

/// A scalar value for the ristretto255 group.
///
/// Scalars are integers mod ℓ, where ℓ is the order of the ristretto255 group.
#[cfg_attr(not(hax), derive(Zeroize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Scalar([u8; 32]);

impl Scalar {
    /// Generate a random scalar using the provided RNG.
    pub fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        let mut bytes = [0u8; 64];
        rng.fill_bytes(&mut bytes);
        Self::from_bytes_mod_order_wide(&bytes)
    }

    /// Attempt to construct a scalar from a canonical byte representation.
    ///
    /// Returns `None` if the bytes do not represent a canonical scalar
    /// (i.e. the value is >= ℓ).
    pub fn from_bytes_checked(bytes: &[u8; 32]) -> Option<Self> {
        let candidate = Scalar(*bytes);
        let high_bit_unset = (bytes[31] >> 7).ct_eq(&0);
        let is_canonical = candidate.is_canonical();
        if (high_bit_unset & is_canonical).into() {
            Some(candidate)
        } else {
            None
        }
    }

    /// Construct a scalar by reducing a 256-bit little-endian integer modulo ℓ.
    ///
    /// Unlike [`from_bytes_checked`](Self::from_bytes_checked), this always
    /// succeeds by reducing the input mod the group order.
    pub fn from_bytes_mod_order(bytes: &[u8; 32]) -> Self {
        Scalar(*bytes).reduce()
    }

    /// Construct a scalar by reducing a 512-bit little-endian integer modulo ℓ.
    pub fn from_bytes_mod_order_wide(bytes: &[u8; 64]) -> Self {
        Scalar(Scalar52::from_bytes_wide(bytes).to_bytes())
    }

    /// Serialize this scalar to a 32-byte little-endian array.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0
    }

    /// Reduce this scalar mod ℓ, returning the canonical representative.
    fn reduce(&self) -> Scalar {
        let x = Scalar52::from_bytes(&self.0);
        let xR = Scalar52::mul_internal(&x, &R);
        let x_mod_l = Scalar52::montgomery_reduce(&xR);
        Scalar(x_mod_l.to_bytes())
    }

    fn is_canonical(&self) -> Choice {
        self.0.ct_eq(&self.reduce().0)
    }
}

// ---- Scalar52 backend (52-bit limbs mod ℓ) ----

/// `Scalar52` represents an element of ℤ/ℓℤ as 5 × 52-bit limbs.
#[derive(Copy, Clone)]
struct Scalar52([u64; 5]);

/// u64 × u64 → u128 multiply helper.
#[inline(always)]
fn m(x: u64, y: u64) -> u128 {
    (x as u128) * (y as u128)
}

impl Scalar52 {
    const ZERO: Scalar52 = Scalar52([0, 0, 0, 0, 0]);

    #[rustfmt::skip]
    fn from_bytes(bytes: &[u8; 32]) -> Scalar52 {
        let mut words = [0u64; 4];
        for i in 0..4 {
            for j in 0..8 {
                words[i] |= (bytes[(i * 8) + j] as u64) << (j * 8);
            }
        }

        let mask = (1u64 << 52) - 1;
        let top_mask = (1u64 << 48) - 1;

        Scalar52([
              words[0]                            & mask,
            ((words[0] >> 52) | (words[1] << 12)) & mask,
            ((words[1] >> 40) | (words[2] << 24)) & mask,
            ((words[2] >> 28) | (words[3] << 36)) & mask,
             (words[3] >> 16)                     & top_mask,
        ])
    }

    #[rustfmt::skip]
    fn from_bytes_wide(bytes: &[u8; 64]) -> Scalar52 {
        let mut words = [0u64; 8];
        for i in 0..8 {
            for j in 0..8 {
                words[i] |= (bytes[(i * 8) + j] as u64) << (j * 8);
            }
        }

        let mask = (1u64 << 52) - 1;

        let lo = Scalar52([
              words[0]                             & mask,
            ((words[0] >> 52) | (words[1] << 12))  & mask,
            ((words[1] >> 40) | (words[2] << 24))  & mask,
            ((words[2] >> 28) | (words[3] << 36))  & mask,
            ((words[3] >> 16) | (words[4] << 48))  & mask,
        ]);
        let hi = Scalar52([
             (words[4] >>  4)                      & mask,
            ((words[4] >> 56) | (words[5] <<  8))  & mask,
            ((words[5] >> 44) | (words[6] << 20))  & mask,
            ((words[6] >> 32) | (words[7] << 32))  & mask,
              words[7] >> 20,
        ]);

        let lo = Scalar52::montgomery_mul(&lo, &R);  // (lo * R) / R = lo
        let hi = Scalar52::montgomery_mul(&hi, &RR); // (hi * R^2) / R = hi * R

        Scalar52::add(&hi, &lo)
    }

    #[rustfmt::skip]
    #[allow(clippy::identity_op)]
    fn to_bytes(self) -> [u8; 32] {
        let mut s = [0u8; 32];

        s[ 0] =  (self.0[0] >>  0)                      as u8;
        s[ 1] =  (self.0[0] >>  8)                      as u8;
        s[ 2] =  (self.0[0] >> 16)                      as u8;
        s[ 3] =  (self.0[0] >> 24)                      as u8;
        s[ 4] =  (self.0[0] >> 32)                      as u8;
        s[ 5] =  (self.0[0] >> 40)                      as u8;
        s[ 6] = ((self.0[0] >> 48) | (self.0[1] << 4))  as u8;
        s[ 7] =  (self.0[1] >>  4)                      as u8;
        s[ 8] =  (self.0[1] >> 12)                      as u8;
        s[ 9] =  (self.0[1] >> 20)                      as u8;
        s[10] =  (self.0[1] >> 28)                      as u8;
        s[11] =  (self.0[1] >> 36)                      as u8;
        s[12] =  (self.0[1] >> 44)                      as u8;
        s[13] =  (self.0[2] >>  0)                      as u8;
        s[14] =  (self.0[2] >>  8)                      as u8;
        s[15] =  (self.0[2] >> 16)                      as u8;
        s[16] =  (self.0[2] >> 24)                      as u8;
        s[17] =  (self.0[2] >> 32)                      as u8;
        s[18] =  (self.0[2] >> 40)                      as u8;
        s[19] = ((self.0[2] >> 48) | (self.0[3] << 4))  as u8;
        s[20] =  (self.0[3] >>  4)                      as u8;
        s[21] =  (self.0[3] >> 12)                      as u8;
        s[22] =  (self.0[3] >> 20)                      as u8;
        s[23] =  (self.0[3] >> 28)                      as u8;
        s[24] =  (self.0[3] >> 36)                      as u8;
        s[25] =  (self.0[3] >> 44)                      as u8;
        s[26] =  (self.0[4] >>  0)                      as u8;
        s[27] =  (self.0[4] >>  8)                      as u8;
        s[28] =  (self.0[4] >> 16)                      as u8;
        s[29] =  (self.0[4] >> 24)                      as u8;
        s[30] =  (self.0[4] >> 32)                      as u8;
        s[31] =  (self.0[4] >> 40)                      as u8;

        s
    }

    fn add(a: &Scalar52, b: &Scalar52) -> Scalar52 {
        let mut sum = Scalar52::ZERO;
        let mask = (1u64 << 52) - 1;

        let mut carry: u64 = 0;
        for i in 0..5 {
            carry = a.0[i] + b.0[i] + (carry >> 52);
            sum.0[i] = carry & mask;
        }

        // subtract ℓ if the sum is ≥ ℓ
        Scalar52::sub(&sum, &L)
    }

    fn sub(a: &Scalar52, b: &Scalar52) -> Scalar52 {
        let mut difference = Scalar52::ZERO;
        let mask = (1u64 << 52) - 1;

        let mut borrow: u64 = 0;
        for i in 0..5 {
            borrow = a.0[i].wrapping_sub(b.0[i] + (borrow >> 63));
            difference.0[i] = borrow & mask;
        }

        // conditionally add ℓ if the difference is negative
        let underflow = Choice::from((borrow >> 63) as u8);
        let mut carry: u64 = 0;
        for i in 0..5 {
            let addend = u64::conditional_select(&0, &L.0[i], underflow);
            carry = (carry >> 52) + difference.0[i] + addend;
            difference.0[i] = carry & mask;
        }
        difference
    }

    #[inline(always)]
    #[rustfmt::skip]
    fn mul_internal(a: &Scalar52, b: &Scalar52) -> [u128; 9] {
        let a = &a.0;
        let b = &b.0;
        [
            m(a[0], b[0]),
            m(a[0], b[1]) + m(a[1], b[0]),
            m(a[0], b[2]) + m(a[1], b[1]) + m(a[2], b[0]),
            m(a[0], b[3]) + m(a[1], b[2]) + m(a[2], b[1]) + m(a[3], b[0]),
            m(a[0], b[4]) + m(a[1], b[3]) + m(a[2], b[2]) + m(a[3], b[1]) + m(a[4], b[0]),
                            m(a[1], b[4]) + m(a[2], b[3]) + m(a[3], b[2]) + m(a[4], b[1]),
                                            m(a[2], b[4]) + m(a[3], b[3]) + m(a[4], b[2]),
                                                            m(a[3], b[4]) + m(a[4], b[3]),
                                                                            m(a[4], b[4]),
        ]
    }

    #[inline(always)]
    #[rustfmt::skip]
    fn montgomery_reduce(limbs: &[u128; 9]) -> Scalar52 {
        #[inline(always)]
        fn part1(sum: u128) -> (u128, u64) {
            let p = (sum as u64).wrapping_mul(LFACTOR) & ((1u64 << 52) - 1);
            ((sum + m(p, L.0[0])) >> 52, p)
        }

        #[inline(always)]
        fn part2(sum: u128) -> (u128, u64) {
            let w = (sum as u64) & ((1u64 << 52) - 1);
            (sum >> 52, w)
        }

        // note: L.0[3] is zero, so its multiples can be skipped
        let l = &L.0;

        let (carry, n0) = part1(        limbs[0]);
        let (carry, n1) = part1(carry + limbs[1] + m(n0, l[1]));
        let (carry, n2) = part1(carry + limbs[2] + m(n0, l[2]) + m(n1, l[1]));
        let (carry, n3) = part1(carry + limbs[3]               + m(n1, l[2]) + m(n2, l[1]));
        let (carry, n4) = part1(carry + limbs[4] + m(n0, l[4])               + m(n2, l[2]) + m(n3, l[1]));

        let (carry, r0) = part2(carry + limbs[5]               + m(n1, l[4])               + m(n3, l[2])   + m(n4, l[1]));
        let (carry, r1) = part2(carry + limbs[6]                             + m(n2, l[4])                 + m(n4, l[2]));
        let (carry, r2) = part2(carry + limbs[7]                                           + m(n3, l[4])                );
        let (carry, r3) = part2(carry + limbs[8]                                                           + m(n4, l[4]));
        let         r4 = carry as u64;

        Scalar52::sub(&Scalar52([r0, r1, r2, r3, r4]), &L)
    }

    fn montgomery_mul(a: &Scalar52, b: &Scalar52) -> Scalar52 {
        Scalar52::montgomery_reduce(&Scalar52::mul_internal(a, b))
    }
}

// ---- Scalar52 constants: group order ℓ in Montgomery form ----

/// `L` is the group order ℓ = 2^252 + 27742317777372353535851937790883648493.
const L: Scalar52 = Scalar52([
    0x0002631a5cf5d3ed,
    0x000dea2f79cd6581,
    0x000000000014def9,
    0x0000000000000000,
    0x0000100000000000,
]);

/// `L * LFACTOR ≡ -1  (mod 2^52)`.
const LFACTOR: u64 = 0x51da312547e1b;

/// `R = 2^260 mod ℓ`, the Montgomery modulus.
const R: Scalar52 = Scalar52([
    0x000f48bd6721e6ed,
    0x0003bab5ac67e45a,
    0x000fffffeb35e51b,
    0x000fffffffffffff,
    0x00000fffffffffff,
]);

/// `RR = R^2 mod ℓ`.
const RR: Scalar52 = Scalar52([
    0x0009d265e952d13b,
    0x000d63c715bea69f,
    0x0005be65cb687604,
    0x0003dceec73d217f,
    0x000009411b7c309a,
]);
