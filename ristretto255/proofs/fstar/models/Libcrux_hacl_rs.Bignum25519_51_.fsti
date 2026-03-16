module Libcrux_hacl_rs.Bignum25519_51_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// Stub models for libcrux-hacl-rs bignum25519_51 field arithmetic.
/// These operations are verified in HACL* (Hacl.Bignum25519); here we
/// simply assume them for the purposes of ristretto255 verification.

val fadd
    (out: t_Array u64 (mk_usize 5))
    (f1: t_Slice u64)
    (f2: t_Slice u64)
    : t_Array u64 (mk_usize 5)

val fsub
    (out: t_Array u64 (mk_usize 5))
    (f1: t_Slice u64)
    (f2: t_Slice u64)
    : t_Array u64 (mk_usize 5)

val fmul1
    (out: t_Array u64 (mk_usize 5))
    (f1: t_Slice u64)
    (f2: u64)
    : t_Array u64 (mk_usize 5)

val fmul
    (out: t_Array u64 (mk_usize 5))
    (f1: t_Slice u64)
    (f2: t_Slice u64)
    (tmp: t_Slice u128)
    : t_Array u64 (mk_usize 5)

val fsqr
    (out: t_Array u64 (mk_usize 5))
    (f1: t_Slice u64)
    (tmp: t_Slice u128)
    : t_Array u64 (mk_usize 5)
