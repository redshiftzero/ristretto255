module Ristretto255.Constants
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Edwards `d` value, equal to `-121665/121666 mod p`.
let v_EDWARDS_D: Ristretto255.Field.t_FieldElement =
  Ristretto255.Field.FieldElement
  (let list =
      [
        mk_u64 929955233495203;
        mk_u64 466365720129213;
        mk_u64 1662059464998953;
        mk_u64 2033849074728123;
        mk_u64 1442794654840575
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  Ristretto255.Field.t_FieldElement

/// Precomputed value of one of the square roots of -1 (mod p).
let v_SQRT_M1: Ristretto255.Field.t_FieldElement =
  Ristretto255.Field.FieldElement
  (let list =
      [
        mk_u64 1718705420411056;
        mk_u64 234908883556509;
        mk_u64 2233514472574048;
        mk_u64 2117202627021982;
        mk_u64 765476049583133
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  Ristretto255.Field.t_FieldElement
