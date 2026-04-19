module Ristretto255.Bundle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Ristretto255.Traits in
  let open Subtle in
  ()

/// A compressed Ristretto255 point.
/// This represents the canonical encoding of a Ristretto255 group element.
type t_CompressedRistretto =
  | CompressedRistretto : t_Array u8 (mk_usize 32) -> t_CompressedRistretto

let impl_13: Core_models.Clone.t_Clone t_CompressedRistretto =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_12': Core_models.Marker.t_Copy t_CompressedRistretto

unfold
let impl_12 = impl_12'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_14': Core_models.Fmt.t_Debug t_CompressedRistretto

unfold
let impl_14 = impl_14'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_16': Core_models.Hash.t_Hash t_CompressedRistretto

unfold
let impl_16 = impl_16'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core_models.Cmp.t_PartialEq t_CompressedRistretto t_CompressedRistretto =
  {
    f_eq_pre = (fun (self: t_CompressedRistretto) (other: t_CompressedRistretto) -> true);
    f_eq_post
    =
    (fun (self: t_CompressedRistretto) (other: t_CompressedRistretto) (out: bool) -> true);
    f_eq
    =
    fun (self: t_CompressedRistretto) (other: t_CompressedRistretto) ->
      Core_models.Convert.f_into #Subtle.t_Choice
        #bool
        #FStar.Tactics.Typeclasses.solve
        (Subtle.f_ct_eq #(t_Slice u8)
            #FStar.Tactics.Typeclasses.solve
            (self._0 <: t_Slice u8)
            (other._0 <: t_Slice u8)
          <:
          Subtle.t_Choice)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_15': Core_models.Cmp.t_Eq t_CompressedRistretto

unfold
let impl_15 = impl_15'

/// Copy the bytes of this `CompressedRistretto`.
let impl_19__to_bytes (self: t_CompressedRistretto) : t_Array u8 (mk_usize 32) = self._0

/// View this `CompressedRistretto` as an array of bytes.
let impl_19__as_bytes (self: t_CompressedRistretto) : t_Array u8 (mk_usize 32) = self._0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Subtle.t_ConstantTimeEq t_CompressedRistretto =
  {
    f_ct_eq_pre = (fun (self: t_CompressedRistretto) (other: t_CompressedRistretto) -> true);
    f_ct_eq_post
    =
    (fun (self: t_CompressedRistretto) (other: t_CompressedRistretto) (out: Subtle.t_Choice) -> true
    );
    f_ct_eq
    =
    fun (self: t_CompressedRistretto) (other: t_CompressedRistretto) ->
      Subtle.f_ct_eq #(t_Slice u8)
        #FStar.Tactics.Typeclasses.solve
        (impl_19__as_bytes self <: t_Slice u8)
        (impl_19__as_bytes other <: t_Slice u8)
  }

/// Construct a `CompressedRistretto` from a slice of bytes.
/// # Errors
/// Returns [`TryFromSliceError`] if the input `bytes` slice does not have
/// a length of 32.
let impl_19__from_slice (bytes: t_Slice u8)
    : Prims.Pure
      (Core_models.Result.t_Result t_CompressedRistretto Core_models.Array.t_TryFromSliceError)
      (requires True)
      (fun _ -> Prims.l_True) =
  Core_models.Result.impl__map #(t_Array u8 (mk_usize 32))
    #Core_models.Array.t_TryFromSliceError
    #t_CompressedRistretto
    (Core_models.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 (mk_usize 32))
        #FStar.Tactics.Typeclasses.solve
        bytes
      <:
      Core_models.Result.t_Result (t_Array u8 (mk_usize 32)) Core_models.Array.t_TryFromSliceError)
    CompressedRistretto

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Ristretto255.Traits.t_Identity t_CompressedRistretto =
  {
    f_identity_pre = (fun (_: Prims.unit) -> true);
    f_identity_post = (fun (_: Prims.unit) (out: t_CompressedRistretto) -> true);
    f_identity
    =
    fun (_: Prims.unit) ->
      CompressedRistretto (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32))
      <:
      t_CompressedRistretto
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core_models.Default.t_Default t_CompressedRistretto =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_CompressedRistretto) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      Ristretto255.Traits.f_identity #t_CompressedRistretto #FStar.Tactics.Typeclasses.solve ()
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: Core_models.Convert.t_TryFrom t_CompressedRistretto (t_Slice u8) =
  {
    f_Error = Core_models.Array.t_TryFromSliceError;
    f_try_from_pre = (fun (slice: t_Slice u8) -> true);
    f_try_from_post
    =
    (fun
        (slice: t_Slice u8)
        (out:
          Core_models.Result.t_Result t_CompressedRistretto Core_models.Array.t_TryFromSliceError)
        ->
        true);
    f_try_from = fun (slice: t_Slice u8) -> impl_19__from_slice slice
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core_models.Convert.t_From (t_Array u8 (mk_usize 32)) t_CompressedRistretto =
  {
    f_from_pre = (fun (c: t_CompressedRistretto) -> true);
    f_from_post = (fun (c: t_CompressedRistretto) (out: t_Array u8 (mk_usize 32)) -> true);
    f_from = fun (c: t_CompressedRistretto) -> c._0
  }

/// The compressed Ristretto255 basepoint (i.e. 1 * generator).
let v_RISTRETTO_BASEPOINT_COMPRESSED: t_CompressedRistretto =
  CompressedRistretto
  (let list =
      [
        mk_u8 226; mk_u8 242; mk_u8 174; mk_u8 10; mk_u8 106; mk_u8 188; mk_u8 78; mk_u8 113;
        mk_u8 168; mk_u8 132; mk_u8 169; mk_u8 97; mk_u8 197; mk_u8 0; mk_u8 81; mk_u8 95; mk_u8 88;
        mk_u8 227; mk_u8 11; mk_u8 106; mk_u8 165; mk_u8 130; mk_u8 221; mk_u8 141; mk_u8 182;
        mk_u8 166; mk_u8 89; mk_u8 69; mk_u8 224; mk_u8 141; mk_u8 45; mk_u8 118
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
    Rust_primitives.Hax.array_of_list 32 list)
  <:
  t_CompressedRistretto

type t_FieldElement = | FieldElement : t_Array u64 (mk_usize 5) -> t_FieldElement

/// An `EdwardsPoint` represents a point on the Edwards form of Curve25519
/// in extended coordinates \\((X:Y:Z:T)\\) with \\(x = X/Z\\), \\(y = Y/Z\\),
/// \\(xy = T/Z\\).
type t_EdwardsPoint = {
  f_X:t_FieldElement;
  f_Y:t_FieldElement;
  f_Z:t_FieldElement;
  f_T:t_FieldElement
}

/// A `RistrettoPoint` is an element in the Ristretto255 group.
type t_RistrettoPoint = | RistrettoPoint : t_EdwardsPoint -> t_RistrettoPoint

let impl_22: Core_models.Clone.t_Clone t_RistrettoPoint =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_21': Core_models.Marker.t_Copy t_RistrettoPoint

unfold
let impl_21 = impl_21'

/// Return the Ristretto255 basepoint.
assume
val impl_5__basepoint': Prims.unit -> t_RistrettoPoint

unfold
let impl_5__basepoint = impl_5__basepoint'

let impl_8__from__backend: Core_models.Clone.t_Clone t_EdwardsPoint =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7__from__backend': Core_models.Marker.t_Copy t_EdwardsPoint

unfold
let impl_7__from__backend = impl_7__from__backend'

/// A `CompletedPoint` is a point \\(((X:Z), (Y:T))\\) on the
/// \\(\mathbb P^1 \times \mathbb P^1\\) model of the curve.
/// A point (x,y) in the affine model corresponds to \\(((x:1),(y:1))\\).
type t_CompletedPoint = {
  f_X:t_FieldElement;
  f_Y:t_FieldElement;
  f_Z:t_FieldElement;
  f_T:t_FieldElement
}

let impl_10__from__backend: Core_models.Clone.t_Clone t_CompletedPoint =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9__from__backend': Core_models.Marker.t_Copy t_CompletedPoint

unfold
let impl_9__from__backend = impl_9__from__backend'

/// A pre-computed point on the \\( \mathbb P\^3 \\) model for the
/// curve, represented as \\((Y+X, Y-X, Z, 2dXY)\\) in "Niels coordinates".
type t_ProjectiveNielsPoint = {
  f_Y_plus_X:t_FieldElement;
  f_Y_minus_X:t_FieldElement;
  f_Z:t_FieldElement;
  f_T2d:t_FieldElement
}

let impl_12__from__backend: Core_models.Clone.t_Clone t_ProjectiveNielsPoint =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_11__from__backend': Core_models.Marker.t_Copy t_ProjectiveNielsPoint

unfold
let impl_11__from__backend = impl_11__from__backend'

/// Edwards `d` value, equal to `-121665/121666 mod p`.
let v_EDWARDS_D: t_FieldElement =
  FieldElement
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
  t_FieldElement

/// Precomputed value of one of the square roots of -1 (mod p).
let v_SQRT_M1: t_FieldElement =
  FieldElement
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
  t_FieldElement

/// `= 1/sqrt(a-d)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.
let v_INVSQRT_A_MINUS_D: t_FieldElement =
  FieldElement
  (let list =
      [
        mk_u64 278908739862762;
        mk_u64 821645201101625;
        mk_u64 8113234426968;
        mk_u64 1777959178193151;
        mk_u64 2118520810568447
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_FieldElement

/// One minus edwards `d` value squared, equal to `(1 - (-121665/121666) mod p) pow 2`
let v_ONE_MINUS_EDWARDS_D_SQUARED: t_FieldElement =
  FieldElement
  (let list =
      [
        mk_u64 1136626929484150;
        mk_u64 1998550399581263;
        mk_u64 496427632559748;
        mk_u64 118527312129759;
        mk_u64 45110755273534
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_FieldElement

/// Edwards `d` value minus one squared, equal to `(((-121665/121666) mod p) - 1) pow 2`
let v_EDWARDS_D_MINUS_ONE_SQUARED: t_FieldElement =
  FieldElement
  (let list =
      [
        mk_u64 1507062230895904;
        mk_u64 1572317787530805;
        mk_u64 683053064812840;
        mk_u64 317374165784489;
        mk_u64 1572899562415810
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_FieldElement

/// `= sqrt(a*d - 1)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.
let v_SQRT_AD_MINUS_ONE: t_FieldElement =
  FieldElement
  (let list =
      [
        mk_u64 2241493124984347;
        mk_u64 425987919032274;
        mk_u64 2207028919301688;
        mk_u64 1220490630685848;
        mk_u64 974799131293748
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_FieldElement

/// The value of minus one, equal to `-&FieldElement::ONE`
let v_MINUS_ONE: t_FieldElement =
  FieldElement
  (let list =
      [
        mk_u64 2251799813685228;
        mk_u64 2251799813685247;
        mk_u64 2251799813685247;
        mk_u64 2251799813685247;
        mk_u64 2251799813685247
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_FieldElement

/// Edwards `2*d` value, equal to `2*(-121665/121666) mod p`.
let v_EDWARDS_D2: t_FieldElement =
  FieldElement
  (let list =
      [
        mk_u64 1859910466990425;
        mk_u64 932731440258426;
        mk_u64 1072319116312658;
        mk_u64 1815898335770999;
        mk_u64 633789495995903
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_FieldElement

let impl_1__from__field: Core_models.Clone.t_Clone t_FieldElement =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2__from__field': Core_models.Marker.t_Copy t_FieldElement

unfold
let impl_2__from__field = impl_2__from__field'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3__from__field': Core_models.Fmt.t_Debug t_FieldElement

unfold
let impl_3__from__field = impl_3__from__field'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4__from__field': Core_models.Marker.t_StructuralPartialEq t_FieldElement

unfold
let impl_4__from__field = impl_4__from__field'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core_models.Cmp.t_PartialEq t_FieldElement t_FieldElement

unfold
let impl_5 = impl_5'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6__from__field': Core_models.Cmp.t_Eq t_FieldElement

unfold
let impl_6__from__field = impl_6__from__field'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl__from__field: Ristretto255.Traits.t_Identity t_FieldElement =
  {
    f_identity_pre = (fun (_: Prims.unit) -> true);
    f_identity_post = (fun (_: Prims.unit) (out: t_FieldElement) -> true);
    f_identity
    =
    fun (_: Prims.unit) ->
      FieldElement (Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 5)) <: t_FieldElement
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8__from__field: Core_models.Ops.Arith.t_Add t_FieldElement t_FieldElement =
  {
    f_Output = t_FieldElement;
    f_add_pre = (fun (self: t_FieldElement) (rhs: t_FieldElement) -> true);
    f_add_post = (fun (self: t_FieldElement) (rhs: t_FieldElement) (out1: t_FieldElement) -> true);
    f_add
    =
    fun (self: t_FieldElement) (rhs: t_FieldElement) ->
      let out:t_Array u64 (mk_usize 5) = Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 5) in
      let out:t_Array u64 (mk_usize 5) =
        Libcrux_hacl_rs.Bignum25519_51_.fadd out (self._0 <: t_Slice u64) (rhs._0 <: t_Slice u64)
      in
      FieldElement out <: t_FieldElement
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9__from__field: Core_models.Ops.Arith.t_Sub t_FieldElement t_FieldElement =
  {
    f_Output = t_FieldElement;
    f_sub_pre = (fun (self: t_FieldElement) (rhs: t_FieldElement) -> true);
    f_sub_post = (fun (self: t_FieldElement) (rhs: t_FieldElement) (out1: t_FieldElement) -> true);
    f_sub
    =
    fun (self: t_FieldElement) (rhs: t_FieldElement) ->
      let out:t_Array u64 (mk_usize 5) = Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 5) in
      let out:t_Array u64 (mk_usize 5) =
        Libcrux_hacl_rs.Bignum25519_51_.fsub out (self._0 <: t_Slice u64) (rhs._0 <: t_Slice u64)
      in
      FieldElement out <: t_FieldElement
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10__from__field: Core_models.Ops.Arith.t_Mul t_FieldElement u64 =
  {
    f_Output = t_FieldElement;
    f_mul_pre = (fun (self: t_FieldElement) (rhs: u64) -> true);
    f_mul_post = (fun (self: t_FieldElement) (rhs: u64) (out1: t_FieldElement) -> true);
    f_mul
    =
    fun (self: t_FieldElement) (rhs: u64) ->
      let out:t_Array u64 (mk_usize 5) = Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 5) in
      let out:t_Array u64 (mk_usize 5) =
        Libcrux_hacl_rs.Bignum25519_51_.fmul1 out (self._0 <: t_Slice u64) rhs
      in
      FieldElement out <: t_FieldElement
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11__from__field: Core_models.Ops.Arith.t_Mul t_FieldElement t_FieldElement =
  {
    f_Output = t_FieldElement;
    f_mul_pre = (fun (self: t_FieldElement) (rhs: t_FieldElement) -> true);
    f_mul_post = (fun (self: t_FieldElement) (rhs: t_FieldElement) (out1: t_FieldElement) -> true);
    f_mul
    =
    fun (self: t_FieldElement) (rhs: t_FieldElement) ->
      let out:t_Array u64 (mk_usize 5) = Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 5) in
      let (tmp: t_Array u128 (mk_usize 10)):t_Array u128 (mk_usize 10) =
        Rust_primitives.Hax.repeat (Libcrux_hacl_rs.Fstar.Uint128.uint64_to_uint128 (mk_u64 0)
            <:
            u128)
          (mk_usize 10)
      in
      let out:t_Array u64 (mk_usize 5) =
        Libcrux_hacl_rs.Bignum25519_51_.fmul out
          (self._0 <: t_Slice u64)
          (rhs._0 <: t_Slice u64)
          (tmp <: t_Slice u128)
      in
      FieldElement out <: t_FieldElement
  }

/// Mask for the low 51 bits: 51 ones = `0x7FFFFFFFFFFFF`.
/// Equivalent to `(1u64 << 51) - 1`
let v_LOW_51_BIT_MASK: u64 = mk_u64 2251799813685247

let impl_12__ZERO: t_FieldElement =
  FieldElement
  (let list = [mk_u64 0; mk_u64 0; mk_u64 0; mk_u64 0; mk_u64 0] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_FieldElement

let impl_12__ONE: t_FieldElement =
  FieldElement
  (let list = [mk_u64 1; mk_u64 0; mk_u64 0; mk_u64 0; mk_u64 0] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_FieldElement

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl__from__backend: Ristretto255.Traits.t_Identity t_EdwardsPoint =
  {
    f_identity_pre = (fun (_: Prims.unit) -> true);
    f_identity_post = (fun (_: Prims.unit) (out: t_EdwardsPoint) -> true);
    f_identity
    =
    fun (_: Prims.unit) ->
      { f_X = impl_12__ZERO; f_Y = impl_12__ONE; f_Z = impl_12__ONE; f_T = impl_12__ZERO }
      <:
      t_EdwardsPoint
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Ristretto255.Traits.t_Identity t_RistrettoPoint =
  {
    f_identity_pre = (fun (_: Prims.unit) -> true);
    f_identity_post = (fun (_: Prims.unit) (out: t_RistrettoPoint) -> true);
    f_identity
    =
    fun (_: Prims.unit) ->
      RistrettoPoint
      (Ristretto255.Traits.f_identity #t_EdwardsPoint #FStar.Tactics.Typeclasses.solve ())
      <:
      t_RistrettoPoint
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core_models.Default.t_Default t_RistrettoPoint =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_RistrettoPoint) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      Ristretto255.Traits.f_identity #t_RistrettoPoint #FStar.Tactics.Typeclasses.solve ()
  }

/// The scalar \\\\( -1 \\\\).
let impl_12__MINUS_ONE: t_FieldElement =
  FieldElement
  (let list =
      [
        mk_u64 2251799813685228;
        mk_u64 2251799813685247;
        mk_u64 2251799813685247;
        mk_u64 2251799813685247;
        mk_u64 2251799813685247
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_FieldElement

/// Serialize this field element to canonical 32-byte encoding.
/// Adapted from the `curve25519-dalek` crate.
assume
val impl_12__to_bytes': self: t_FieldElement -> t_Array u8 (mk_usize 32)

unfold
let impl_12__to_bytes = impl_12__to_bytes'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7__from__field: Subtle.t_ConstantTimeEq t_FieldElement =
  {
    f_ct_eq_pre = (fun (self: t_FieldElement) (other: t_FieldElement) -> true);
    f_ct_eq_post
    =
    (fun (self: t_FieldElement) (other: t_FieldElement) (out: Subtle.t_Choice) -> true);
    f_ct_eq
    =
    fun (self: t_FieldElement) (other: t_FieldElement) ->
      Subtle.f_ct_eq #(t_Slice u8)
        #FStar.Tactics.Typeclasses.solve
        (impl_12__to_bytes self <: t_Slice u8)
        (impl_12__to_bytes other <: t_Slice u8)
  }

let impl_12__square (self: t_FieldElement) : t_FieldElement =
  let (out: t_Array u64 (mk_usize 5)):t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 5)
  in
  let (tmp: t_Array u128 (mk_usize 10)):t_Array u128 (mk_usize 10) =
    Rust_primitives.Hax.repeat (Libcrux_hacl_rs.Fstar.Uint128.uint64_to_uint128 (mk_u64 0) <: u128)
      (mk_usize 10)
  in
  let out:t_Array u64 (mk_usize 5) =
    Libcrux_hacl_rs.Bignum25519_51_.fsqr out (self._0 <: t_Slice u64) (tmp <: t_Slice u128)
  in
  FieldElement out <: t_FieldElement

let impl_12__is_negative (self: t_FieldElement) : Subtle.t_Choice =
  let bytes:t_Array u8 (mk_usize 32) = impl_12__to_bytes self in
  Core_models.Convert.f_into #u8
    #Subtle.t_Choice
    #FStar.Tactics.Typeclasses.solve
    ((bytes.[ mk_usize 0 ] <: u8) &. mk_u8 1 <: u8)

let impl_12__is_zero (self: t_FieldElement) : Subtle.t_Choice =
  let zero:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let bytes:t_Array u8 (mk_usize 32) = impl_12__to_bytes self in
  Subtle.f_ct_eq #(t_Slice u8)
    #FStar.Tactics.Typeclasses.solve
    (bytes <: t_Slice u8)
    (zero <: t_Slice u8)

let impl_12__conditional_negate (self: t_FieldElement) (choice: Subtle.t_Choice) : t_FieldElement =
  let neg:t_FieldElement =
    Core_models.Ops.Arith.f_sub #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      (Ristretto255.Traits.f_identity #t_FieldElement #FStar.Tactics.Typeclasses.solve ()
        <:
        t_FieldElement)
      self
  in
  let mask:u64 =
    Core_models.Num.impl_u64__wrapping_sub (mk_u64 0)
      (cast (Subtle.impl_Choice__unwrap_u8 choice <: u8) <: u64)
  in
  let self:t_FieldElement =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 5)
      (fun self temp_1_ ->
          let self:t_FieldElement = self in
          let _:usize = temp_1_ in
          true)
      self
      (fun self i ->
          let self:t_FieldElement = self in
          let i:usize = i in
          {
            self with
            _0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self._0
              i
              ((self._0.[ i ] <: u64) ^.
                (mask &. ((self._0.[ i ] <: u64) ^. (neg._0.[ i ] <: u64) <: u64) <: u64)
                <:
                u64)
            <:
            t_Array u64 (mk_usize 5)
          }
          <:
          t_FieldElement)
  in
  self

let impl_12__conditional_assign (self other: t_FieldElement) (choice: Subtle.t_Choice)
    : t_FieldElement =
  let mask:u64 =
    Core_models.Num.impl_u64__wrapping_sub (mk_u64 0)
      (cast (Subtle.impl_Choice__unwrap_u8 choice <: u8) <: u64)
  in
  let self:t_FieldElement =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 5)
      (fun self temp_1_ ->
          let self:t_FieldElement = self in
          let _:usize = temp_1_ in
          true)
      self
      (fun self i ->
          let self:t_FieldElement = self in
          let i:usize = i in
          {
            self with
            _0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self._0
              i
              ((self._0.[ i ] <: u64) ^.
                (mask &. ((self._0.[ i ] <: u64) ^. (other._0.[ i ] <: u64) <: u64) <: u64)
                <:
                u64)
            <:
            t_Array u64 (mk_usize 5)
          }
          <:
          t_FieldElement)
  in
  self

/// Raise this field element to the power (p-5)/8 = 2^252 - 3.
assume
val impl_12__pow_p58': self: t_FieldElement -> t_FieldElement

unfold
let impl_12__pow_p58 = impl_12__pow_p58'

let impl_12__load8_at (input: t_Array u8 (mk_usize 32)) (i: usize)
    : Prims.Pure u64 (requires Rust_primitives.Integers.v i + 7 < 32) (fun _ -> Prims.l_True) =
  (((((((cast (input.[ i ] <: u8) <: u64) |.
              ((cast (input.[ i +! mk_usize 1 <: usize ] <: u8) <: u64) <<! mk_i32 8 <: u64)
              <:
              u64) |.
            ((cast (input.[ i +! mk_usize 2 <: usize ] <: u8) <: u64) <<! mk_i32 16 <: u64)
            <:
            u64) |.
          ((cast (input.[ i +! mk_usize 3 <: usize ] <: u8) <: u64) <<! mk_i32 24 <: u64)
          <:
          u64) |.
        ((cast (input.[ i +! mk_usize 4 <: usize ] <: u8) <: u64) <<! mk_i32 32 <: u64)
        <:
        u64) |.
      ((cast (input.[ i +! mk_usize 5 <: usize ] <: u8) <: u64) <<! mk_i32 40 <: u64)
      <:
      u64) |.
    ((cast (input.[ i +! mk_usize 6 <: usize ] <: u8) <: u64) <<! mk_i32 48 <: u64)
    <:
    u64) |.
  ((cast (input.[ i +! mk_usize 7 <: usize ] <: u8) <: u64) <<! mk_i32 56 <: u64)

/// Load a field element from the low 255 bits of a 32-byte input.
/// This is intentionally non-canonical: it masks the top bit and does not
/// reject inputs >= p.
/// Adapted from the `curve25519-dalek` crate.
let impl_12__from_bytes (bytes: t_Array u8 (mk_usize 32)) : t_FieldElement =
  let low_51_bit_mask:u64 = v_LOW_51_BIT_MASK in
  FieldElement
  (let list =
      [
        (impl_12__load8_at bytes (mk_usize 0) <: u64) &. low_51_bit_mask;
        ((impl_12__load8_at bytes (mk_usize 6) <: u64) >>! mk_i32 3 <: u64) &. low_51_bit_mask;
        ((impl_12__load8_at bytes (mk_usize 12) <: u64) >>! mk_i32 6 <: u64) &. low_51_bit_mask;
        ((impl_12__load8_at bytes (mk_usize 19) <: u64) >>! mk_i32 1 <: u64) &. low_51_bit_mask;
        ((impl_12__load8_at bytes (mk_usize 24) <: u64) >>! mk_i32 12 <: u64) &. low_51_bit_mask
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_FieldElement

let step_1_ (repr: t_CompressedRistretto) : (Subtle.t_Choice & Subtle.t_Choice & t_FieldElement) =
  let s:t_FieldElement = impl_12__from_bytes (impl_19__as_bytes repr <: t_Array u8 (mk_usize 32)) in
  let s_bytes_check:t_Array u8 (mk_usize 32) = impl_12__to_bytes s in
  let s_encoding_is_canonical:Subtle.t_Choice =
    Subtle.f_ct_eq #(t_Slice u8)
      #FStar.Tactics.Typeclasses.solve
      (s_bytes_check.[ Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull ]
        <:
        t_Slice u8)
      (impl_19__as_bytes repr <: t_Slice u8)
  in
  let s_is_negative:Subtle.t_Choice = impl_12__is_negative s in
  s_encoding_is_canonical, s_is_negative, s <: (Subtle.t_Choice & Subtle.t_Choice & t_FieldElement)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13__from__field: Core_models.Ops.Arith.t_Add t_FieldElement t_FieldElement =
  {
    f_Output = t_FieldElement;
    f_add_pre = (fun (self: t_FieldElement) (rhs: t_FieldElement) -> true);
    f_add_post = (fun (self: t_FieldElement) (rhs: t_FieldElement) (out: t_FieldElement) -> true);
    f_add
    =
    fun (self: t_FieldElement) (rhs: t_FieldElement) ->
      Core_models.Ops.Arith.f_add #t_FieldElement
        #t_FieldElement
        #FStar.Tactics.Typeclasses.solve
        self
        rhs
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14__from__field: Core_models.Ops.Arith.t_Sub t_FieldElement t_FieldElement =
  {
    f_Output = t_FieldElement;
    f_sub_pre = (fun (self: t_FieldElement) (rhs: t_FieldElement) -> true);
    f_sub_post = (fun (self: t_FieldElement) (rhs: t_FieldElement) (out: t_FieldElement) -> true);
    f_sub
    =
    fun (self: t_FieldElement) (rhs: t_FieldElement) ->
      Core_models.Ops.Arith.f_sub #t_FieldElement
        #t_FieldElement
        #FStar.Tactics.Typeclasses.solve
        self
        rhs
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15__from__field: Core_models.Ops.Arith.t_Mul t_FieldElement t_FieldElement =
  {
    f_Output = t_FieldElement;
    f_mul_pre = (fun (self: t_FieldElement) (rhs: t_FieldElement) -> true);
    f_mul_post = (fun (self: t_FieldElement) (rhs: t_FieldElement) (out: t_FieldElement) -> true);
    f_mul
    =
    fun (self: t_FieldElement) (rhs: t_FieldElement) ->
      Core_models.Ops.Arith.f_mul #t_FieldElement
        #t_FieldElement
        #FStar.Tactics.Typeclasses.solve
        self
        rhs
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Subtle.t_ConstantTimeEq t_RistrettoPoint =
  {
    f_ct_eq_pre = (fun (self: t_RistrettoPoint) (other: t_RistrettoPoint) -> true);
    f_ct_eq_post
    =
    (fun (self: t_RistrettoPoint) (other: t_RistrettoPoint) (out: Subtle.t_Choice) -> true);
    f_ct_eq
    =
    fun (self: t_RistrettoPoint) (other: t_RistrettoPoint) ->
      let v_X1Y2:t_FieldElement =
        Core_models.Ops.Arith.f_mul #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          self._0.f_X
          other._0.f_Y
      in
      let v_Y1X2:t_FieldElement =
        Core_models.Ops.Arith.f_mul #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          self._0.f_Y
          other._0.f_X
      in
      let v_X1X2:t_FieldElement =
        Core_models.Ops.Arith.f_mul #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          self._0.f_X
          other._0.f_X
      in
      let v_Y1Y2:t_FieldElement =
        Core_models.Ops.Arith.f_mul #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          self._0.f_Y
          other._0.f_Y
      in
      Core_models.Ops.Bit.f_bitor #Subtle.t_Choice
        #Subtle.t_Choice
        #FStar.Tactics.Typeclasses.solve
        (Subtle.f_ct_eq #t_FieldElement #FStar.Tactics.Typeclasses.solve v_X1Y2 v_Y1X2
          <:
          Subtle.t_Choice)
        (Subtle.f_ct_eq #t_FieldElement #FStar.Tactics.Typeclasses.solve v_X1X2 v_Y1Y2
          <:
          Subtle.t_Choice)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core_models.Cmp.t_PartialEq t_RistrettoPoint t_RistrettoPoint =
  {
    f_eq_pre = (fun (self: t_RistrettoPoint) (other: t_RistrettoPoint) -> true);
    f_eq_post = (fun (self: t_RistrettoPoint) (other: t_RistrettoPoint) (out: bool) -> true);
    f_eq
    =
    fun (self: t_RistrettoPoint) (other: t_RistrettoPoint) ->
      Core_models.Convert.f_into #Subtle.t_Choice
        #bool
        #FStar.Tactics.Typeclasses.solve
        (Subtle.f_ct_eq #t_RistrettoPoint #FStar.Tactics.Typeclasses.solve self other
          <:
          Subtle.t_Choice)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_23': Core_models.Cmp.t_Eq t_RistrettoPoint

unfold
let impl_23 = impl_23'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1__from__backend: Subtle.t_ConstantTimeEq t_EdwardsPoint =
  {
    f_ct_eq_pre = (fun (self: t_EdwardsPoint) (other: t_EdwardsPoint) -> true);
    f_ct_eq_post
    =
    (fun (self: t_EdwardsPoint) (other: t_EdwardsPoint) (out: Subtle.t_Choice) -> true);
    f_ct_eq
    =
    fun (self: t_EdwardsPoint) (other: t_EdwardsPoint) ->
      Core_models.Ops.Bit.f_bitand #Subtle.t_Choice
        #Subtle.t_Choice
        #FStar.Tactics.Typeclasses.solve
        (Subtle.f_ct_eq #t_FieldElement
            #FStar.Tactics.Typeclasses.solve
            (Core_models.Ops.Arith.f_mul #t_FieldElement
                #t_FieldElement
                #FStar.Tactics.Typeclasses.solve
                self.f_X
                other.f_Z
              <:
              t_FieldElement)
            (Core_models.Ops.Arith.f_mul #t_FieldElement
                #t_FieldElement
                #FStar.Tactics.Typeclasses.solve
                other.f_X
                self.f_Z
              <:
              t_FieldElement)
          <:
          Subtle.t_Choice)
        (Subtle.f_ct_eq #t_FieldElement
            #FStar.Tactics.Typeclasses.solve
            (Core_models.Ops.Arith.f_mul #t_FieldElement
                #t_FieldElement
                #FStar.Tactics.Typeclasses.solve
                self.f_Y
                other.f_Z
              <:
              t_FieldElement)
            (Core_models.Ops.Arith.f_mul #t_FieldElement
                #t_FieldElement
                #FStar.Tactics.Typeclasses.solve
                other.f_Y
                self.f_Z
              <:
              t_FieldElement)
          <:
          Subtle.t_Choice)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core_models.Cmp.t_PartialEq t_EdwardsPoint t_EdwardsPoint =
  {
    f_eq_pre = (fun (self: t_EdwardsPoint) (other: t_EdwardsPoint) -> true);
    f_eq_post = (fun (self: t_EdwardsPoint) (other: t_EdwardsPoint) (out: bool) -> true);
    f_eq
    =
    fun (self: t_EdwardsPoint) (other: t_EdwardsPoint) ->
      Core_models.Convert.f_into #Subtle.t_Choice
        #bool
        #FStar.Tactics.Typeclasses.solve
        (Subtle.f_ct_eq #t_EdwardsPoint #FStar.Tactics.Typeclasses.solve self other
          <:
          Subtle.t_Choice)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core_models.Cmp.t_Eq t_EdwardsPoint = { _super_i0 = FStar.Tactics.Typeclasses.solve }

/// Convert to a ProjectiveNielsPoint
let impl_4__as_projective_niels (self: t_EdwardsPoint) : t_ProjectiveNielsPoint =
  {
    f_Y_plus_X
    =
    Core_models.Ops.Arith.f_add #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      self.f_Y
      self.f_X;
    f_Y_minus_X
    =
    Core_models.Ops.Arith.f_sub #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      self.f_Y
      self.f_X;
    f_Z = self.f_Z;
    f_T2d
    =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      self.f_T
      v_EDWARDS_D2
  }
  <:
  t_ProjectiveNielsPoint

/// Convert this point from the \\( \mathbb P\^1 \times \mathbb P\^1
/// \\) model to the \\( \mathbb P\^3 \\) model.
/// This costs \\(4 \mathrm M \\).
let impl_4__as_extended (self: t_EdwardsPoint) : t_EdwardsPoint =
  {
    f_X
    =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      self.f_X
      self.f_T;
    f_Y
    =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      self.f_Y
      self.f_Z;
    f_Z
    =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      self.f_Z
      self.f_T;
    f_T
    =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      self.f_X
      self.f_Y
  }
  <:
  t_EdwardsPoint

/// Convert from the \\(\mathbb P^1 \times \mathbb P^1\\) model to
/// the \\(\mathbb P^3\\) (extended) model.
/// Cost: \\(4 \mathrm M\\).
let impl_5__as_extended (self: t_CompletedPoint) : t_EdwardsPoint =
  {
    f_X
    =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      self.f_X
      self.f_T;
    f_Y
    =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      self.f_Y
      self.f_Z;
    f_Z
    =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      self.f_Z
      self.f_T;
    f_T
    =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      self.f_X
      self.f_Y
  }
  <:
  t_EdwardsPoint

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6__from__backend: Core_models.Ops.Arith.t_Add t_EdwardsPoint t_ProjectiveNielsPoint =
  {
    f_Output = t_CompletedPoint;
    f_add_pre = (fun (self: t_EdwardsPoint) (other: t_ProjectiveNielsPoint) -> true);
    f_add_post
    =
    (fun (self: t_EdwardsPoint) (other: t_ProjectiveNielsPoint) (out: t_CompletedPoint) -> true);
    f_add
    =
    fun (self: t_EdwardsPoint) (other: t_ProjectiveNielsPoint) ->
      let v_Y_plus_X:t_FieldElement =
        Core_models.Ops.Arith.f_add #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          self.f_Y
          self.f_X
      in
      let v_Y_minus_X:t_FieldElement =
        Core_models.Ops.Arith.f_sub #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          self.f_Y
          self.f_X
      in
      let v_PP:t_FieldElement =
        Core_models.Ops.Arith.f_mul #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          v_Y_plus_X
          other.f_Y_plus_X
      in
      let v_MM:t_FieldElement =
        Core_models.Ops.Arith.f_mul #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          v_Y_minus_X
          other.f_Y_minus_X
      in
      let v_TT2d:t_FieldElement =
        Core_models.Ops.Arith.f_mul #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          self.f_T
          other.f_T2d
      in
      let v_ZZ:t_FieldElement =
        Core_models.Ops.Arith.f_mul #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          self.f_Z
          other.f_Z
      in
      let v_ZZ2:t_FieldElement =
        Core_models.Ops.Arith.f_add #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          v_ZZ
          v_ZZ
      in
      {
        f_X
        =
        Core_models.Ops.Arith.f_sub #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          v_PP
          v_MM;
        f_Y
        =
        Core_models.Ops.Arith.f_add #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          v_PP
          v_MM;
        f_Z
        =
        Core_models.Ops.Arith.f_add #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          v_ZZ2
          v_TT2d;
        f_T
        =
        Core_models.Ops.Arith.f_sub #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          v_ZZ2
          v_TT2d
      }
      <:
      t_CompletedPoint
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core_models.Ops.Arith.t_Add t_RistrettoPoint t_RistrettoPoint =
  {
    f_Output = t_RistrettoPoint;
    f_add_pre = (fun (self: t_RistrettoPoint) (other: t_RistrettoPoint) -> true);
    f_add_post
    =
    (fun (self: t_RistrettoPoint) (other: t_RistrettoPoint) (out: t_RistrettoPoint) -> true);
    f_add
    =
    fun (self: t_RistrettoPoint) (other: t_RistrettoPoint) ->
      RistrettoPoint
      (impl_5__as_extended (Core_models.Ops.Arith.f_add #t_EdwardsPoint
              #t_ProjectiveNielsPoint
              #FStar.Tactics.Typeclasses.solve
              self._0
              (impl_4__as_projective_niels other._0 <: t_ProjectiveNielsPoint)
            <:
            t_CompletedPoint))
      <:
      t_RistrettoPoint
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core_models.Ops.Arith.t_Add t_RistrettoPoint t_RistrettoPoint =
  {
    f_Output = t_RistrettoPoint;
    f_add_pre = (fun (self: t_RistrettoPoint) (other: t_RistrettoPoint) -> true);
    f_add_post
    =
    (fun (self: t_RistrettoPoint) (other: t_RistrettoPoint) (out: t_RistrettoPoint) -> true);
    f_add
    =
    fun (self: t_RistrettoPoint) (other: t_RistrettoPoint) ->
      Core_models.Ops.Arith.f_add #t_RistrettoPoint
        #t_RistrettoPoint
        #FStar.Tactics.Typeclasses.solve
        self
        other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16__from__field: Core_models.Ops.Arith.t_Neg t_FieldElement =
  {
    f_Output = t_FieldElement;
    f_neg_pre = (fun (self: t_FieldElement) -> true);
    f_neg_post = (fun (self: t_FieldElement) (out: t_FieldElement) -> true);
    f_neg
    =
    fun (self: t_FieldElement) ->
      Core_models.Ops.Arith.f_sub #t_FieldElement
        #t_FieldElement
        #FStar.Tactics.Typeclasses.solve
        (Ristretto255.Traits.f_identity #t_FieldElement #FStar.Tactics.Typeclasses.solve ()
          <:
          t_FieldElement)
        self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17__from__field: Core_models.Ops.Arith.t_Neg t_FieldElement =
  {
    f_Output = t_FieldElement;
    f_neg_pre = (fun (self: t_FieldElement) -> true);
    f_neg_post = (fun (self: t_FieldElement) (out: t_FieldElement) -> true);
    f_neg
    =
    fun (self: t_FieldElement) ->
      Core_models.Ops.Arith.f_neg #t_FieldElement #FStar.Tactics.Typeclasses.solve self
  }

/// Given `FieldElements` `u` and `v`, compute either `sqrt(u/v)`
/// or `sqrt(i*u/v)` in constant time.
/// This function always returns the nonnegative square root.
/// # Return
/// - `(Choice(1), +sqrt(u/v))  ` if `v` is nonzero and `u/v` is square;
/// - `(Choice(1), zero)        ` if `u` is zero;
/// - `(Choice(0), zero)        ` if `v` is zero and `u` is nonzero;
/// - `(Choice(0), +sqrt(i*u/v))` if `u/v` is nonsquare (so `i*u/v` is square).
let impl_12__sqrt_ratio_i (u v: t_FieldElement) : (Subtle.t_Choice & t_FieldElement) =
  let v3:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      (impl_12__square v <: t_FieldElement)
      v
  in
  let v7:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      (impl_12__square v3 <: t_FieldElement)
      v
  in
  let r:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_mul #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          u
          v3
        <:
        t_FieldElement)
      (impl_12__pow_p58 (Core_models.Ops.Arith.f_mul #t_FieldElement
              #t_FieldElement
              #FStar.Tactics.Typeclasses.solve
              u
              v7
            <:
            t_FieldElement)
        <:
        t_FieldElement)
  in
  let check:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      v
      (impl_12__square r <: t_FieldElement)
  in
  let i:t_FieldElement = v_SQRT_M1 in
  let correct_sign_sqrt:Subtle.t_Choice =
    Subtle.f_ct_eq #t_FieldElement #FStar.Tactics.Typeclasses.solve check u
  in
  let flipped_sign_sqrt:Subtle.t_Choice =
    Subtle.f_ct_eq #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      check
      (Core_models.Ops.Arith.f_neg #t_FieldElement #FStar.Tactics.Typeclasses.solve u
        <:
        t_FieldElement)
  in
  let flipped_sign_sqrt_i:Subtle.t_Choice =
    Subtle.f_ct_eq #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      check
      (Core_models.Ops.Arith.f_mul #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Ops.Arith.f_neg #t_FieldElement #FStar.Tactics.Typeclasses.solve u
            <:
            t_FieldElement)
          i
        <:
        t_FieldElement)
  in
  let r_prime:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      v_SQRT_M1
      r
  in
  let r:t_FieldElement =
    impl_12__conditional_assign r
      r_prime
      (Core_models.Ops.Bit.f_bitor #Subtle.t_Choice
          #Subtle.t_Choice
          #FStar.Tactics.Typeclasses.solve
          flipped_sign_sqrt
          flipped_sign_sqrt_i
        <:
        Subtle.t_Choice)
  in
  let r_is_negative:Subtle.t_Choice = impl_12__is_negative r in
  let r:t_FieldElement = impl_12__conditional_negate r r_is_negative in
  let was_nonzero_square:Subtle.t_Choice =
    Core_models.Ops.Bit.f_bitor #Subtle.t_Choice
      #Subtle.t_Choice
      #FStar.Tactics.Typeclasses.solve
      correct_sign_sqrt
      flipped_sign_sqrt
  in
  was_nonzero_square, r <: (Subtle.t_Choice & t_FieldElement)

/// Computes the Ristretto Elligator map for the given field element. This is the second half of
/// the [`MAP`](https://www.rfc-editor.org/rfc/rfc9496.html#section-4.3.4-4) function defined in
/// the Ristretto spec.
/// # Note
/// This method is not public because it's just used for hashing
/// to a point -- proper elligator support is deferred for now.
let impl_3__elligator_ristretto_flavor (r_0_: t_FieldElement) : t_RistrettoPoint =
  let i:t_FieldElement = v_SQRT_M1 in
  let d:t_FieldElement = v_EDWARDS_D in
  let one_minus_d_sq:t_FieldElement = v_ONE_MINUS_EDWARDS_D_SQUARED in
  let d_minus_one_sq:t_FieldElement = v_EDWARDS_D_MINUS_ONE_SQUARED in
  let c:t_FieldElement = v_MINUS_ONE in
  let one:t_FieldElement = impl_12__ONE in
  let r:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      i
      (impl_12__square r_0_ <: t_FieldElement)
  in
  let v_N_s:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_add #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          r
          one
        <:
        t_FieldElement)
      one_minus_d_sq
  in
  let v_D:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_sub #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          c
          (Core_models.Ops.Arith.f_mul #t_FieldElement
              #t_FieldElement
              #FStar.Tactics.Typeclasses.solve
              d
              r
            <:
            t_FieldElement)
        <:
        t_FieldElement)
      (Core_models.Ops.Arith.f_add #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          r
          d
        <:
        t_FieldElement)
  in
  let (v_Ns_D_is_sq: Subtle.t_Choice), (s: t_FieldElement) = impl_12__sqrt_ratio_i v_N_s v_D in
  let s_prime:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      s
      r_0_
  in
  let s_prime_is_pos:Subtle.t_Choice = ~.(impl_12__is_negative s_prime <: Subtle.t_Choice) in
  let s_prime:t_FieldElement = impl_12__conditional_negate s_prime s_prime_is_pos in
  let s:t_FieldElement =
    impl_12__conditional_assign s s_prime (~.v_Ns_D_is_sq <: Subtle.t_Choice)
  in
  let c:t_FieldElement = impl_12__conditional_assign c r (~.v_Ns_D_is_sq <: Subtle.t_Choice) in
  let v_N_t:t_FieldElement =
    Core_models.Ops.Arith.f_sub #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_mul #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Ops.Arith.f_mul #t_FieldElement
              #t_FieldElement
              #FStar.Tactics.Typeclasses.solve
              c
              (Core_models.Ops.Arith.f_sub #t_FieldElement
                  #t_FieldElement
                  #FStar.Tactics.Typeclasses.solve
                  r
                  one
                <:
                t_FieldElement)
            <:
            t_FieldElement)
          d_minus_one_sq
        <:
        t_FieldElement)
      v_D
  in
  let s_sq:t_FieldElement = impl_12__square s in
  RistrettoPoint
  (impl_5__as_extended ({
          f_X
          =
          Core_models.Ops.Arith.f_mul #t_FieldElement
            #t_FieldElement
            #FStar.Tactics.Typeclasses.solve
            (Core_models.Ops.Arith.f_add #t_FieldElement
                #t_FieldElement
                #FStar.Tactics.Typeclasses.solve
                s
                s
              <:
              t_FieldElement)
            v_D
          <:
          t_FieldElement;
          f_Z
          =
          Core_models.Ops.Arith.f_mul #t_FieldElement
            #t_FieldElement
            #FStar.Tactics.Typeclasses.solve
            v_N_t
            v_SQRT_AD_MINUS_ONE
          <:
          t_FieldElement;
          f_Y
          =
          Core_models.Ops.Arith.f_sub #t_FieldElement
            #t_FieldElement
            #FStar.Tactics.Typeclasses.solve
            impl_12__ONE
            s_sq
          <:
          t_FieldElement;
          f_T
          =
          Core_models.Ops.Arith.f_add #t_FieldElement
            #t_FieldElement
            #FStar.Tactics.Typeclasses.solve
            impl_12__ONE
            s_sq
          <:
          t_FieldElement
        }
        <:
        t_CompletedPoint))
  <:
  t_RistrettoPoint

/// Construct a `RistrettoPoint` from 64 bytes of data.
/// If the input bytes are uniformly distributed, the resulting
/// point will be uniformly distributed over the group, and its
/// discrete log with respect to other points should be unknown.
/// # Implementation
/// This function splits the input array into two 32-byte halves,
/// takes the low 255 bits of each half mod p, applies the
/// Ristretto-flavored Elligator map to each, and adds the results.
let impl_5__from_uniform_bytes (bytes: t_Array u8 (mk_usize 64)) : t_RistrettoPoint =
  let r_1_bytes:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let r_1_bytes:t_Array u8 (mk_usize 32) =
    Core_models.Slice.impl__copy_from_slice #u8
      r_1_bytes
      (bytes.[ {
            Core_models.Ops.Range.f_start = mk_usize 0;
            Core_models.Ops.Range.f_end = mk_usize 32
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let r_1_:t_FieldElement = impl_12__from_bytes r_1_bytes in
  let v_R_1_:t_RistrettoPoint = impl_3__elligator_ristretto_flavor r_1_ in
  let r_2_bytes:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let r_2_bytes:t_Array u8 (mk_usize 32) =
    Core_models.Slice.impl__copy_from_slice #u8
      r_2_bytes
      (bytes.[ {
            Core_models.Ops.Range.f_start = mk_usize 32;
            Core_models.Ops.Range.f_end = mk_usize 64
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let r_2_:t_FieldElement = impl_12__from_bytes r_2_bytes in
  let v_R_2_:t_RistrettoPoint = impl_3__elligator_ristretto_flavor r_2_ in
  Core_models.Ops.Arith.f_add #t_RistrettoPoint
    #t_RistrettoPoint
    #FStar.Tactics.Typeclasses.solve
    v_R_1_
    v_R_2_

/// Attempt to compute `sqrt(1/self)` in constant time.
/// Convenience wrapper around `sqrt_ratio_i`.
/// This function always returns the nonnegative square root.
/// # Return
/// - `(Choice(1), +sqrt(1/self))  ` if `self` is a nonzero square;
/// - `(Choice(0), zero)           ` if `self` is zero;
/// - `(Choice(0), +sqrt(i/self))  ` if `self` is a nonzero nonsquare;
let impl_12__invsqrt (self: t_FieldElement) : (Subtle.t_Choice & t_FieldElement) =
  impl_12__sqrt_ratio_i impl_12__ONE self

/// Compress this point using the Ristretto encoding.
let impl_2__compress (self: t_RistrettoPoint) : t_CompressedRistretto =
  let v_X:t_FieldElement = self._0.f_X in
  let v_Y:t_FieldElement = self._0.f_Y in
  let v_Z:t_FieldElement = self._0.f_Z in
  let v_T:t_FieldElement = self._0.f_T in
  let u1:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_add #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          v_Z
          v_Y
        <:
        t_FieldElement)
      (Core_models.Ops.Arith.f_sub #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          v_Z
          v_Y
        <:
        t_FieldElement)
  in
  let u2:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      v_X
      v_Y
  in
  let (_: Subtle.t_Choice), (invsqrt: t_FieldElement) =
    impl_12__invsqrt (Core_models.Ops.Arith.f_mul #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          u1
          (impl_12__square u2 <: t_FieldElement)
        <:
        t_FieldElement)
  in
  let i1:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      invsqrt
      u1
  in
  let i2:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      invsqrt
      u2
  in
  let z_inv:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      i1
      (Core_models.Ops.Arith.f_mul #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          i2
          v_T
        <:
        t_FieldElement)
  in
  let den_inv:t_FieldElement = i2 in
  let iX:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      v_X
      v_SQRT_M1
  in
  let iY:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      v_Y
      v_SQRT_M1
  in
  let ristretto_magic:t_FieldElement = v_INVSQRT_A_MINUS_D in
  let enchanted_denominator:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      i1
      ristretto_magic
  in
  let rotate:Subtle.t_Choice =
    impl_12__is_negative (Core_models.Ops.Arith.f_mul #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          v_T
          z_inv
        <:
        t_FieldElement)
  in
  let v_X:t_FieldElement = impl_12__conditional_assign v_X iY rotate in
  let v_Y:t_FieldElement = impl_12__conditional_assign v_Y iX rotate in
  let den_inv:t_FieldElement = impl_12__conditional_assign den_inv enchanted_denominator rotate in
  let v_Y:t_FieldElement =
    impl_12__conditional_negate v_Y
      (impl_12__is_negative (Core_models.Ops.Arith.f_mul #t_FieldElement
              #t_FieldElement
              #FStar.Tactics.Typeclasses.solve
              v_X
              z_inv
            <:
            t_FieldElement)
        <:
        Subtle.t_Choice)
  in
  let s:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      den_inv
      (Core_models.Ops.Arith.f_sub #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          v_Z
          v_Y
        <:
        t_FieldElement)
  in
  let s_is_negative:Subtle.t_Choice = impl_12__is_negative s in
  let s:t_FieldElement = impl_12__conditional_negate s s_is_negative in
  CompressedRistretto (impl_12__to_bytes s) <: t_CompressedRistretto

let step_2_ (s: t_FieldElement)
    : (Subtle.t_Choice & Subtle.t_Choice & Subtle.t_Choice & t_RistrettoPoint) =
  let one:t_FieldElement = impl_12__ONE in
  let ss:t_FieldElement = impl_12__square s in
  let u1:t_FieldElement =
    Core_models.Ops.Arith.f_sub #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      one
      ss
  in
  let u2:t_FieldElement =
    Core_models.Ops.Arith.f_add #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      one
      ss
  in
  let u2_sqr:t_FieldElement = impl_12__square u2 in
  let v:t_FieldElement =
    Core_models.Ops.Arith.f_sub #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_mul #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Ops.Arith.f_neg #t_FieldElement #FStar.Tactics.Typeclasses.solve v_EDWARDS_D
            <:
            t_FieldElement)
          (impl_12__square u1 <: t_FieldElement)
        <:
        t_FieldElement)
      u2_sqr
  in
  let (ok: Subtle.t_Choice), (v_I: t_FieldElement) =
    impl_12__invsqrt (Core_models.Ops.Arith.f_mul #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          v
          u2_sqr
        <:
        t_FieldElement)
  in
  let v_Dx:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      v_I
      u2
  in
  let v_Dy:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      v_I
      (Core_models.Ops.Arith.f_mul #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          v_Dx
          v
        <:
        t_FieldElement)
  in
  let x:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_add #t_FieldElement
          #t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          s
          s
        <:
        t_FieldElement)
      v_Dx
  in
  let x_neg:Subtle.t_Choice = impl_12__is_negative x in
  let x:t_FieldElement = impl_12__conditional_negate x x_neg in
  let y:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      u1
      v_Dy
  in
  let t:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement #t_FieldElement #FStar.Tactics.Typeclasses.solve x y
  in
  ok,
  impl_12__is_negative t,
  impl_12__is_zero y,
  (RistrettoPoint ({ f_X = x; f_Y = y; f_Z = one; f_T = t } <: t_EdwardsPoint) <: t_RistrettoPoint)
  <:
  (Subtle.t_Choice & Subtle.t_Choice & Subtle.t_Choice & t_RistrettoPoint)

/// Attempt to decompress to an `RistrettoPoint`.
/// # Return
/// - `Some(RistrettoPoint)` if `self` was the canonical encoding of a point;
/// - `None` if `self` was not the canonical encoding of a point.
let impl_19__decompress (self: t_CompressedRistretto) : Core_models.Option.t_Option t_RistrettoPoint =
  let
  (s_encoding_is_canonical: Subtle.t_Choice), (s_is_negative: Subtle.t_Choice), (s: t_FieldElement)
  =
    step_1_ self
  in
  if
    Core_models.Convert.f_into #Subtle.t_Choice
      #bool
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Bit.f_bitor #Subtle.t_Choice
          #Subtle.t_Choice
          #FStar.Tactics.Typeclasses.solve
          (~.s_encoding_is_canonical <: Subtle.t_Choice)
          s_is_negative
        <:
        Subtle.t_Choice)
  then Core_models.Option.Option_None <: Core_models.Option.t_Option t_RistrettoPoint
  else
    let
    (ok: Subtle.t_Choice),
    (tt_is_negative: Subtle.t_Choice),
    (y_is_zero: Subtle.t_Choice),
    (res: t_RistrettoPoint) =
      step_2_ s
    in
    if
      Core_models.Convert.f_into #Subtle.t_Choice
        #bool
        #FStar.Tactics.Typeclasses.solve
        (Core_models.Ops.Bit.f_bitor #Subtle.t_Choice
            #Subtle.t_Choice
            #FStar.Tactics.Typeclasses.solve
            (Core_models.Ops.Bit.f_bitor #Subtle.t_Choice
                #Subtle.t_Choice
                #FStar.Tactics.Typeclasses.solve
                (~.ok <: Subtle.t_Choice)
                tt_is_negative
              <:
              Subtle.t_Choice)
            y_is_zero
          <:
          Subtle.t_Choice)
    then Core_models.Option.Option_None <: Core_models.Option.t_Option t_RistrettoPoint
    else Core_models.Option.Option_Some res <: Core_models.Option.t_Option t_RistrettoPoint
