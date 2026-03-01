module Ristretto255.Bundle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Curve25519_dalek.Traits in
  let open Subtle in
  ()

type t_FieldElement = | FieldElement : t_Array u64 (mk_usize 5) -> t_FieldElement

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

let impl_11: Core_models.Clone.t_Clone t_FieldElement =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_12': Core_models.Marker.t_Copy t_FieldElement

unfold
let impl_12 = impl_12'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_13': Core_models.Fmt.t_Debug t_FieldElement

unfold
let impl_13 = impl_13'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_14': Core_models.Marker.t_StructuralPartialEq t_FieldElement

unfold
let impl_14 = impl_14'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_15': Core_models.Cmp.t_PartialEq t_FieldElement t_FieldElement

unfold
let impl_15 = impl_15'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_16': Core_models.Cmp.t_Eq t_FieldElement

unfold
let impl_16 = impl_16'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Curve25519_dalek.Traits.t_Identity t_FieldElement =
  {
    f_identity_pre = (fun (_: Prims.unit) -> true);
    f_identity_post = (fun (_: Prims.unit) (out: t_FieldElement) -> true);
    f_identity
    =
    fun (_: Prims.unit) ->
      FieldElement (Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 5)) <: t_FieldElement
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core_models.Ops.Arith.t_Add t_FieldElement t_FieldElement =
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
let impl_3: Core_models.Ops.Arith.t_Sub t_FieldElement t_FieldElement =
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
let impl_4: Core_models.Ops.Arith.t_Mul t_FieldElement u64 =
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
let impl_5: Core_models.Ops.Arith.t_Mul t_FieldElement t_FieldElement =
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

let impl_17__ONE: t_FieldElement =
  FieldElement
  (let list = [mk_u64 1; mk_u64 0; mk_u64 0; mk_u64 0; mk_u64 0] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_FieldElement

let impl_17__square (self: t_FieldElement) : t_FieldElement =
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

let impl_17__conditional_negate (self: t_FieldElement) (choice: Subtle.t_Choice) : t_FieldElement =
  let neg:t_FieldElement =
    Core_models.Ops.Arith.f_sub #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      (Curve25519_dalek.Traits.f_identity #t_FieldElement #FStar.Tactics.Typeclasses.solve ()
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

let impl_17__conditional_assign (self other: t_FieldElement) (choice: Subtle.t_Choice)
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

let impl_17__from_bytes__load8_at (input: t_Array u8 (mk_usize 32)) (i: usize) : u64 =
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
let impl_17__from_bytes (bytes: t_Array u8 (mk_usize 32))
    : Prims.Pure t_FieldElement
      Prims.l_True
      (ensures
        fun r ->
          let r:t_FieldElement = r in
          (r._0.[ mk_usize 0 ] <: u64) <. (mk_u64 1 <<! mk_i32 51 <: u64) &&
          (r._0.[ mk_usize 1 ] <: u64) <. (mk_u64 1 <<! mk_i32 51 <: u64) &&
          (r._0.[ mk_usize 2 ] <: u64) <. (mk_u64 1 <<! mk_i32 51 <: u64) &&
          (r._0.[ mk_usize 3 ] <: u64) <. (mk_u64 1 <<! mk_i32 51 <: u64) &&
          (r._0.[ mk_usize 4 ] <: u64) <. (mk_u64 1 <<! mk_i32 51 <: u64)) =
  let low_51_bit_mask:u64 = (mk_u64 1 <<! mk_i32 51 <: u64) -! mk_u64 1 in
  FieldElement
  (let list =
      [
        (impl_17__from_bytes__load8_at bytes (mk_usize 0) <: u64) &. low_51_bit_mask;
        ((impl_17__from_bytes__load8_at bytes (mk_usize 6) <: u64) >>! mk_i32 3 <: u64) &.
        low_51_bit_mask;
        ((impl_17__from_bytes__load8_at bytes (mk_usize 12) <: u64) >>! mk_i32 6 <: u64) &.
        low_51_bit_mask;
        ((impl_17__from_bytes__load8_at bytes (mk_usize 19) <: u64) >>! mk_i32 1 <: u64) &.
        low_51_bit_mask;
        ((impl_17__from_bytes__load8_at bytes (mk_usize 24) <: u64) >>! mk_i32 12 <: u64) &.
        low_51_bit_mask
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_FieldElement

/// Serialize this field element to canonical 32-byte encoding.
/// Adapted from the `curve25519-dalek` crate.
let impl_17__to_bytes (self: t_FieldElement)
    : Prims.Pure (t_Array u8 (mk_usize 32))
      Prims.l_True
      (ensures
        fun r ->
          let r:t_Array u8 (mk_usize 32) = r in
          ((r.[ mk_usize 31 ] <: u8) &. mk_u8 128 <: u8) =. mk_u8 0) =
  let low_51_bit_mask:u64 = (mk_u64 1 <<! mk_i32 51 <: u64) -! mk_u64 1 in
  let limbs:t_Array u64 (mk_usize 5) = self._0 in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 1)
      ((limbs.[ mk_usize 1 ] <: u64) +! ((limbs.[ mk_usize 0 ] <: u64) >>! mk_i32 51 <: u64) <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 0)
      ((limbs.[ mk_usize 0 ] <: u64) &. low_51_bit_mask <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 2)
      ((limbs.[ mk_usize 2 ] <: u64) +! ((limbs.[ mk_usize 1 ] <: u64) >>! mk_i32 51 <: u64) <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 1)
      ((limbs.[ mk_usize 1 ] <: u64) &. low_51_bit_mask <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 3)
      ((limbs.[ mk_usize 3 ] <: u64) +! ((limbs.[ mk_usize 2 ] <: u64) >>! mk_i32 51 <: u64) <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 2)
      ((limbs.[ mk_usize 2 ] <: u64) &. low_51_bit_mask <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 4)
      ((limbs.[ mk_usize 4 ] <: u64) +! ((limbs.[ mk_usize 3 ] <: u64) >>! mk_i32 51 <: u64) <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 3)
      ((limbs.[ mk_usize 3 ] <: u64) &. low_51_bit_mask <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 0)
      ((limbs.[ mk_usize 0 ] <: u64) +!
        (((limbs.[ mk_usize 4 ] <: u64) >>! mk_i32 51 <: u64) *! mk_u64 19 <: u64)
        <:
        u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 4)
      ((limbs.[ mk_usize 4 ] <: u64) &. low_51_bit_mask <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 1)
      ((limbs.[ mk_usize 1 ] <: u64) +! ((limbs.[ mk_usize 0 ] <: u64) >>! mk_i32 51 <: u64) <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 0)
      ((limbs.[ mk_usize 0 ] <: u64) &. low_51_bit_mask <: u64)
  in
  let q:u64 = ((limbs.[ mk_usize 0 ] <: u64) +! mk_u64 19 <: u64) >>! mk_i32 51 in
  let q:u64 = ((limbs.[ mk_usize 1 ] <: u64) +! q <: u64) >>! mk_i32 51 in
  let q:u64 = ((limbs.[ mk_usize 2 ] <: u64) +! q <: u64) >>! mk_i32 51 in
  let q:u64 = ((limbs.[ mk_usize 3 ] <: u64) +! q <: u64) >>! mk_i32 51 in
  let q:u64 = ((limbs.[ mk_usize 4 ] <: u64) +! q <: u64) >>! mk_i32 51 in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 0)
      ((limbs.[ mk_usize 0 ] <: u64) +! (mk_u64 19 *! q <: u64) <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 1)
      ((limbs.[ mk_usize 1 ] <: u64) +! ((limbs.[ mk_usize 0 ] <: u64) >>! mk_i32 51 <: u64) <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 0)
      ((limbs.[ mk_usize 0 ] <: u64) &. low_51_bit_mask <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 2)
      ((limbs.[ mk_usize 2 ] <: u64) +! ((limbs.[ mk_usize 1 ] <: u64) >>! mk_i32 51 <: u64) <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 1)
      ((limbs.[ mk_usize 1 ] <: u64) &. low_51_bit_mask <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 3)
      ((limbs.[ mk_usize 3 ] <: u64) +! ((limbs.[ mk_usize 2 ] <: u64) >>! mk_i32 51 <: u64) <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 2)
      ((limbs.[ mk_usize 2 ] <: u64) &. low_51_bit_mask <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 4)
      ((limbs.[ mk_usize 4 ] <: u64) +! ((limbs.[ mk_usize 3 ] <: u64) >>! mk_i32 51 <: u64) <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 3)
      ((limbs.[ mk_usize 3 ] <: u64) &. low_51_bit_mask <: u64)
  in
  let limbs:t_Array u64 (mk_usize 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize limbs
      (mk_usize 4)
      ((limbs.[ mk_usize 4 ] <: u64) &. low_51_bit_mask <: u64)
  in
  let s:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 0)
      (cast (limbs.[ mk_usize 0 ] <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 1)
      (cast ((limbs.[ mk_usize 0 ] <: u64) >>! mk_i32 8 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 2)
      (cast ((limbs.[ mk_usize 0 ] <: u64) >>! mk_i32 16 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 3)
      (cast ((limbs.[ mk_usize 0 ] <: u64) >>! mk_i32 24 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 4)
      (cast ((limbs.[ mk_usize 0 ] <: u64) >>! mk_i32 32 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 5)
      (cast ((limbs.[ mk_usize 0 ] <: u64) >>! mk_i32 40 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 6)
      (cast (((limbs.[ mk_usize 0 ] <: u64) >>! mk_i32 48 <: u64) |.
            ((limbs.[ mk_usize 1 ] <: u64) <<! mk_i32 3 <: u64)
            <:
            u64)
        <:
        u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 7)
      (cast ((limbs.[ mk_usize 1 ] <: u64) >>! mk_i32 5 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 8)
      (cast ((limbs.[ mk_usize 1 ] <: u64) >>! mk_i32 13 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 9)
      (cast ((limbs.[ mk_usize 1 ] <: u64) >>! mk_i32 21 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 10)
      (cast ((limbs.[ mk_usize 1 ] <: u64) >>! mk_i32 29 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 11)
      (cast ((limbs.[ mk_usize 1 ] <: u64) >>! mk_i32 37 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 12)
      (cast (((limbs.[ mk_usize 1 ] <: u64) >>! mk_i32 45 <: u64) |.
            ((limbs.[ mk_usize 2 ] <: u64) <<! mk_i32 6 <: u64)
            <:
            u64)
        <:
        u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 13)
      (cast ((limbs.[ mk_usize 2 ] <: u64) >>! mk_i32 2 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 14)
      (cast ((limbs.[ mk_usize 2 ] <: u64) >>! mk_i32 10 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 15)
      (cast ((limbs.[ mk_usize 2 ] <: u64) >>! mk_i32 18 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 16)
      (cast ((limbs.[ mk_usize 2 ] <: u64) >>! mk_i32 26 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 17)
      (cast ((limbs.[ mk_usize 2 ] <: u64) >>! mk_i32 34 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 18)
      (cast ((limbs.[ mk_usize 2 ] <: u64) >>! mk_i32 42 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 19)
      (cast (((limbs.[ mk_usize 2 ] <: u64) >>! mk_i32 50 <: u64) |.
            ((limbs.[ mk_usize 3 ] <: u64) <<! mk_i32 1 <: u64)
            <:
            u64)
        <:
        u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 20)
      (cast ((limbs.[ mk_usize 3 ] <: u64) >>! mk_i32 7 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 21)
      (cast ((limbs.[ mk_usize 3 ] <: u64) >>! mk_i32 15 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 22)
      (cast ((limbs.[ mk_usize 3 ] <: u64) >>! mk_i32 23 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 23)
      (cast ((limbs.[ mk_usize 3 ] <: u64) >>! mk_i32 31 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 24)
      (cast ((limbs.[ mk_usize 3 ] <: u64) >>! mk_i32 39 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 25)
      (cast (((limbs.[ mk_usize 3 ] <: u64) >>! mk_i32 47 <: u64) |.
            ((limbs.[ mk_usize 4 ] <: u64) <<! mk_i32 4 <: u64)
            <:
            u64)
        <:
        u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 26)
      (cast ((limbs.[ mk_usize 4 ] <: u64) >>! mk_i32 4 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 27)
      (cast ((limbs.[ mk_usize 4 ] <: u64) >>! mk_i32 12 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 28)
      (cast ((limbs.[ mk_usize 4 ] <: u64) >>! mk_i32 20 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 29)
      (cast ((limbs.[ mk_usize 4 ] <: u64) >>! mk_i32 28 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 30)
      (cast ((limbs.[ mk_usize 4 ] <: u64) >>! mk_i32 36 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 31)
      (cast ((limbs.[ mk_usize 4 ] <: u64) >>! mk_i32 44 <: u64) <: u8)
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert (((s.[ mk_usize 31 ] <: u8) &. mk_u8 128 <: u8) =. mk_u8 0 <: bool)
      in
      ()
  in
  s

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Subtle.t_ConstantTimeEq t_FieldElement =
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
        (impl_17__to_bytes self <: t_Slice u8)
        (impl_17__to_bytes other <: t_Slice u8)
  }

let impl_17__is_negative (self: t_FieldElement) : Subtle.t_Choice =
  let bytes:t_Array u8 (mk_usize 32) = impl_17__to_bytes self in
  Core_models.Convert.f_into #u8
    #Subtle.t_Choice
    #FStar.Tactics.Typeclasses.solve
    ((bytes.[ mk_usize 0 ] <: u8) &. mk_u8 1 <: u8)

let impl_17__is_zero (self: t_FieldElement) : Subtle.t_Choice =
  let zero:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let bytes:t_Array u8 (mk_usize 32) = impl_17__to_bytes self in
  Subtle.f_ct_eq #(t_Slice u8)
    #FStar.Tactics.Typeclasses.solve
    (bytes <: t_Slice u8)
    (zero <: t_Slice u8)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core_models.Ops.Arith.t_Add t_FieldElement t_FieldElement =
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
let impl_7: Core_models.Ops.Arith.t_Sub t_FieldElement t_FieldElement =
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
let impl_8: Core_models.Ops.Arith.t_Mul t_FieldElement t_FieldElement =
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

/// Raise this field element to the power (p-5)/8 = 2^252 - 3.
let impl_17__pow_p58 (self: t_FieldElement) : t_FieldElement =
  let acc:t_FieldElement = impl_17__ONE in
  let acc:t_FieldElement =
    Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(Core_models.Iter.Adapters.Rev.t_Rev
            (Core_models.Ops.Range.t_Range i32))
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Iter.Traits.Iterator.f_rev #(Core_models.Ops.Range.t_Range i32)
              #FStar.Tactics.Typeclasses.solve
              ({
                  Core_models.Ops.Range.f_start = mk_i32 0;
                  Core_models.Ops.Range.f_end = mk_i32 252
                }
                <:
                Core_models.Ops.Range.t_Range i32)
            <:
            Core_models.Iter.Adapters.Rev.t_Rev (Core_models.Ops.Range.t_Range i32))
        <:
        Core_models.Iter.Adapters.Rev.t_Rev (Core_models.Ops.Range.t_Range i32))
      acc
      (fun acc i ->
          let acc:t_FieldElement = acc in
          let i:i32 = i in
          let acc:t_FieldElement = impl_17__square acc in
          if i <>. mk_i32 1
          then
            let acc:t_FieldElement =
              Core_models.Ops.Arith.f_mul #t_FieldElement
                #t_FieldElement
                #FStar.Tactics.Typeclasses.solve
                acc
                self
            in
            acc
          else acc)
  in
  acc

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core_models.Ops.Arith.t_Neg t_FieldElement =
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
        (Curve25519_dalek.Traits.f_identity #t_FieldElement #FStar.Tactics.Typeclasses.solve ()
          <:
          t_FieldElement)
        self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core_models.Ops.Arith.t_Neg t_FieldElement =
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
let impl_17__sqrt_ratio_i (u v: t_FieldElement) : (Subtle.t_Choice & t_FieldElement) =
  let v3:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      (impl_17__square v <: t_FieldElement)
      v
  in
  let v7:t_FieldElement =
    Core_models.Ops.Arith.f_mul #t_FieldElement
      #t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      (impl_17__square v3 <: t_FieldElement)
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
      (impl_17__pow_p58 (Core_models.Ops.Arith.f_mul #t_FieldElement
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
      (impl_17__square r <: t_FieldElement)
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
    impl_17__conditional_assign r
      r_prime
      (Core_models.Ops.Bit.f_bitor #Subtle.t_Choice
          #Subtle.t_Choice
          #FStar.Tactics.Typeclasses.solve
          flipped_sign_sqrt
          flipped_sign_sqrt_i
        <:
        Subtle.t_Choice)
  in
  let r_is_negative:Subtle.t_Choice = impl_17__is_negative r in
  let r:t_FieldElement = impl_17__conditional_negate r r_is_negative in
  let was_nonzero_square:Subtle.t_Choice =
    Core_models.Ops.Bit.f_bitor #Subtle.t_Choice
      #Subtle.t_Choice
      #FStar.Tactics.Typeclasses.solve
      correct_sign_sqrt
      flipped_sign_sqrt
  in
  was_nonzero_square, r <: (Subtle.t_Choice & t_FieldElement)

/// Attempt to compute `sqrt(1/self)` in constant time.
/// Convenience wrapper around `sqrt_ratio_i`.
/// This function always returns the nonnegative square root.
/// # Return
/// - `(Choice(1), +sqrt(1/self))  ` if `self` is a nonzero square;
/// - `(Choice(0), zero)           ` if `self` is zero;
/// - `(Choice(0), +sqrt(i/self))  ` if `self` is a nonzero nonsquare;
let impl_17__invsqrt (self: t_FieldElement) : (Subtle.t_Choice & t_FieldElement) =
  impl_17__sqrt_ratio_i impl_17__ONE self
