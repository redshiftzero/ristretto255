module Ristretto255.Field
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Ristretto255.Traits in
  let open Subtle in
  ()

type t_FieldElement = | FieldElement : t_Array u64 (mk_usize 5) -> t_FieldElement

let impl_1: Core_models.Clone.t_Clone t_FieldElement =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core_models.Marker.t_Copy t_FieldElement

unfold
let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core_models.Fmt.t_Debug t_FieldElement

unfold
let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core_models.Marker.t_StructuralPartialEq t_FieldElement

unfold
let impl_4 = impl_4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core_models.Cmp.t_PartialEq t_FieldElement t_FieldElement

unfold
let impl_5 = impl_5'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': Core_models.Cmp.t_Eq t_FieldElement

unfold
let impl_6 = impl_6'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Ristretto255.Traits.t_Identity t_FieldElement =
  {
    f_identity_pre = (fun (_: Prims.unit) -> true);
    f_identity_post = (fun (_: Prims.unit) (out: t_FieldElement) -> true);
    f_identity
    =
    fun (_: Prims.unit) ->
      FieldElement (Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 5)) <: t_FieldElement
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core_models.Ops.Arith.t_Add t_FieldElement t_FieldElement =
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
let impl_9: Core_models.Ops.Arith.t_Sub t_FieldElement t_FieldElement =
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
let impl_10: Core_models.Ops.Arith.t_Mul t_FieldElement u64 =
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
let impl_11: Core_models.Ops.Arith.t_Mul t_FieldElement t_FieldElement =
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

let impl_FieldElement__ONE: t_FieldElement =
  FieldElement
  (let list = [mk_u64 1; mk_u64 0; mk_u64 0; mk_u64 0; mk_u64 0] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_FieldElement

/// Serialize this field element to canonical 32-byte encoding.
/// Adapted from the `curve25519-dalek` crate.
assume
val impl_FieldElement__to_bytes': self: t_FieldElement -> t_Array u8 (mk_usize 32)

unfold
let impl_FieldElement__to_bytes = impl_FieldElement__to_bytes'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Subtle.t_ConstantTimeEq t_FieldElement =
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
        (impl_FieldElement__to_bytes self <: t_Slice u8)
        (impl_FieldElement__to_bytes other <: t_Slice u8)
  }

assume
val impl_FieldElement__square': self: t_FieldElement -> t_FieldElement

unfold
let impl_FieldElement__square = impl_FieldElement__square'

assume
val impl_FieldElement__is_negative': self: t_FieldElement -> Subtle.t_Choice

unfold
let impl_FieldElement__is_negative = impl_FieldElement__is_negative'

assume
val impl_FieldElement__is_zero': self: t_FieldElement -> Subtle.t_Choice

unfold
let impl_FieldElement__is_zero = impl_FieldElement__is_zero'

assume
val impl_FieldElement__conditional_negate': self: t_FieldElement -> choice: Subtle.t_Choice
  -> t_FieldElement

unfold
let impl_FieldElement__conditional_negate = impl_FieldElement__conditional_negate'

assume
val impl_FieldElement__conditional_assign':
    self: t_FieldElement ->
    other: t_FieldElement ->
    choice: Subtle.t_Choice
  -> t_FieldElement

unfold
let impl_FieldElement__conditional_assign = impl_FieldElement__conditional_assign'

/// Attempt to compute `sqrt(1/self)` in constant time.
/// Convenience wrapper around `sqrt_ratio_i`.
/// This function always returns the nonnegative square root.
/// # Return
/// - `(Choice(1), +sqrt(1/self))  ` if `self` is a nonzero square;
/// - `(Choice(0), zero)           ` if `self` is zero;
/// - `(Choice(0), +sqrt(i/self))  ` if `self` is a nonzero nonsquare;
assume
val impl_FieldElement__invsqrt': self: t_FieldElement -> (Subtle.t_Choice & t_FieldElement)

unfold
let impl_FieldElement__invsqrt = impl_FieldElement__invsqrt'

/// Given `FieldElements` `u` and `v`, compute either `sqrt(u/v)`
/// or `sqrt(i*u/v)` in constant time.
/// This function always returns the nonnegative square root.
/// # Return
/// - `(Choice(1), +sqrt(u/v))  ` if `v` is nonzero and `u/v` is square;
/// - `(Choice(1), zero)        ` if `u` is zero;
/// - `(Choice(0), zero)        ` if `v` is zero and `u` is nonzero;
/// - `(Choice(0), +sqrt(i*u/v))` if `u/v` is nonsquare (so `i*u/v` is square).
assume
val impl_FieldElement__sqrt_ratio_i': u: t_FieldElement -> v: t_FieldElement
  -> (Subtle.t_Choice & t_FieldElement)

unfold
let impl_FieldElement__sqrt_ratio_i = impl_FieldElement__sqrt_ratio_i'

/// Raise this field element to the power (p-5)/8 = 2^252 - 3.
assume
val impl_FieldElement__pow_p58': self: t_FieldElement -> t_FieldElement

unfold
let impl_FieldElement__pow_p58 = impl_FieldElement__pow_p58'

let impl_FieldElement__load8_at (input: t_Array u8 (mk_usize 32)) (i: usize)
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
let impl_FieldElement__from_bytes (bytes: t_Array u8 (mk_usize 32)) : t_FieldElement =
  let low_51_bit_mask:u64 = v_LOW_51_BIT_MASK in
  FieldElement
  (let list =
      [
        (impl_FieldElement__load8_at bytes (mk_usize 0) <: u64) &. low_51_bit_mask;
        ((impl_FieldElement__load8_at bytes (mk_usize 6) <: u64) >>! mk_i32 3 <: u64) &.
        low_51_bit_mask;
        ((impl_FieldElement__load8_at bytes (mk_usize 12) <: u64) >>! mk_i32 6 <: u64) &.
        low_51_bit_mask;
        ((impl_FieldElement__load8_at bytes (mk_usize 19) <: u64) >>! mk_i32 1 <: u64) &.
        low_51_bit_mask;
        ((impl_FieldElement__load8_at bytes (mk_usize 24) <: u64) >>! mk_i32 12 <: u64) &.
        low_51_bit_mask
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_FieldElement

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core_models.Ops.Arith.t_Add t_FieldElement t_FieldElement =
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
let impl_14: Core_models.Ops.Arith.t_Sub t_FieldElement t_FieldElement =
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
let impl_15: Core_models.Ops.Arith.t_Mul t_FieldElement t_FieldElement =
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
let impl_16: Core_models.Ops.Arith.t_Neg t_FieldElement =
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
let impl_17: Core_models.Ops.Arith.t_Neg t_FieldElement =
  {
    f_Output = t_FieldElement;
    f_neg_pre = (fun (self: t_FieldElement) -> true);
    f_neg_post = (fun (self: t_FieldElement) (out: t_FieldElement) -> true);
    f_neg
    =
    fun (self: t_FieldElement) ->
      Core_models.Ops.Arith.f_neg #t_FieldElement #FStar.Tactics.Typeclasses.solve self
  }
