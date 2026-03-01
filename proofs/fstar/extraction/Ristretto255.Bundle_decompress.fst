module Ristretto255.Bundle_decompress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Curve25519_dalek.Traits in
  let open Ristretto255.Field in
  let open Subtle in
  ()

/// A compressed Ristretto255 point.
type t_CompressedRistretto =
  | CompressedRistretto : t_Array u8 (mk_usize 32) -> t_CompressedRistretto

let impl_6: Core_models.Clone.t_Clone t_CompressedRistretto =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core_models.Marker.t_Copy t_CompressedRistretto

unfold
let impl_5 = impl_5'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_8': Core_models.Hash.t_Hash t_CompressedRistretto

unfold
let impl_8 = impl_8'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core_models.Cmp.t_PartialEq t_CompressedRistretto t_CompressedRistretto =
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
val impl_7': Core_models.Cmp.t_Eq t_CompressedRistretto

unfold
let impl_7 = impl_7'

/// Copy the bytes of this `CompressedRistretto`.
let impl_9__to_bytes (self: t_CompressedRistretto) : t_Array u8 (mk_usize 32) = self._0

/// View this `CompressedRistretto` as an array of bytes.
let impl_9__as_bytes (self: t_CompressedRistretto) : t_Array u8 (mk_usize 32) = self._0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Subtle.t_ConstantTimeEq t_CompressedRistretto =
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
        (impl_9__as_bytes self <: t_Slice u8)
        (impl_9__as_bytes other <: t_Slice u8)
  }

/// Construct a `CompressedRistretto` from a slice of bytes.
/// # Errors
/// Returns [`TryFromSliceError`] if the input `bytes` slice does not have
/// a length of 32.
let impl_9__from_slice (bytes: t_Slice u8)
    : Prims.Pure
      (Core_models.Result.t_Result t_CompressedRistretto Core_models.Array.t_TryFromSliceError)
      (requires (Core_models.Slice.impl__len #u8 bytes <: usize) =. mk_usize 32)
      (ensures
        fun r ->
          let r:Core_models.Result.t_Result t_CompressedRistretto
            Core_models.Array.t_TryFromSliceError =
            r
          in
          Core_models.Result.impl__is_ok #t_CompressedRistretto
            #Core_models.Array.t_TryFromSliceError
            r) =
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
let impl_2: Curve25519_dalek.Traits.t_Identity t_CompressedRistretto =
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
let impl_3: Core_models.Default.t_Default t_CompressedRistretto =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_CompressedRistretto) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      Curve25519_dalek.Traits.f_identity #t_CompressedRistretto #FStar.Tactics.Typeclasses.solve ()
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core_models.Convert.t_TryFrom t_CompressedRistretto (t_Slice u8) =
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
    f_try_from = fun (slice: t_Slice u8) -> impl_9__from_slice slice
  }

type t_EdwardsPoint = {
  f_X:Ristretto255.Field.t_FieldElement;
  f_Y:Ristretto255.Field.t_FieldElement;
  f_Z:Ristretto255.Field.t_FieldElement;
  f_T:Ristretto255.Field.t_FieldElement
}

type t_RistrettoPoint = | RistrettoPoint : t_EdwardsPoint -> t_RistrettoPoint

let step_1_ (repr: t_CompressedRistretto)
    : (Subtle.t_Choice & Subtle.t_Choice & Ristretto255.Field.t_FieldElement) =
  let s:Ristretto255.Field.t_FieldElement =
    Ristretto255.Field.impl_FieldElement__from_bytes (impl_9__as_bytes repr
        <:
        t_Array u8 (mk_usize 32))
  in
  let s_bytes_check:t_Array u8 (mk_usize 32) = Ristretto255.Field.impl_FieldElement__to_bytes s in
  let s_encoding_is_canonical:Subtle.t_Choice =
    Subtle.f_ct_eq #(t_Slice u8)
      #FStar.Tactics.Typeclasses.solve
      (s_bytes_check.[ Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull ]
        <:
        t_Slice u8)
      (impl_9__as_bytes repr <: t_Slice u8)
  in
  let s_is_negative:Subtle.t_Choice = Ristretto255.Field.impl_FieldElement__is_negative s in
  s_encoding_is_canonical, s_is_negative, s
  <:
  (Subtle.t_Choice & Subtle.t_Choice & Ristretto255.Field.t_FieldElement)

let step_2_ (s: Ristretto255.Field.t_FieldElement)
    : (Subtle.t_Choice & Subtle.t_Choice & Subtle.t_Choice & t_RistrettoPoint) =
  let one:Ristretto255.Field.t_FieldElement = Ristretto255.Field.impl_FieldElement__ONE in
  let ss:Ristretto255.Field.t_FieldElement = Ristretto255.Field.impl_FieldElement__square s in
  let u1:Ristretto255.Field.t_FieldElement =
    Core_models.Ops.Arith.f_sub #Ristretto255.Field.t_FieldElement
      #Ristretto255.Field.t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      one
      ss
  in
  let u2:Ristretto255.Field.t_FieldElement =
    Core_models.Ops.Arith.f_add #Ristretto255.Field.t_FieldElement
      #Ristretto255.Field.t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      one
      ss
  in
  let u2_sqr:Ristretto255.Field.t_FieldElement = Ristretto255.Field.impl_FieldElement__square u2 in
  let v:Ristretto255.Field.t_FieldElement =
    Core_models.Ops.Arith.f_sub #Ristretto255.Field.t_FieldElement
      #Ristretto255.Field.t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_mul #Ristretto255.Field.t_FieldElement
          #Ristretto255.Field.t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Ops.Arith.f_neg #Ristretto255.Field.t_FieldElement
              #FStar.Tactics.Typeclasses.solve
              Ristretto255.Constants.v_EDWARDS_D
            <:
            Ristretto255.Field.t_FieldElement)
          (Ristretto255.Field.impl_FieldElement__square u1 <: Ristretto255.Field.t_FieldElement)
        <:
        Ristretto255.Field.t_FieldElement)
      u2_sqr
  in
  let (ok: Subtle.t_Choice), (v_I: Ristretto255.Field.t_FieldElement) =
    Ristretto255.Field.impl_FieldElement__invsqrt (Core_models.Ops.Arith.f_mul #Ristretto255.Field.t_FieldElement
          #Ristretto255.Field.t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          v
          u2_sqr
        <:
        Ristretto255.Field.t_FieldElement)
  in
  let v_Dx:Ristretto255.Field.t_FieldElement =
    Core_models.Ops.Arith.f_mul #Ristretto255.Field.t_FieldElement
      #Ristretto255.Field.t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      v_I
      u2
  in
  let v_Dy:Ristretto255.Field.t_FieldElement =
    Core_models.Ops.Arith.f_mul #Ristretto255.Field.t_FieldElement
      #Ristretto255.Field.t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      v_I
      (Core_models.Ops.Arith.f_mul #Ristretto255.Field.t_FieldElement
          #Ristretto255.Field.t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          v_Dx
          v
        <:
        Ristretto255.Field.t_FieldElement)
  in
  let x:Ristretto255.Field.t_FieldElement =
    Core_models.Ops.Arith.f_mul #Ristretto255.Field.t_FieldElement
      #Ristretto255.Field.t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Arith.f_add #Ristretto255.Field.t_FieldElement
          #Ristretto255.Field.t_FieldElement
          #FStar.Tactics.Typeclasses.solve
          s
          s
        <:
        Ristretto255.Field.t_FieldElement)
      v_Dx
  in
  let x_neg:Subtle.t_Choice = Ristretto255.Field.impl_FieldElement__is_negative x in
  let x:Ristretto255.Field.t_FieldElement =
    Ristretto255.Field.impl_FieldElement__conditional_negate x x_neg
  in
  let y:Ristretto255.Field.t_FieldElement =
    Core_models.Ops.Arith.f_mul #Ristretto255.Field.t_FieldElement
      #Ristretto255.Field.t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      u1
      v_Dy
  in
  let t:Ristretto255.Field.t_FieldElement =
    Core_models.Ops.Arith.f_mul #Ristretto255.Field.t_FieldElement
      #Ristretto255.Field.t_FieldElement
      #FStar.Tactics.Typeclasses.solve
      x
      y
  in
  ok,
  Ristretto255.Field.impl_FieldElement__is_negative t,
  Ristretto255.Field.impl_FieldElement__is_zero y,
  (RistrettoPoint ({ f_X = x; f_Y = y; f_Z = one; f_T = t } <: t_EdwardsPoint) <: t_RistrettoPoint)
  <:
  (Subtle.t_Choice & Subtle.t_Choice & Subtle.t_Choice & t_RistrettoPoint)

/// Attempt to decompress to an `RistrettoPoint`.
/// # Return
/// - `Some(RistrettoPoint)` if `self` was the canonical encoding of a point;
/// - `None` if `self` was not the canonical encoding of a point.
let impl_9__decompress (self: t_CompressedRistretto) : Core_models.Option.t_Option t_RistrettoPoint =
  let
  (s_encoding_is_canonical: Subtle.t_Choice),
  (s_is_negative: Subtle.t_Choice),
  (s: Ristretto255.Field.t_FieldElement) =
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
