module Ristretto255.Scalar
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Rand_core in
  let open Subtle in
  ()

/// A scalar value for the ristretto255 group.
/// Scalars are integers mod ℓ, where ℓ is the order of the ristretto255 group.
type t_Scalar = | Scalar : t_Array u8 (mk_usize 32) -> t_Scalar

let impl_2: Core_models.Clone.t_Clone t_Scalar =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core_models.Fmt.t_Debug t_Scalar

unfold
let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core_models.Marker.t_StructuralPartialEq t_Scalar

unfold
let impl_4 = impl_4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core_models.Cmp.t_PartialEq t_Scalar t_Scalar

unfold
let impl_5 = impl_5'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': Core_models.Cmp.t_Eq t_Scalar

unfold
let impl_6 = impl_6'

/// Generate a random scalar using the provided RNG.
assume
val impl_Scalar__random':
    #v_R: Type0 ->
    {| i0: Rand_core.t_RngCore v_R |} ->
    {| i1: Rand_core.t_CryptoRng v_R |} ->
    rng: v_R
  -> (v_R & t_Scalar)

unfold
let impl_Scalar__random
      (#v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand_core.t_RngCore v_R)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng v_R)
     = impl_Scalar__random' #v_R #i0 #i1

/// Serialize this scalar to a 32-byte little-endian array.
let impl_Scalar__to_bytes (self: t_Scalar) : t_Array u8 (mk_usize 32) = self._0

/// `Scalar52` represents an element of ℤ/ℓℤ as 5 × 52-bit limbs.
type t_Scalar52 = | Scalar52 : t_Array u64 (mk_usize 5) -> t_Scalar52

let impl_8: Core_models.Clone.t_Clone t_Scalar52 =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core_models.Marker.t_Copy t_Scalar52

unfold
let impl_7 = impl_7'

/// u64 × u64 → u128 multiply helper.
let m (x y: u64) : u128 = (cast (x <: u64) <: u128) *! (cast (y <: u64) <: u128)

let impl_Scalar52__ZERO: t_Scalar52 =
  Scalar52
  (let list = [mk_u64 0; mk_u64 0; mk_u64 0; mk_u64 0; mk_u64 0] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_Scalar52

assume
val impl_Scalar52__from_bytes': bytes: t_Array u8 (mk_usize 32) -> t_Scalar52

unfold
let impl_Scalar52__from_bytes = impl_Scalar52__from_bytes'

assume
val impl_Scalar52__from_bytes_wide': bytes: t_Array u8 (mk_usize 64) -> t_Scalar52

unfold
let impl_Scalar52__from_bytes_wide = impl_Scalar52__from_bytes_wide'

assume
val impl_Scalar52__to_bytes': self: t_Scalar52 -> t_Array u8 (mk_usize 32)

unfold
let impl_Scalar52__to_bytes = impl_Scalar52__to_bytes'

/// Construct a scalar by reducing a 512-bit little-endian integer modulo ℓ.
let impl_Scalar__from_bytes_mod_order_wide (bytes: t_Array u8 (mk_usize 64)) : t_Scalar =
  Scalar (impl_Scalar52__to_bytes (impl_Scalar52__from_bytes_wide bytes <: t_Scalar52)) <: t_Scalar

assume
val impl_Scalar52__add': a: t_Scalar52 -> b: t_Scalar52 -> t_Scalar52

unfold
let impl_Scalar52__add = impl_Scalar52__add'

assume
val impl_Scalar52__sub': a: t_Scalar52 -> b: t_Scalar52 -> t_Scalar52

unfold
let impl_Scalar52__sub = impl_Scalar52__sub'

assume
val impl_Scalar52__mul_internal': a: t_Scalar52 -> b: t_Scalar52 -> t_Array u128 (mk_usize 9)

unfold
let impl_Scalar52__mul_internal = impl_Scalar52__mul_internal'

assume
val impl_Scalar52__montgomery_reduce': limbs: t_Array u128 (mk_usize 9) -> t_Scalar52

unfold
let impl_Scalar52__montgomery_reduce = impl_Scalar52__montgomery_reduce'

assume
val impl_Scalar52__montgomery_mul': a: t_Scalar52 -> b: t_Scalar52 -> t_Scalar52

unfold
let impl_Scalar52__montgomery_mul = impl_Scalar52__montgomery_mul'

assume
val impl_Scalar52__montgomery_reduce__part1': sum: u128 -> (u128 & u64)

unfold
let impl_Scalar52__montgomery_reduce__part1 = impl_Scalar52__montgomery_reduce__part1'

assume
val impl_Scalar52__montgomery_reduce__part2': sum: u128 -> (u128 & u64)

unfold
let impl_Scalar52__montgomery_reduce__part2 = impl_Scalar52__montgomery_reduce__part2'

/// `L` is the group order ℓ = 2^252 + 27742317777372353535851937790883648493.
let v_L: t_Scalar52 =
  Scalar52
  (let list =
      [
        mk_u64 671914833335277;
        mk_u64 3916664325105025;
        mk_u64 1367801;
        mk_u64 0;
        mk_u64 17592186044416
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_Scalar52

/// `L * LFACTOR ≡ -1  (mod 2^52)`.
let v_LFACTOR: u64 = mk_u64 1439961107955227

/// `R = 2^260 mod ℓ`, the Montgomery modulus.
let v_R: t_Scalar52 =
  Scalar52
  (let list =
      [
        mk_u64 4302102966953709;
        mk_u64 1049714374468698;
        mk_u64 4503599278581019;
        mk_u64 4503599627370495;
        mk_u64 17592186044415
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_Scalar52

/// Reduce this scalar mod ℓ, returning the canonical representative.
let impl_Scalar__reduce (self: t_Scalar) : t_Scalar =
  let x:t_Scalar52 = impl_Scalar52__from_bytes self._0 in
  let xR:t_Array u128 (mk_usize 9) = impl_Scalar52__mul_internal x v_R in
  let x_mod_l:t_Scalar52 = impl_Scalar52__montgomery_reduce xR in
  Scalar (impl_Scalar52__to_bytes x_mod_l) <: t_Scalar

/// Construct a scalar by reducing a 256-bit little-endian integer modulo ℓ.
/// Unlike [`from_bytes_checked`](Self::from_bytes_checked), this always
/// succeeds by reducing the input mod the group order.
let impl_Scalar__from_bytes_mod_order (bytes: t_Array u8 (mk_usize 32)) : t_Scalar =
  impl_Scalar__reduce (Scalar bytes <: t_Scalar)

let impl_Scalar__is_canonical (self: t_Scalar) : Subtle.t_Choice =
  Subtle.f_ct_eq #(t_Slice u8)
    #FStar.Tactics.Typeclasses.solve
    (self._0 <: t_Slice u8)
    ((impl_Scalar__reduce self)._0 <: t_Slice u8)

/// Attempt to construct a scalar from a canonical byte representation.
/// Returns `None` if the bytes do not represent a canonical scalar
/// (i.e. the value is >= ℓ).
let impl_Scalar__from_bytes_checked (bytes: t_Array u8 (mk_usize 32))
    : Core_models.Option.t_Option t_Scalar =
  let candidate:t_Scalar = Scalar bytes <: t_Scalar in
  let high_bit_unset:Subtle.t_Choice =
    Subtle.f_ct_eq #u8
      #FStar.Tactics.Typeclasses.solve
      ((bytes.[ mk_usize 31 ] <: u8) >>! mk_i32 7 <: u8)
      (mk_u8 0)
  in
  let is_canonical:Subtle.t_Choice = impl_Scalar__is_canonical candidate in
  if
    Core_models.Convert.f_into #Subtle.t_Choice
      #bool
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Ops.Bit.f_bitand #Subtle.t_Choice
          #Subtle.t_Choice
          #FStar.Tactics.Typeclasses.solve
          high_bit_unset
          is_canonical
        <:
        Subtle.t_Choice)
  then Core_models.Option.Option_Some candidate <: Core_models.Option.t_Option t_Scalar
  else Core_models.Option.Option_None <: Core_models.Option.t_Option t_Scalar

/// `RR = R^2 mod ℓ`.
let v_RR: t_Scalar52 =
  Scalar52
  (let list =
      [
        mk_u64 2764609938444603;
        mk_u64 3768881411696287;
        mk_u64 1616719297148420;
        mk_u64 1087343033131391;
        mk_u64 10175238647962
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_Scalar52
