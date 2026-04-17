module Ristretto255.Scalar
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Rand_core in
  ()

/// A scalar value for the ristretto255 group.
/// Scalars are integers mod ℓ, where ℓ is the order of the ristretto255 group.
type t_Scalar = | Scalar : t_Array u8 (mk_usize 32) -> t_Scalar

let impl_1: Core_models.Clone.t_Clone t_Scalar =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core_models.Fmt.t_Debug t_Scalar

unfold
let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core_models.Marker.t_StructuralPartialEq t_Scalar

unfold
let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core_models.Cmp.t_PartialEq t_Scalar t_Scalar

unfold
let impl_4 = impl_4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core_models.Cmp.t_Eq t_Scalar

unfold
let impl_5 = impl_5'

/// Generate a random scalar using the provided RNG.
assume
val impl_Scalar__random':
    #v_R: Type0 ->
    {| i0: Rand_core.t_RngCore v_R |} ->
    {| i1: Rand_core.t_CryptoRng v_R |} ->
    e_rng: v_R
  -> (v_R & t_Scalar)

unfold
let impl_Scalar__random
      (#v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand_core.t_RngCore v_R)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng v_R)
     = impl_Scalar__random' #v_R #i0 #i1

/// Attempt to construct a scalar from a canonical byte representation.
/// Returns `None` if the bytes do not represent a canonical scalar
/// (i.e. the value is >= ℓ).
assume
val impl_Scalar__from_bytes_checked': e_bytes: t_Array u8 (mk_usize 32)
  -> Core_models.Option.t_Option t_Scalar

unfold
let impl_Scalar__from_bytes_checked = impl_Scalar__from_bytes_checked'

/// Construct a scalar by reducing a 256-bit little-endian integer modulo ℓ.
/// Unlike [`from_bytes_checked`](Self::from_bytes_checked), this always
/// succeeds by reducing the input mod the group order.
assume
val impl_Scalar__from_bytes_mod_order': e_bytes: t_Array u8 (mk_usize 32) -> t_Scalar

unfold
let impl_Scalar__from_bytes_mod_order = impl_Scalar__from_bytes_mod_order'

/// Serialize this scalar to a 32-byte little-endian array.
let impl_Scalar__to_bytes (self: t_Scalar) : t_Array u8 (mk_usize 32) = self._0
