module Ristretto255
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// A Ristretto encoding.
type t_CompressedRistretto =
  | CompressedRistretto : t_Array u8 (mk_usize 32) -> t_CompressedRistretto

let impl_1: Core_models.Clone.t_Clone t_CompressedRistretto =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core_models.Marker.t_Copy t_CompressedRistretto

unfold
let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core_models.Marker.t_StructuralPartialEq t_CompressedRistretto

unfold
let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core_models.Cmp.t_PartialEq t_CompressedRistretto t_CompressedRistretto

unfold
let impl_4 = impl_4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core_models.Cmp.t_Eq t_CompressedRistretto

unfold
let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core_models.Hash.t_Hash t_CompressedRistretto

unfold
let impl_5 = impl_5'
