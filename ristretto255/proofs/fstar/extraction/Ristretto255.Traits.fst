module Ristretto255.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Trait for getting the identity element of a point type.
class t_Identity (v_Self: Type0) = {
  f_identity_pre:Prims.unit -> Type0;
  f_identity_post:Prims.unit -> v_Self -> Type0;
  f_identity:x0: Prims.unit
    -> Prims.Pure v_Self (f_identity_pre x0) (fun result -> f_identity_post x0 result)
}
