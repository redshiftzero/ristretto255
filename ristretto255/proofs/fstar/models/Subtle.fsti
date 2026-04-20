module Subtle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// Models `subtle::Choice` — a byte (0 or 1) used in constant-time code.
type t_Choice = | Choice : u8 -> t_Choice

/// Extract the inner u8 value.
let impl_Choice__unwrap_u8 (self: t_Choice) : u8 = self._0

/// Typeclass for constant-time equality comparison.
/// Models `subtle::ConstantTimeEq`.
class t_ConstantTimeEq (v_Self: Type0) = {
  f_ct_eq_pre  : v_Self -> v_Self -> Type0;
  f_ct_eq_post : v_Self -> v_Self -> t_Choice -> Type0;
  f_ct_eq : x0:v_Self -> x1:v_Self
    -> Prims.Pure t_Choice (f_ct_eq_pre x0 x1) (fun result -> f_ct_eq_post x0 x1 result)
}

/// Constant-time equality for byte slices.
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_ct_eq_slice_u8 : t_ConstantTimeEq (t_Slice u8) = {
  f_ct_eq_pre  = (fun _ _ -> True);
  f_ct_eq_post = (fun _ _ _ -> True);
  f_ct_eq = magic ()
}

/// Constant-time equality for u8.
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_ct_eq_u8 : t_ConstantTimeEq u8 = {
  f_ct_eq_pre  = (fun _ _ -> True);
  f_ct_eq_post = (fun _ _ _ -> True);
  f_ct_eq = fun (a: u8) (b: u8) -> Choice (if a = b then mk_u8 1 else mk_u8 0)
}

/// `From<u8>` for `Choice`.
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_from_u8 : Core_models.Convert.t_From t_Choice u8 =
  {
    f_from_pre  = (fun (_: u8) -> true);
    f_from_post = (fun (_: u8) (_: t_Choice) -> true);
    f_from      = fun (x: u8) -> Choice x
  }

/// `Not` for `Choice` (bitwise NOT of the underlying byte, then mask to 1 bit).
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_not_choice : Rust_primitives.Notations.negation_tc t_Choice = {
  Rust_primitives.Notations.op_Tilde_Dot = fun (x: t_Choice) -> Choice (mk_u8 1 -. x._0)
}

/// `Into<bool>` for `Choice` (nonzero = true).
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_into_bool : Core_models.Convert.t_Into t_Choice bool =
  {
    f_into_pre  = (fun (_: t_Choice) -> true);
    f_into_post = (fun (_: t_Choice) (_: bool) -> true);
    f_into      = fun (x: t_Choice) -> x._0 <> mk_u8 0
  }

/// `BitOr` instance for `Choice` (bitwise OR of the underlying bytes).
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_bitor_choice : Core_models.Ops.Bit.t_BitOr t_Choice t_Choice =
  {
    f_Output      = t_Choice;
    f_bitor_pre   = (fun (_: t_Choice) (_: t_Choice) -> true);
    f_bitor_post  = (fun (_: t_Choice) (_: t_Choice) (_: t_Choice) -> true);
    f_bitor       = fun (x: t_Choice) (y: t_Choice) -> Choice (x._0 |. y._0)
  }

/// `BitAnd` instance for `Choice` (bitwise AND of the underlying bytes).
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_bitand_choice : Core_models.Ops.Bit.t_BitAnd t_Choice t_Choice =
  {
    f_Output      = t_Choice;
    f_bitand_pre  = (fun (_: t_Choice) (_: t_Choice) -> true);
    f_bitand_post = (fun (_: t_Choice) (_: t_Choice) (_: t_Choice) -> true);
    f_bitand      = fun (x: t_Choice) (y: t_Choice) -> Choice (x._0 &. y._0)
  }

/// Typeclass for constant-time selection between two values.
/// Models `subtle::ConditionallySelectable`.
class t_ConditionallySelectable (v_Self: Type0) = {
  f_conditional_select_pre  : v_Self -> v_Self -> t_Choice -> Type0;
  f_conditional_select_post : v_Self -> v_Self -> t_Choice -> v_Self -> Type0;
  f_conditional_select : x0:v_Self -> x1:v_Self -> x2:t_Choice
    -> Prims.Pure v_Self
        (f_conditional_select_pre x0 x1 x2)
        (fun result -> f_conditional_select_post x0 x1 x2 result)
}

/// `ConditionallySelectable` for `u64`: return `b` if `choice.0 != 0`, else `a`.
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_conditional_select_u64 : t_ConditionallySelectable u64 =
  {
    f_conditional_select_pre  = (fun _ _ _ -> True);
    f_conditional_select_post = (fun _ _ _ _ -> True);
    f_conditional_select      =
      fun (a: u64) (b: u64) (choice: t_Choice) ->
        if choice._0 <> mk_u8 0 then b else a
  }
