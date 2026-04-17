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

let impl_Scalar52__from_bytes (bytes: t_Array u8 (mk_usize 32)) : t_Scalar52 =
  let words:t_Array u64 (mk_usize 4) = Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 4) in
  let words:t_Array u64 (mk_usize 4) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 4)
      (fun words temp_1_ ->
          let words:t_Array u64 (mk_usize 4) = words in
          let _:usize = temp_1_ in
          true)
      words
      (fun words i ->
          let words:t_Array u64 (mk_usize 4) = words in
          let i:usize = i in
          Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
            (mk_usize 8)
            (fun words temp_1_ ->
                let words:t_Array u64 (mk_usize 4) = words in
                let _:usize = temp_1_ in
                true)
            words
            (fun words j ->
                let words:t_Array u64 (mk_usize 4) = words in
                let j:usize = j in
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize words
                  i
                  ((words.[ i ] <: u64) |.
                    ((cast (bytes.[ (i *! mk_usize 8 <: usize) +! j <: usize ] <: u8) <: u64) <<!
                      (j *! mk_usize 8 <: usize)
                      <:
                      u64)
                    <:
                    u64)
                <:
                t_Array u64 (mk_usize 4))
          <:
          t_Array u64 (mk_usize 4))
  in
  let mask:u64 = (mk_u64 1 <<! mk_i32 52 <: u64) -! mk_u64 1 in
  let top_mask:u64 = (mk_u64 1 <<! mk_i32 48 <: u64) -! mk_u64 1 in
  Scalar52
  (let list =
      [
        (words.[ mk_usize 0 ] <: u64) &. mask;
        (((words.[ mk_usize 0 ] <: u64) >>! mk_i32 52 <: u64) |.
          ((words.[ mk_usize 1 ] <: u64) <<! mk_i32 12 <: u64)
          <:
          u64) &.
        mask;
        (((words.[ mk_usize 1 ] <: u64) >>! mk_i32 40 <: u64) |.
          ((words.[ mk_usize 2 ] <: u64) <<! mk_i32 24 <: u64)
          <:
          u64) &.
        mask;
        (((words.[ mk_usize 2 ] <: u64) >>! mk_i32 28 <: u64) |.
          ((words.[ mk_usize 3 ] <: u64) <<! mk_i32 36 <: u64)
          <:
          u64) &.
        mask;
        ((words.[ mk_usize 3 ] <: u64) >>! mk_i32 16 <: u64) &. top_mask
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list)
  <:
  t_Scalar52

let impl_Scalar52__to_bytes (self: t_Scalar52) : t_Array u8 (mk_usize 32) =
  let s:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 0)
      (cast ((self._0.[ mk_usize 0 ] <: u64) >>! mk_i32 0 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 1)
      (cast ((self._0.[ mk_usize 0 ] <: u64) >>! mk_i32 8 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 2)
      (cast ((self._0.[ mk_usize 0 ] <: u64) >>! mk_i32 16 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 3)
      (cast ((self._0.[ mk_usize 0 ] <: u64) >>! mk_i32 24 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 4)
      (cast ((self._0.[ mk_usize 0 ] <: u64) >>! mk_i32 32 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 5)
      (cast ((self._0.[ mk_usize 0 ] <: u64) >>! mk_i32 40 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 6)
      (cast (((self._0.[ mk_usize 0 ] <: u64) >>! mk_i32 48 <: u64) |.
            ((self._0.[ mk_usize 1 ] <: u64) <<! mk_i32 4 <: u64)
            <:
            u64)
        <:
        u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 7)
      (cast ((self._0.[ mk_usize 1 ] <: u64) >>! mk_i32 4 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 8)
      (cast ((self._0.[ mk_usize 1 ] <: u64) >>! mk_i32 12 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 9)
      (cast ((self._0.[ mk_usize 1 ] <: u64) >>! mk_i32 20 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 10)
      (cast ((self._0.[ mk_usize 1 ] <: u64) >>! mk_i32 28 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 11)
      (cast ((self._0.[ mk_usize 1 ] <: u64) >>! mk_i32 36 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 12)
      (cast ((self._0.[ mk_usize 1 ] <: u64) >>! mk_i32 44 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 13)
      (cast ((self._0.[ mk_usize 2 ] <: u64) >>! mk_i32 0 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 14)
      (cast ((self._0.[ mk_usize 2 ] <: u64) >>! mk_i32 8 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 15)
      (cast ((self._0.[ mk_usize 2 ] <: u64) >>! mk_i32 16 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 16)
      (cast ((self._0.[ mk_usize 2 ] <: u64) >>! mk_i32 24 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 17)
      (cast ((self._0.[ mk_usize 2 ] <: u64) >>! mk_i32 32 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 18)
      (cast ((self._0.[ mk_usize 2 ] <: u64) >>! mk_i32 40 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 19)
      (cast (((self._0.[ mk_usize 2 ] <: u64) >>! mk_i32 48 <: u64) |.
            ((self._0.[ mk_usize 3 ] <: u64) <<! mk_i32 4 <: u64)
            <:
            u64)
        <:
        u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 20)
      (cast ((self._0.[ mk_usize 3 ] <: u64) >>! mk_i32 4 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 21)
      (cast ((self._0.[ mk_usize 3 ] <: u64) >>! mk_i32 12 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 22)
      (cast ((self._0.[ mk_usize 3 ] <: u64) >>! mk_i32 20 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 23)
      (cast ((self._0.[ mk_usize 3 ] <: u64) >>! mk_i32 28 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 24)
      (cast ((self._0.[ mk_usize 3 ] <: u64) >>! mk_i32 36 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 25)
      (cast ((self._0.[ mk_usize 3 ] <: u64) >>! mk_i32 44 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 26)
      (cast ((self._0.[ mk_usize 4 ] <: u64) >>! mk_i32 0 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 27)
      (cast ((self._0.[ mk_usize 4 ] <: u64) >>! mk_i32 8 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 28)
      (cast ((self._0.[ mk_usize 4 ] <: u64) >>! mk_i32 16 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 29)
      (cast ((self._0.[ mk_usize 4 ] <: u64) >>! mk_i32 24 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 30)
      (cast ((self._0.[ mk_usize 4 ] <: u64) >>! mk_i32 32 <: u64) <: u8)
  in
  let s:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      (mk_usize 31)
      (cast ((self._0.[ mk_usize 4 ] <: u64) >>! mk_i32 40 <: u64) <: u8)
  in
  s

let impl_Scalar52__mul_internal (a b: t_Scalar52) : t_Array u128 (mk_usize 9) =
  let a:t_Array u64 (mk_usize 5) = a._0 in
  let b:t_Array u64 (mk_usize 5) = b._0 in
  let list =
    [
      m (a.[ mk_usize 0 ] <: u64) (b.[ mk_usize 0 ] <: u64);
      (m (a.[ mk_usize 0 ] <: u64) (b.[ mk_usize 1 ] <: u64) <: u128) +!
      (m (a.[ mk_usize 1 ] <: u64) (b.[ mk_usize 0 ] <: u64) <: u128);
      ((m (a.[ mk_usize 0 ] <: u64) (b.[ mk_usize 2 ] <: u64) <: u128) +!
        (m (a.[ mk_usize 1 ] <: u64) (b.[ mk_usize 1 ] <: u64) <: u128)
        <:
        u128) +!
      (m (a.[ mk_usize 2 ] <: u64) (b.[ mk_usize 0 ] <: u64) <: u128);
      (((m (a.[ mk_usize 0 ] <: u64) (b.[ mk_usize 3 ] <: u64) <: u128) +!
          (m (a.[ mk_usize 1 ] <: u64) (b.[ mk_usize 2 ] <: u64) <: u128)
          <:
          u128) +!
        (m (a.[ mk_usize 2 ] <: u64) (b.[ mk_usize 1 ] <: u64) <: u128)
        <:
        u128) +!
      (m (a.[ mk_usize 3 ] <: u64) (b.[ mk_usize 0 ] <: u64) <: u128);
      ((((m (a.[ mk_usize 0 ] <: u64) (b.[ mk_usize 4 ] <: u64) <: u128) +!
            (m (a.[ mk_usize 1 ] <: u64) (b.[ mk_usize 3 ] <: u64) <: u128)
            <:
            u128) +!
          (m (a.[ mk_usize 2 ] <: u64) (b.[ mk_usize 2 ] <: u64) <: u128)
          <:
          u128) +!
        (m (a.[ mk_usize 3 ] <: u64) (b.[ mk_usize 1 ] <: u64) <: u128)
        <:
        u128) +!
      (m (a.[ mk_usize 4 ] <: u64) (b.[ mk_usize 0 ] <: u64) <: u128);
      (((m (a.[ mk_usize 1 ] <: u64) (b.[ mk_usize 4 ] <: u64) <: u128) +!
          (m (a.[ mk_usize 2 ] <: u64) (b.[ mk_usize 3 ] <: u64) <: u128)
          <:
          u128) +!
        (m (a.[ mk_usize 3 ] <: u64) (b.[ mk_usize 2 ] <: u64) <: u128)
        <:
        u128) +!
      (m (a.[ mk_usize 4 ] <: u64) (b.[ mk_usize 1 ] <: u64) <: u128);
      ((m (a.[ mk_usize 2 ] <: u64) (b.[ mk_usize 4 ] <: u64) <: u128) +!
        (m (a.[ mk_usize 3 ] <: u64) (b.[ mk_usize 3 ] <: u64) <: u128)
        <:
        u128) +!
      (m (a.[ mk_usize 4 ] <: u64) (b.[ mk_usize 2 ] <: u64) <: u128);
      (m (a.[ mk_usize 3 ] <: u64) (b.[ mk_usize 4 ] <: u64) <: u128) +!
      (m (a.[ mk_usize 4 ] <: u64) (b.[ mk_usize 3 ] <: u64) <: u128);
      m (a.[ mk_usize 4 ] <: u64) (b.[ mk_usize 4 ] <: u64)
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 9);
  Rust_primitives.Hax.array_of_list 9 list

let impl_Scalar52__montgomery_reduce__part2 (sum: u128) : (u128 & u64) =
  let w:u64 = (cast (sum <: u128) <: u64) &. ((mk_u64 1 <<! mk_i32 52 <: u64) -! mk_u64 1 <: u64) in
  sum >>! mk_i32 52, w <: (u128 & u64)

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

let impl_Scalar52__sub (a b: t_Scalar52) : t_Scalar52 =
  let difference:t_Scalar52 = impl_Scalar52__ZERO in
  let mask:u64 = (mk_u64 1 <<! mk_i32 52 <: u64) -! mk_u64 1 in
  let (borrow: u64):u64 = mk_u64 0 in
  let (borrow: u64), (difference: t_Scalar52) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 5)
      (fun temp_0_ temp_1_ ->
          let (borrow: u64), (difference: t_Scalar52) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (borrow, difference <: (u64 & t_Scalar52))
      (fun temp_0_ i ->
          let (borrow: u64), (difference: t_Scalar52) = temp_0_ in
          let i:usize = i in
          let borrow:u64 =
            Core_models.Num.impl_u64__wrapping_sub (a._0.[ i ] <: u64)
              ((b._0.[ i ] <: u64) +! (borrow >>! mk_i32 63 <: u64) <: u64)
          in
          let difference:t_Scalar52 =
            {
              difference with
              _0
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize difference._0
                i
                (borrow &. mask <: u64)
            }
            <:
            t_Scalar52
          in
          borrow, difference <: (u64 & t_Scalar52))
  in
  let underflow:Subtle.t_Choice =
    Core_models.Convert.f_from #Subtle.t_Choice
      #u8
      #FStar.Tactics.Typeclasses.solve
      (cast (borrow >>! mk_i32 63 <: u64) <: u8)
  in
  let (carry: u64):u64 = mk_u64 0 in
  let (carry: u64), (difference: t_Scalar52) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 5)
      (fun temp_0_ temp_1_ ->
          let (carry: u64), (difference: t_Scalar52) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (carry, difference <: (u64 & t_Scalar52))
      (fun temp_0_ i ->
          let (carry: u64), (difference: t_Scalar52) = temp_0_ in
          let i:usize = i in
          let addend:u64 =
            Subtle.f_conditional_select #u64
              #FStar.Tactics.Typeclasses.solve
              (mk_u64 0)
              (v_L._0.[ i ] <: u64)
              underflow
          in
          let carry:u64 =
            ((carry >>! mk_i32 52 <: u64) +! (difference._0.[ i ] <: u64) <: u64) +! addend
          in
          let difference:t_Scalar52 =
            {
              difference with
              _0
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize difference._0
                i
                (carry &. mask <: u64)
            }
            <:
            t_Scalar52
          in
          carry, difference <: (u64 & t_Scalar52))
  in
  difference

let impl_Scalar52__add (a b: t_Scalar52) : t_Scalar52 =
  let sum:t_Scalar52 = impl_Scalar52__ZERO in
  let mask:u64 = (mk_u64 1 <<! mk_i32 52 <: u64) -! mk_u64 1 in
  let (carry: u64):u64 = mk_u64 0 in
  let (carry: u64), (sum: t_Scalar52) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 5)
      (fun temp_0_ temp_1_ ->
          let (carry: u64), (sum: t_Scalar52) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (carry, sum <: (u64 & t_Scalar52))
      (fun temp_0_ i ->
          let (carry: u64), (sum: t_Scalar52) = temp_0_ in
          let i:usize = i in
          let carry:u64 =
            ((a._0.[ i ] <: u64) +! (b._0.[ i ] <: u64) <: u64) +! (carry >>! mk_i32 52 <: u64)
          in
          let sum:t_Scalar52 =
            {
              sum with
              _0
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize sum._0
                i
                (carry &. mask <: u64)
            }
            <:
            t_Scalar52
          in
          carry, sum <: (u64 & t_Scalar52))
  in
  impl_Scalar52__sub sum v_L

/// `L * LFACTOR ≡ -1  (mod 2^52)`.
let v_LFACTOR: u64 = mk_u64 1439961107955227

let impl_Scalar52__montgomery_reduce__part1 (sum: u128) : (u128 & u64) =
  let p:u64 =
    (Core_models.Num.impl_u64__wrapping_mul (cast (sum <: u128) <: u64) v_LFACTOR <: u64) &.
    ((mk_u64 1 <<! mk_i32 52 <: u64) -! mk_u64 1 <: u64)
  in
  (sum +! (m p (v_L._0.[ mk_usize 0 ] <: u64) <: u128) <: u128) >>! mk_i32 52, p <: (u128 & u64)

let impl_Scalar52__montgomery_reduce (limbs: t_Array u128 (mk_usize 9)) : t_Scalar52 =
  let l:t_Array u64 (mk_usize 5) = v_L._0 in
  let (carry: u128), (n0: u64) =
    impl_Scalar52__montgomery_reduce__part1 (limbs.[ mk_usize 0 ] <: u128)
  in
  let (carry: u128), (n1: u64) =
    impl_Scalar52__montgomery_reduce__part1 ((carry +! (limbs.[ mk_usize 1 ] <: u128) <: u128) +!
        (m n0 (l.[ mk_usize 1 ] <: u64) <: u128)
        <:
        u128)
  in
  let (carry: u128), (n2: u64) =
    impl_Scalar52__montgomery_reduce__part1 (((carry +! (limbs.[ mk_usize 2 ] <: u128) <: u128) +!
          (m n0 (l.[ mk_usize 2 ] <: u64) <: u128)
          <:
          u128) +!
        (m n1 (l.[ mk_usize 1 ] <: u64) <: u128)
        <:
        u128)
  in
  let (carry: u128), (n3: u64) =
    impl_Scalar52__montgomery_reduce__part1 (((carry +! (limbs.[ mk_usize 3 ] <: u128) <: u128) +!
          (m n1 (l.[ mk_usize 2 ] <: u64) <: u128)
          <:
          u128) +!
        (m n2 (l.[ mk_usize 1 ] <: u64) <: u128)
        <:
        u128)
  in
  let (carry: u128), (n4: u64) =
    impl_Scalar52__montgomery_reduce__part1 ((((carry +! (limbs.[ mk_usize 4 ] <: u128) <: u128) +!
            (m n0 (l.[ mk_usize 4 ] <: u64) <: u128)
            <:
            u128) +!
          (m n2 (l.[ mk_usize 2 ] <: u64) <: u128)
          <:
          u128) +!
        (m n3 (l.[ mk_usize 1 ] <: u64) <: u128)
        <:
        u128)
  in
  let (carry: u128), (r0: u64) =
    impl_Scalar52__montgomery_reduce__part2 ((((carry +! (limbs.[ mk_usize 5 ] <: u128) <: u128) +!
            (m n1 (l.[ mk_usize 4 ] <: u64) <: u128)
            <:
            u128) +!
          (m n3 (l.[ mk_usize 2 ] <: u64) <: u128)
          <:
          u128) +!
        (m n4 (l.[ mk_usize 1 ] <: u64) <: u128)
        <:
        u128)
  in
  let (carry: u128), (r1: u64) =
    impl_Scalar52__montgomery_reduce__part2 (((carry +! (limbs.[ mk_usize 6 ] <: u128) <: u128) +!
          (m n2 (l.[ mk_usize 4 ] <: u64) <: u128)
          <:
          u128) +!
        (m n4 (l.[ mk_usize 2 ] <: u64) <: u128)
        <:
        u128)
  in
  let (carry: u128), (r2: u64) =
    impl_Scalar52__montgomery_reduce__part2 ((carry +! (limbs.[ mk_usize 7 ] <: u128) <: u128) +!
        (m n3 (l.[ mk_usize 4 ] <: u64) <: u128)
        <:
        u128)
  in
  let (carry: u128), (r3: u64) =
    impl_Scalar52__montgomery_reduce__part2 ((carry +! (limbs.[ mk_usize 8 ] <: u128) <: u128) +!
        (m n4 (l.[ mk_usize 4 ] <: u64) <: u128)
        <:
        u128)
  in
  let r4:u64 = cast (carry <: u128) <: u64 in
  impl_Scalar52__sub (Scalar52
      (let list = [r0; r1; r2; r3; r4] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
        Rust_primitives.Hax.array_of_list 5 list)
      <:
      t_Scalar52)
    v_L

let impl_Scalar52__montgomery_mul (a b: t_Scalar52) : t_Scalar52 =
  impl_Scalar52__montgomery_reduce (impl_Scalar52__mul_internal a b <: t_Array u128 (mk_usize 9))

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

let impl_Scalar52__from_bytes_wide (bytes: t_Array u8 (mk_usize 64)) : t_Scalar52 =
  let words:t_Array u64 (mk_usize 8) = Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 8) in
  let words:t_Array u64 (mk_usize 8) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 8)
      (fun words temp_1_ ->
          let words:t_Array u64 (mk_usize 8) = words in
          let _:usize = temp_1_ in
          true)
      words
      (fun words i ->
          let words:t_Array u64 (mk_usize 8) = words in
          let i:usize = i in
          Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
            (mk_usize 8)
            (fun words temp_1_ ->
                let words:t_Array u64 (mk_usize 8) = words in
                let _:usize = temp_1_ in
                true)
            words
            (fun words j ->
                let words:t_Array u64 (mk_usize 8) = words in
                let j:usize = j in
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize words
                  i
                  ((words.[ i ] <: u64) |.
                    ((cast (bytes.[ (i *! mk_usize 8 <: usize) +! j <: usize ] <: u8) <: u64) <<!
                      (j *! mk_usize 8 <: usize)
                      <:
                      u64)
                    <:
                    u64)
                <:
                t_Array u64 (mk_usize 8))
          <:
          t_Array u64 (mk_usize 8))
  in
  let mask:u64 = (mk_u64 1 <<! mk_i32 52 <: u64) -! mk_u64 1 in
  let lo:t_Scalar52 =
    Scalar52
    (let list =
        [
          (words.[ mk_usize 0 ] <: u64) &. mask;
          (((words.[ mk_usize 0 ] <: u64) >>! mk_i32 52 <: u64) |.
            ((words.[ mk_usize 1 ] <: u64) <<! mk_i32 12 <: u64)
            <:
            u64) &.
          mask;
          (((words.[ mk_usize 1 ] <: u64) >>! mk_i32 40 <: u64) |.
            ((words.[ mk_usize 2 ] <: u64) <<! mk_i32 24 <: u64)
            <:
            u64) &.
          mask;
          (((words.[ mk_usize 2 ] <: u64) >>! mk_i32 28 <: u64) |.
            ((words.[ mk_usize 3 ] <: u64) <<! mk_i32 36 <: u64)
            <:
            u64) &.
          mask;
          (((words.[ mk_usize 3 ] <: u64) >>! mk_i32 16 <: u64) |.
            ((words.[ mk_usize 4 ] <: u64) <<! mk_i32 48 <: u64)
            <:
            u64) &.
          mask
        ]
      in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
      Rust_primitives.Hax.array_of_list 5 list)
    <:
    t_Scalar52
  in
  let hi:t_Scalar52 =
    Scalar52
    (let list =
        [
          ((words.[ mk_usize 4 ] <: u64) >>! mk_i32 4 <: u64) &. mask;
          (((words.[ mk_usize 4 ] <: u64) >>! mk_i32 56 <: u64) |.
            ((words.[ mk_usize 5 ] <: u64) <<! mk_i32 8 <: u64)
            <:
            u64) &.
          mask;
          (((words.[ mk_usize 5 ] <: u64) >>! mk_i32 44 <: u64) |.
            ((words.[ mk_usize 6 ] <: u64) <<! mk_i32 20 <: u64)
            <:
            u64) &.
          mask;
          (((words.[ mk_usize 6 ] <: u64) >>! mk_i32 32 <: u64) |.
            ((words.[ mk_usize 7 ] <: u64) <<! mk_i32 32 <: u64)
            <:
            u64) &.
          mask;
          (words.[ mk_usize 7 ] <: u64) >>! mk_i32 20
        ]
      in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
      Rust_primitives.Hax.array_of_list 5 list)
    <:
    t_Scalar52
  in
  let lo:t_Scalar52 = impl_Scalar52__montgomery_mul lo v_R in
  let hi:t_Scalar52 = impl_Scalar52__montgomery_mul hi v_RR in
  impl_Scalar52__add hi lo

/// Construct a scalar by reducing a 512-bit little-endian integer modulo ℓ.
let impl_Scalar__from_bytes_mod_order_wide (bytes: t_Array u8 (mk_usize 64)) : t_Scalar =
  Scalar (impl_Scalar52__to_bytes (impl_Scalar52__from_bytes_wide bytes <: t_Scalar52)) <: t_Scalar

/// Generate a random scalar using the provided RNG.
let impl_Scalar__random
      (#v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Rand_core.t_RngCore v_R)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng v_R)
      (rng: v_R)
    : (v_R & t_Scalar) =
  let bytes:t_Array u8 (mk_usize 64) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 64) in
  let (tmp0: v_R), (tmp1: t_Array u8 (mk_usize 64)) =
    Rand_core.f_fill_bytes #v_R #FStar.Tactics.Typeclasses.solve rng bytes
  in
  let rng:v_R = tmp0 in
  let bytes:t_Array u8 (mk_usize 64) = tmp1 in
  let _:Prims.unit = () in
  let hax_temp_output:t_Scalar = impl_Scalar__from_bytes_mod_order_wide bytes in
  rng, hax_temp_output <: (v_R & t_Scalar)
