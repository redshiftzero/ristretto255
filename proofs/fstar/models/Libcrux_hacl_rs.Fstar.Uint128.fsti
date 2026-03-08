module Libcrux_hacl_rs.Fstar.Uint128
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// Stub models for libcrux-hacl-rs uint128 utilities.

val uint64_to_uint128 (x: u64) : u128
