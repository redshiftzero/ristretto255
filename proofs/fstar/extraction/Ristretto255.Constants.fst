module Ristretto255.Constants
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Ristretto255.Bundle {v_EDWARDS_D as v_EDWARDS_D}

include Ristretto255.Bundle {v_SQRT_M1 as v_SQRT_M1}
