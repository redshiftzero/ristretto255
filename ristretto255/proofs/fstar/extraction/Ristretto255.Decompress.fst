module Ristretto255.Decompress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Ristretto255.Bundle {step_1_ as step_1_}

include Ristretto255.Bundle {step_2_ as step_2_}
