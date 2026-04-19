module Ristretto255.Constants
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Ristretto255.Bundle {v_EDWARDS_D as v_EDWARDS_D}

include Ristretto255.Bundle {v_SQRT_M1 as v_SQRT_M1}

include Ristretto255.Bundle {v_INVSQRT_A_MINUS_D as v_INVSQRT_A_MINUS_D}

include Ristretto255.Bundle {v_ONE_MINUS_EDWARDS_D_SQUARED as v_ONE_MINUS_EDWARDS_D_SQUARED}

include Ristretto255.Bundle {v_EDWARDS_D_MINUS_ONE_SQUARED as v_EDWARDS_D_MINUS_ONE_SQUARED}

include Ristretto255.Bundle {v_SQRT_AD_MINUS_ONE as v_SQRT_AD_MINUS_ONE}

include Ristretto255.Bundle {v_MINUS_ONE as v_MINUS_ONE}

include Ristretto255.Bundle {v_EDWARDS_D2 as v_EDWARDS_D2}

include Ristretto255.Bundle {v_RISTRETTO_BASEPOINT_COMPRESSED as v_RISTRETTO_BASEPOINT_COMPRESSED}
