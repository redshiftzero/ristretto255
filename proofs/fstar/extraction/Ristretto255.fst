module Ristretto255
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Ristretto255.Bundle_decompress {t_CompressedRistretto as t_CompressedRistretto}

include Ristretto255.Bundle_decompress {CompressedRistretto as CompressedRistretto}

include Ristretto255.Bundle_decompress {impl_5 as impl_5}

include Ristretto255.Bundle_decompress {impl_6 as impl_6}

include Ristretto255.Bundle_decompress {impl_7 as impl_7}

include Ristretto255.Bundle_decompress {impl_8 as impl_8}

include Ristretto255.Bundle_decompress {impl as impl}

include Ristretto255.Bundle_decompress {impl_1 as impl_1}

include Ristretto255.Bundle_decompress {impl_9__to_bytes as impl_CompressedRistretto__to_bytes}

include Ristretto255.Bundle_decompress {impl_9__as_bytes as impl_CompressedRistretto__as_bytes}

include Ristretto255.Bundle_decompress {impl_9__from_slice as impl_CompressedRistretto__from_slice}

include Ristretto255.Bundle_decompress {impl_9__decompress as impl_CompressedRistretto__decompress}

include Ristretto255.Bundle_decompress {impl_2 as impl_2}

include Ristretto255.Bundle_decompress {impl_3 as impl_3}

include Ristretto255.Bundle_decompress {impl_4 as impl_4}

include Ristretto255.Bundle_decompress {t_RistrettoPoint as t_RistrettoPoint}

include Ristretto255.Bundle_decompress {RistrettoPoint as RistrettoPoint}

include Ristretto255.Bundle_decompress {t_EdwardsPoint as t_EdwardsPoint}
