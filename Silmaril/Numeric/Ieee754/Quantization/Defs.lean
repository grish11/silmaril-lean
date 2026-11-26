module

public import Silmaril.Numeric.Ieee754.SignedRationalRounding

/-! # Binary64 quantization of exact rationals -/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Quantization

/-- Round an exact rational to binary64, ties to even, then decode its
finite value. At magnitudes at or above the overflow midpoint `2^1024 - 2^970`,
rounding produces signed infinity and decoding returns `none`. Gradual
underflow retains subnormal results. Both signed zeros decode to rational zero.
The input domain consists of exact finite rationals. -/
def binary64 (x : ℚ) : Option ℚ := (F64.ofBits (RationalRounding.roundRational x)).toRat?

end Silmaril.Numeric.Ieee754.Quantization
