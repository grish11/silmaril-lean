module

public import Silmaril.Numeric.Ieee754.Quantization.Defs
import Silmaril.Proofs.Numeric.Ieee754.Quantization.Error

/-! # Absolute rounding error for finite binary64 brackets -/

public section

namespace Silmaril.Numeric.Ieee754.Quantization

open RationalRounding

/-- If the input magnitude lies between adjacent finite binary64 magnitudes,
the actual nearest-even rounder decodes to a finite value within half their gap.
The consecutive sign-clear encodings may include zero, subnormals, or a binade
boundary. The upper encoding is strictly below the infinity encoding `limit`,
so the largest allowed endpoint is maximum finite. The bound holds for either
sign, including midpoint ties, where the rounder selects the even encoding. -/
theorem binary64_error (x : ℚ) (lower : Nat) (hfinite : lower + 1 < limit)
    (hlo : magnitude lower ≤ |x|) (hhi : |x| ≤ magnitude (lower + 1)) :
    ∃ q : ℚ, binary64 x = some q ∧
      |q - x| ≤ (magnitude (lower + 1) - magnitude lower) / 2 :=
  Proofs.Numeric.Ieee754.Quantization.binary64_error x lower hfinite hlo hhi

end Silmaril.Numeric.Ieee754.Quantization
