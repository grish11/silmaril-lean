module

import Silmaril.Numeric.Ieee754.Quantization.Thms

/-! # Binary64 midpoint examples -/

namespace Silmaril.Numeric.Ieee754.Quantization.Examples

open RationalRounding

/-- Halfway from 1 to its binary64 successor, the converter selects the even
encoding for 1. Decoding attains the half-gap bound `2⁻⁵³`. -/
example : roundRational (1 + 1 / 2 ^ (53 : Nat)) = 0x3ff0000000000000 ∧
    binary64 (1 + 1 / 2 ^ (53 : Nat)) = some 1 ∧
    |(1 : ℚ) - (1 + 1 / 2 ^ (53 : Nat))| =
      (magnitude (0x3ff0000000000000 + 1) - magnitude 0x3ff0000000000000) / 2 := by
  decide +kernel

/-- Halfway between the first two positive subnormals, the even successor
survives decoding as `2⁻¹⁰⁷³`. -/
example : binary64 (3 * (2 : ℚ) ^ (-1075 : Int)) = some ((2 : ℚ) ^ (-1073 : Int)) := by
  decide +kernel

/-- The negative overflow midpoint rounds to infinity and has no finite decoding. -/
example : binary64 (-overflowThreshold) = none := by decide +kernel

end Silmaril.Numeric.Ieee754.Quantization.Examples
