module

public import Silmaril.Numeric.Ieee754.Quantization.Defs
import Silmaril.Numeric.Ieee754.SignedRationalProperties
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

public section

open Silmaril.Numeric.Ieee754
open Silmaril.Numeric.Ieee754.Quantization
open Silmaril.Numeric.Ieee754.RationalRounding

namespace Silmaril.Proofs.Numeric.Ieee754.Quantization

private theorem decode_finite (bits : UInt64) (hfinite : (Binary64Signs.magnitudeBits bits).toNat < limit) :
    (F64.ofBits bits).toRat? = some (Decimal.rational bits) := by
  have he : (decode64 bits.toNat).exponent ≠ maxExponentField binary64ExponentBits := by
    rw [Binary64Signs.exponent_magnitude]
    norm_num [limit, maxExponentField, binary64ExponentBits] at hfinite ⊢
    omega
  rw [Decimal.rational, Conformance.value?_model_unpack64]
  simp only [F64.toRat?, F64.ofBits, value64?, finiteValue, beq_iff_eq, he, ite_false]
  split <;> rfl

theorem binary64_error (x : ℚ) (lower : Nat) (hfinite : lower + 1 < limit)
    (hlo : magnitude lower ≤ |x|) (hhi : |x| ≤ magnitude (lower + 1)) :
    ∃ q : ℚ, binary64 x = some q ∧
      |q - x| ≤ (magnitude (lower + 1) - magnitude lower) / 2 := by
  have hbelow : |x| < overflowThreshold := by
    have hmax : lower + 1 ≤ limit - 1 := by omega
    exact (hhi.trans (magnitude_strictMono.monotone hmax)).trans_lt maxFinite_lt_overflowThreshold
  obtain ⟨hindex, hnearest, _⟩ := roundIndex_nearestEven |x| (abs_nonneg x) hbelow
  have hl := hnearest lower
  have hu := hnearest (lower + 1)
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)] at hl
  rw [abs_of_nonpos (sub_nonpos.mpr hhi)] at hu
  have herr : abs (|x| - magnitude (roundIndex |x|)) ≤ (magnitude (lower + 1) - magnitude lower) / 2 :=
    by linarith
  have hbits : (Binary64Signs.magnitudeBits (roundRational x)).toNat < limit := by
    rw [roundRational, magnitudeBits_roundSigned, roundPositive_toNat]
    exact hindex
  have hvalue : Decimal.rational (roundPositive |x|) = magnitude (roundIndex |x|) := by
    have hfinite : (roundPositive |x|).toNat ≤ 0x7fefffffffffffff := by
      rw [roundPositive_toNat]
      unfold limit at hindex
      omega
    rw [Decimal.rational_eq_binaryMagnitude _ hfinite, roundPositive_toNat]
    rfl
  have hsign : signed (decide (x < 0)) |x| = x := by
    by_cases h : x < 0
    · simp [signed, h, abs_of_neg h]
    · simp [signed, h, abs_of_nonneg (le_of_not_gt h)]
  have hdist (sign : Bool) (a b : ℚ) : |signed sign a - signed sign b| = |b - a| := by
    cases sign
    · exact abs_sub_comm a b
    · change |-a - -b| = |b - a|
      rw [neg_sub_neg]
  refine ⟨Decimal.rational (roundRational x), decode_finite _ hbits, ?_⟩
  calc
    |Decimal.rational (roundRational x) - x| =
        abs (signed (decide (x < 0)) (magnitude (roundIndex |x|)) - signed (decide (x < 0)) |x|) :=
      congrArg₂ (fun a b : ℚ => |a - b|)
        (by rw [roundRational, rational_roundSigned, hvalue]) hsign.symm
    _ = abs (|x| - magnitude (roundIndex |x|)) := hdist _ _ _
    _ ≤ _ := herr

end Silmaril.Proofs.Numeric.Ieee754.Quantization
