module

public import Silmaril.Languages.Python.Core.Binary64.Defs

public section
namespace Silmaril.Proofs.Languages.Python.Core.Binary64

open Silmaril.Languages.Python.Core.Binary64
open Silmaril.Numeric.Ieee754 (F64)
open Silmaril.Numeric.Ieee754.AdjacentRounding (NearestEven)
open Silmaril.Numeric.Ieee754.RationalRounding
open Silmaril.Numeric.Ieee754.Binary64Signs (magnitudeBits exponent_magnitude)

private theorem quotientMagnitude_eq_abs (numerator divisor : Int) :
    quotientMagnitude numerator divisor = |(numerator : ℚ) / (divisor : ℚ)| := by
  simp only [quotientMagnitude, abs_div, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]

private theorem quotient_nonnegative (numerator divisor : Int) :
    0 ≤ quotientMagnitude numerator divisor := by
  unfold quotientMagnitude
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem rounded_finite_iff (negative : Bool) {magnitude : ℚ} (nonnegative : 0 ≤ magnitude) :
    (F64.ofBits (roundSigned negative magnitude)).IsFinite ↔ magnitude < overflowThreshold := by
  have noOverflow := (not_congr (roundIndex_overflow_iff magnitude nonnegative)).trans not_le
  rw [← noOverflow, F64.IsFinite, exponent_magnitude]
  simp only [F64.ofBits, magnitudeBits_roundSigned, roundPositive_toNat]
  have range := roundIndex_le_limit magnitude
  change roundIndex magnitude / (2 ^ 52 : Nat) ≠ 0x7ff ↔ roundIndex magnitude ≠ limit
  unfold limit at range ⊢
  norm_num only [Nat.reducePow]
  omega

theorem roundExact_none_iff (negative : Bool) (value : ℚ) :
    roundExact? negative value = none ↔ overflowThreshold ≤ |value| := by
  have finite := rounded_finite_iff negative (abs_nonneg value)
  by_cases below : |value| < overflowThreshold
  · simp [roundExact?, F64.Finite.ofRaw?, finite.mpr below, not_le_of_gt below]
  · simp [roundExact?, F64.Finite.ofRaw?, mt finite.mp below, le_of_not_gt below]

theorem roundExact_ok_iff (negative : Bool) (value : ℚ) (result : F64.Finite) :
    roundExact? negative value = some result ↔ |value| < overflowThreshold ∧
      result.val = F64.ofBits (roundSigned negative |value|) := by
  have finite := rounded_finite_iff negative (abs_nonneg value)
  by_cases below : |value| < overflowThreshold
  · simp [roundExact?, F64.Finite.ofRaw?, finite.mpr below, below, Subtype.ext_iff, eq_comm]
  · simp [roundExact?, F64.Finite.ofRaw?, mt finite.mp below, below]

private theorem decimal_nonnegative (coefficient : Nat) (exponent : Int) :
    0 ≤ decimalMagnitude coefficient exponent := by
  unfold decimalMagnitude
  exact mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg (by decide : 0 ≤ (10 : ℚ)) exponent)

theorem ofDecimal_ok_iff (negative : Bool) (coefficient : Nat) (exponent : Int) (result : F64.Finite) :
    ofDecimal? negative coefficient exponent = some result ↔
      decimalInProfile coefficient exponent ∧ decimalMagnitude coefficient exponent < overflowThreshold ∧
        result.val = F64.ofBits (roundSigned negative (decimalMagnitude coefficient exponent)) := by
  by_cases admitted : decimalInProfile coefficient exponent
  · have finite := rounded_finite_iff negative (decimal_nonnegative coefficient exponent)
    by_cases below : decimalMagnitude coefficient exponent < overflowThreshold
    · simp [ofDecimal?, admitted, F64.Finite.ofRaw?, finite.mpr below, below, Subtype.ext_iff, eq_comm]
    · simp [ofDecimal?, admitted, F64.Finite.ofRaw?, mt finite.mp below, below]
  · simp [ofDecimal?, admitted]

theorem ofDecimal_nearestEven {negative : Bool} {coefficient : Nat} {exponent : Int} {result : F64.Finite}
    (computed : ofDecimal? negative coefficient exponent = some result) :
    result.val.signBit = negative ∧
      NearestEven magnitude (decimalMagnitude coefficient exponent) (magnitudeBits result.val.bits).toNat := by
  obtain ⟨_, below, bits⟩ := (ofDecimal_ok_iff negative coefficient exponent result).mp computed
  rw [bits]
  exact ⟨signBit_roundSigned _ _, (roundSigned_nearestEven _ _ (decimal_nonnegative _ _) below).2⟩

theorem trueDivide_zeroDivision_iff (numerator divisor : Int) :
    trueDivide numerator divisor = .error .zeroDivisionError ↔ divisor = 0 := by
  by_cases zero : divisor = 0
  · simp [trueDivide, zero]
  · simp only [trueDivide, zero, ↓reduceIte, iff_false]
    split <;> simp

theorem trueDivide_overflow_iff (numerator divisor : Int) :
    trueDivide numerator divisor = .error .overflowError ↔
      divisor ≠ 0 ∧ overflowThreshold ≤ quotientMagnitude numerator divisor := by
  by_cases zero : divisor = 0
  · simp [trueDivide, zero]
  have finite := rounded_finite_iff (quotientNegative numerator divisor) (quotient_nonnegative numerator divisor)
  by_cases below : quotientMagnitude numerator divisor < overflowThreshold
  · simp [trueDivide, zero, F64.Finite.ofRaw?, finite.mpr below, not_le_of_gt below]
  · simp [trueDivide, zero, F64.Finite.ofRaw?, mt finite.mp below, le_of_not_gt below]

theorem trueDivide_ok_iff (numerator divisor : Int) (result : F64.Finite) :
    trueDivide numerator divisor = .ok result ↔
      divisor ≠ 0 ∧ quotientMagnitude numerator divisor < overflowThreshold ∧
        result.val = F64.ofBits (roundSigned (quotientNegative numerator divisor) (quotientMagnitude numerator divisor)) := by
  by_cases zero : divisor = 0
  · simp [trueDivide, zero]
  have finite := rounded_finite_iff (quotientNegative numerator divisor) (quotient_nonnegative numerator divisor)
  by_cases below : quotientMagnitude numerator divisor < overflowThreshold
  · simp [trueDivide, zero, F64.Finite.ofRaw?, finite.mpr below, below, Subtype.ext_iff, eq_comm]
  · simp [trueDivide, zero, F64.Finite.ofRaw?, mt finite.mp below, below]

theorem trueDivide_nearestEven {numerator divisor : Int} {result : F64.Finite}
    (computed : trueDivide numerator divisor = .ok result) :
    result.val.signBit = quotientNegative numerator divisor ∧
      NearestEven magnitude |(numerator : ℚ) / (divisor : ℚ)|
        (magnitudeBits result.val.bits).toNat := by
  obtain ⟨_, below, bits⟩ := (trueDivide_ok_iff numerator divisor result).mp computed
  rw [bits, ← quotientMagnitude_eq_abs]
  exact ⟨signBit_roundSigned _ _,
    (roundSigned_nearestEven _ _ (quotient_nonnegative numerator divisor) below).2⟩

theorem divideFloat_conversion_overflow (operands : FloatOperands) (failed : operands.convert? = none) :
    divideFloat operands = .error .conversionOverflow := by
  simp [divideFloat, failed]

private theorem divideFloat_converted {operands : FloatOperands} {left right : F64.Finite} {lhs rhs : ℚ}
    (converted : operands.convert? = some (left, right))
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs) :
    divideFloat operands = if rhs = 0 then .error .zeroDivisionError
      else (roundExact? (left.val.signBit != right.val.signBit) (lhs / rhs)).elim (.error .nonfiniteResult) .ok := by
  simp [divideFloat, converted, leftValue, rightValue]

theorem divideFloat_zeroDivision_iff {operands : FloatOperands} {left right : F64.Finite} {lhs rhs : ℚ}
    (converted : operands.convert? = some (left, right))
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs) :
    divideFloat operands = .error .zeroDivisionError ↔ rhs = 0 := by
  rw [divideFloat_converted converted leftValue rightValue]
  by_cases zero : rhs = 0
  · simp [zero]
  · cases roundExact? (left.val.signBit != right.val.signBit) (lhs / rhs) <;> simp [zero]

theorem divideFloat_nonfinite_iff {operands : FloatOperands} {left right : F64.Finite} {lhs rhs : ℚ}
    (converted : operands.convert? = some (left, right))
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs) :
    divideFloat operands = .error .nonfiniteResult ↔ rhs ≠ 0 ∧ overflowThreshold ≤ |lhs / rhs| := by
  rw [divideFloat_converted converted leftValue rightValue]
  by_cases zero : rhs = 0
  · simp [zero]
  · rw [← roundExact_none_iff (left.val.signBit != right.val.signBit)]
    cases roundExact? (left.val.signBit != right.val.signBit) (lhs / rhs) <;> simp [zero]

theorem divideFloat_ok_iff {operands : FloatOperands} {left right result : F64.Finite} {lhs rhs : ℚ}
    (converted : operands.convert? = some (left, right))
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs) :
    divideFloat operands = .ok result ↔ rhs ≠ 0 ∧ |lhs / rhs| < overflowThreshold ∧
      result.val = F64.ofBits (roundSigned (left.val.signBit != right.val.signBit) |lhs / rhs|) := by
  rw [divideFloat_converted converted leftValue rightValue]
  by_cases zero : rhs = 0
  · simp [zero]
  · rw [← roundExact_ok_iff (left.val.signBit != right.val.signBit)]
    cases roundExact? (left.val.signBit != right.val.signBit) (lhs / rhs) <;> simp [zero]

theorem divideFloat_nearestEven {operands : FloatOperands} {left right result : F64.Finite} {lhs rhs : ℚ}
    (converted : operands.convert? = some (left, right))
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs)
    (divided : divideFloat operands = .ok result) :
    result.val.signBit = (left.val.signBit != right.val.signBit) ∧
      NearestEven magnitude |lhs / rhs| (magnitudeBits result.val.bits).toNat := by
  obtain ⟨_, below, bits⟩ := (divideFloat_ok_iff converted leftValue rightValue).mp divided
  rw [bits]
  exact ⟨signBit_roundSigned _ _, (roundSigned_nearestEven _ _ (abs_nonneg _) below).2⟩

end Silmaril.Proofs.Languages.Python.Core.Binary64
