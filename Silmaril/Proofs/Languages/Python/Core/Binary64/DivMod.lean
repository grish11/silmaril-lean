module

public import Silmaril.Languages.Python.Core.Binary64.Defs
import Silmaril.Proofs.Languages.Python.Core.Binary64.Addition
import Silmaril.Proofs.Languages.Python.Core.Binary64.Division

public section
namespace Silmaril.Proofs.Languages.Python.Core.Binary64

open Silmaril.Languages.Python.Core.Binary64
open Silmaril.Numeric.Ieee754 (F64)
open Silmaril.Numeric.Ieee754.RationalRounding (overflowThreshold roundSigned)

theorem truncatingRemainder_bounds {lhs rhs : ℚ} (nonzero : rhs ≠ 0) :
    |truncatingRemainder lhs rhs| < |rhs| ∧
      (lhs < 0 → truncatingRemainder lhs rhs ≤ 0) ∧
      (0 ≤ lhs → 0 ≤ truncatingRemainder lhs rhs) := by
  let divisor := |rhs|
  let ratio := |lhs| / divisor
  let q : Int := ratio.floor
  have positive : 0 < divisor := abs_pos.mpr nonzero
  have lower : (q : ℚ) ≤ ratio := Int.floor_le ratio
  have upper : ratio < (q : ℚ) + 1 := Int.lt_floor_add_one ratio
  have start : (q : ℚ) * divisor ≤ |lhs| := (le_div_iff₀ positive).mp lower
  have stop : |lhs| < ((q : ℚ) + 1) * divisor := (div_lt_iff₀ positive).mp upper
  have nonnegative : 0 ≤ |lhs| - (q : ℚ) * divisor := sub_nonneg.mpr start
  have bounded : |lhs| - (q : ℚ) * divisor < divisor := by
    rw [add_mul, one_mul] at stop
    exact sub_lt_iff_lt_add.mpr (by simpa only [add_comm divisor] using stop)
  change |(if lhs < 0 then -(|lhs| - (q : ℚ) * divisor) else |lhs| - (q : ℚ) * divisor)| <
      divisor ∧ _
  constructor
  · by_cases negative : lhs < 0
    · rw [ite_eq_left negative, abs_neg, abs_of_nonneg nonnegative]
      exact bounded
    · rw [ite_eq_right negative, abs_of_nonneg nonnegative]
      exact bounded
  · unfold truncatingRemainder
    exact ⟨fun negative => by simpa [negative] using neg_nonpos.mpr nonnegative,
      fun nonneg => by simpa [not_lt.mpr nonneg] using nonnegative⟩

theorem fmodFinite_ok_iff {left right result : F64.Finite} {lhs rhs : ℚ}
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs) :
    fmodFinite? left right = some result ↔
      rhs ≠ 0 ∧
        |truncatingRemainder lhs rhs| < overflowThreshold ∧
        result.val = F64.ofBits (roundSigned left.val.signBit |truncatingRemainder lhs rhs|) ∧
        result.val.toRat? = some (truncatingRemainder lhs rhs) := by
  by_cases zero : rhs = 0
  · simp [fmodFinite?, leftValue, rightValue, zero]
  · simp [fmodFinite?, leftValue, rightValue, zero, encodeExact?, Option.filter_eq_some_iff,
      roundExact_ok_iff, and_assoc]

theorem signRemainder_zero (right remainder : F64.Finite) :
    (signRemainder? right remainder 0).map (fun result => result.val.bits) =
      some (if right.val.signBit then 0x8000000000000000 else 0) := by
  simpa [signRemainder?] using roundExact_zero right.val.signBit

theorem signRemainder_nonzero_ok_iff {right remainder result : F64.Finite} {rhs value : ℚ}
    (rightValue : right.val.toRat? = some rhs) (remainderValue : remainder.val.toRat? = some value)
    (nonzero : value ≠ 0) :
    signRemainder? right remainder value = some result ↔
      if needsDivModCorrection right remainder value then
        |value + rhs| < overflowThreshold ∧
        result.val = F64.ofBits (roundSigned (sumNegative remainder right (value + rhs)) |value + rhs|)
      else result = remainder := by
  cases adjusted : needsDivModCorrection right remainder value
  · simp [signRemainder?, nonzero, adjusted, eq_comm]
  · simpa [signRemainder?, nonzero, adjusted] using
      (addFinite_ok_iff (result := result) remainderValue rightValue)

theorem snapQuotient_zero {negative : Bool} {quotient : F64.Finite}
    (zero : quotient.val.toRat? = some 0) :
    (snapQuotient? negative quotient).map (fun result => result.val.bits) =
      some (if negative then 0x8000000000000000 else 0) := by
  simpa [snapQuotient?, zero] using roundExact_zero negative

theorem snapQuotient_nonzero_ok_iff {negative : Bool} {quotient integral fraction result : F64.Finite}
    {value delta : ℚ} (quotientValue : quotient.val.toRat? = some value) (nonzero : value ≠ 0)
    (encoded : encodeExact? (decide (value.floor < 0)) (value.floor : ℚ) = some integral)
    (fractional : subFinite? quotient integral = some fraction) (readFraction : fraction.val.toRat? = some delta) :
    snapQuotient? negative quotient = some result ↔
      if delta > 1 / 2 then
        |(value.floor : ℚ) + 1| < overflowThreshold ∧
        result.val = F64.ofBits (roundSigned (sumNegative integral divModOne ((value.floor : ℚ) + 1))
          |(value.floor : ℚ) + 1|)
      else result = integral := by
  by_cases upper : (2 : ℚ)⁻¹ < delta
  · have floorValue : integral.val.toRat? = some (value.floor : ℚ) := by
      exact ((Option.filter_eq_some_iff.mp encoded).2 |> beq_iff_eq.mp)
    have oneValue : divModOne.val.toRat? = some (1 : ℚ) := by decide +kernel
    simpa [snapQuotient?, quotientValue, nonzero, encoded, fractional, readFraction, upper] using
      (addFinite_ok_iff (result := result) floorValue oneValue)
  · simp [snapQuotient?, quotientValue, nonzero, encoded, fractional, readFraction, upper, eq_comm]

theorem floorQuotient_ok_iff {left right remainder result : F64.Finite} {rhs : ℚ}
    (rightValue : right.val.toRat? = some rhs) (adjust : Bool) :
    floorQuotient? left right remainder adjust = some result ↔
      ∃ (difference : F64.Finite) (delta : ℚ),
        subFinite? left remainder = some difference ∧ difference.val.toRat? = some delta ∧
        ∃ quotient : F64.Finite,
          |delta / rhs| < overflowThreshold ∧
          quotient.val = F64.ofBits (roundSigned (difference.val.signBit != right.val.signBit) |delta / rhs|) ∧
          ∃ corrected : F64.Finite,
            (if adjust then subFinite? quotient divModOne else some quotient) = some corrected ∧
            snapQuotient? (left.val.signBit != right.val.signBit) corrected = some result := by
  simp only [floorQuotient?, rightValue, Option.bind_eq_bind]
  change ((subFinite? left remainder).bind fun difference =>
    difference.val.toRat?.bind fun delta =>
      (roundExact? (difference.val.signBit != right.val.signBit) (delta / rhs)).bind fun quotient =>
        (if adjust then subFinite? quotient divModOne else some quotient).bind
          (snapQuotient? (left.val.signBit != right.val.signBit))) = some result ↔ _
  simp only [Option.bind_eq_some_iff, roundExact_ok_iff, and_assoc]
  constructor
  · rintro ⟨difference, hd, delta, hv, quotient, bound, bits, corrected, correction, snapped⟩
    exact ⟨difference, delta, hd, hv, quotient, bound, bits, corrected, correction, snapped⟩
  · rintro ⟨difference, delta, hd, hv, quotient, bound, bits, corrected, correction, snapped⟩
    exact ⟨difference, hd, delta, hv, quotient, bound, bits, corrected, correction, snapped⟩

theorem floatDivMod_conversion_overflow (op : FloatDivModOp) {operands : FloatOperands}
    (failed : operands.convert? = none) :
    op.eval operands = .error .conversionOverflow := by simp [FloatDivModOp.eval, failed]

theorem floatDivMod_zeroDivision_iff (op : FloatDivModOp) {operands : FloatOperands}
    {left right : F64.Finite} {rhs : ℚ}
    (converted : operands.convert? = some (left, right)) (rightValue : right.val.toRat? = some rhs) :
    op.eval operands = .error .zeroDivisionError ↔ rhs = 0 := by
  by_cases zero : rhs = 0
  · simp [FloatDivModOp.eval, converted, rightValue, zero]
  · cases finite : op.finite? left right <;> simp [FloatDivModOp.eval, converted, rightValue, zero, finite]

theorem floatDivMod_ok_iff (op : FloatDivModOp) {operands : FloatOperands}
    {left right result : F64.Finite} {rhs : ℚ}
    (converted : operands.convert? = some (left, right)) (rightValue : right.val.toRat? = some rhs) :
    op.eval operands = .ok result ↔ rhs ≠ 0 ∧ op.finite? left right = some result := by
  by_cases zero : rhs = 0
  · simp [FloatDivModOp.eval, converted, rightValue, zero]
  · cases finite : op.finite? left right <;> simp [FloatDivModOp.eval, converted, rightValue, zero, finite]

end Silmaril.Proofs.Languages.Python.Core.Binary64
