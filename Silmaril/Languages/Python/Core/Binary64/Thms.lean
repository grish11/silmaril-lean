module

public import Silmaril.Languages.Python.Core.Binary64.Defs
import Silmaril.Proofs.Languages.Python.Core.Binary64.Addition
import Silmaril.Proofs.Languages.Python.Core.Binary64.Division
import Silmaril.Proofs.Languages.Python.Core.Binary64.Equality

public section
namespace Silmaril.Languages.Python.Core.Binary64

open Silmaril.Numeric.Ieee754 (F64)
open Silmaril.Numeric.Ieee754.AdjacentRounding (NearestEven)
open Silmaril.Numeric.Ieee754.RationalRounding
open Silmaril.Numeric.Ieee754.Binary64Signs (magnitudeBits)

theorem ofDecimal_ok_iff (negative : Bool) (coefficient : Nat) (exponent : Int) (result : F64.Finite) :
    ofDecimal? negative coefficient exponent = some result ↔
      decimalInProfile coefficient exponent ∧ decimalMagnitude coefficient exponent < overflowThreshold ∧
        result.val = F64.ofBits (roundSigned negative (decimalMagnitude coefficient exponent)) :=
  Proofs.Languages.Python.Core.Binary64.ofDecimal_ok_iff negative coefficient exponent result

theorem ofDecimal_nearestEven {negative : Bool} {coefficient : Nat} {exponent : Int} {result : F64.Finite}
    (computed : ofDecimal? negative coefficient exponent = some result) :
    result.val.signBit = negative ∧
      NearestEven magnitude (decimalMagnitude coefficient exponent) (magnitudeBits result.val.bits).toNat :=
  Proofs.Languages.Python.Core.Binary64.ofDecimal_nearestEven computed

theorem finite_has_exact_value (value : F64.Finite) : ∃ q : ℚ, value.val.toRat? = some q :=
  Proofs.Languages.Python.Core.Binary64.finite_has_exact_value value

theorem equal_eq_ieee (left right : F64.Finite) :
    equal left right = true ↔ left.val.equal right.val = true :=
  Proofs.Languages.Python.Core.Binary64.equal_eq_ieee left right

theorem equalInt_iff_exact (left : F64.Finite) (right : Int) :
    equalInt left right = true ↔ left.val.toRat? = some (right : ℚ) := by simp [equalInt]

theorem signed_zeros_equal :
    equal ⟨F64.ofBits 0, by decide⟩ ⟨F64.ofBits 0x8000000000000000, by decide⟩ = true := by
  decide +kernel

theorem intToFinite_none_iff (integer : Int) :
    intToFinite? integer = none ↔ overflowThreshold ≤ (integer.natAbs : ℚ) :=
  Proofs.Languages.Python.Core.Binary64.intToFinite_none_iff integer

theorem intToFinite_nearestEven {integer : Int} {result : F64.Finite}
    (converted : intToFinite? integer = some result) :
    result.val.signBit = decide (integer < 0) ∧
      NearestEven magnitude (integer.natAbs : ℚ) (magnitudeBits result.val.bits).toNat :=
  Proofs.Languages.Python.Core.Binary64.intToFinite_nearestEven converted

theorem addFinite_none_iff {left right : F64.Finite} {lhs rhs : ℚ}
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs) :
    addFinite? left right = none ↔ overflowThreshold ≤ |lhs + rhs| :=
  Proofs.Languages.Python.Core.Binary64.addFinite_none_iff leftValue rightValue

theorem addFinite_ok_iff {left right result : F64.Finite} {lhs rhs : ℚ}
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs) :
    addFinite? left right = some result ↔ |lhs + rhs| < overflowThreshold ∧
      result.val = F64.ofBits (roundSigned (sumNegative left right (lhs + rhs)) |lhs + rhs|) :=
  Proofs.Languages.Python.Core.Binary64.addFinite_ok_iff leftValue rightValue

theorem addFinite_nearestEven {left right result : F64.Finite} {lhs rhs : ℚ}
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs)
    (added : addFinite? left right = some result) :
    result.val.signBit = sumNegative left right (lhs + rhs) ∧
      NearestEven magnitude |lhs + rhs| (magnitudeBits result.val.bits).toNat :=
  Proofs.Languages.Python.Core.Binary64.addFinite_nearestEven leftValue rightValue added

theorem addFinite_comm (left right : F64.Finite) : addFinite? left right = addFinite? right left :=
  Proofs.Languages.Python.Core.Binary64.addFinite_comm left right

/-- Exact cancellation has positive zero unless both input signs are negative. -/
theorem addFinite_zero {left right : F64.Finite} {lhs rhs : ℚ}
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs)
    (zero : lhs + rhs = 0) :
    (addFinite? left right).map (fun result => result.val.bits) =
      some (if left.val.signBit && right.val.signBit then 0x8000000000000000 else 0) :=
  Proofs.Languages.Python.Core.Binary64.addFinite_zero leftValue rightValue zero

/-- A nonzero exact sum on the subnormal grid retains its exact magnitude bits. -/
theorem addFinite_subnormal {left right : F64.Finite} {lhs rhs : ℚ} {index : Nat}
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs)
    (positive : 0 < index) (subnormal : index < 2 ^ 52)
    (sum : |lhs + rhs| = magnitude index) :
    (addFinite? left right).map (fun result => (magnitudeBits result.val.bits).toNat) = some index :=
  Proofs.Languages.Python.Core.Binary64.addFinite_subnormal leftValue rightValue positive subnormal sum

theorem mixedAdd_conversion_overflow_iff (integer : Int) (floating : F64.Finite) :
    mixedAdd integer floating = .error .conversionOverflow ↔ overflowThreshold ≤ (integer.natAbs : ℚ) :=
  Proofs.Languages.Python.Core.Binary64.mixedAdd_conversion_overflow_iff integer floating

theorem mixedAdd_ok_iff (integer : Int) (floating result : F64.Finite) :
    mixedAdd integer floating = .ok result ↔
      ∃ converted, intToFinite? integer = some converted ∧ addFinite? converted floating = some result :=
  Proofs.Languages.Python.Core.Binary64.mixedAdd_ok_iff integer floating result

theorem mixedAdd_nonfinite_iff {integer : Int} {floating converted : F64.Finite} {lhs rhs : ℚ}
    (coercion : intToFinite? integer = some converted)
    (leftValue : converted.val.toRat? = some lhs) (rightValue : floating.val.toRat? = some rhs) :
    mixedAdd integer floating = .error .nonfiniteResult ↔ overflowThreshold ≤ |lhs + rhs| :=
  Proofs.Languages.Python.Core.Binary64.mixedAdd_nonfinite_iff coercion leftValue rightValue

theorem subFinite_ok_iff {left right result : F64.Finite} {lhs rhs : ℚ}
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs) :
    subFinite? left right = some result ↔ |lhs - rhs| < overflowThreshold ∧
      result.val = F64.ofBits (roundSigned (sumSign left.val.signBit (!right.val.signBit) (lhs - rhs))
        |lhs - rhs|) :=
  Proofs.Languages.Python.Core.Binary64.subFinite_ok_iff leftValue rightValue

theorem subFinite_zero {left right : F64.Finite} {lhs rhs : ℚ}
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs)
    (zero : lhs - rhs = 0) :
    (subFinite? left right).map (fun result => result.val.bits) =
      some (if left.val.signBit && !right.val.signBit then 0x8000000000000000 else 0) :=
  Proofs.Languages.Python.Core.Binary64.subFinite_zero leftValue rightValue zero

theorem subtract_ok_iff (operands : FloatOperands) (result : F64.Finite) :
    subtract operands = .ok result ↔ ∃ left right,
      operands.convert? = some (left, right) ∧ subFinite? left right = some result :=
  Proofs.Languages.Python.Core.Binary64.subtract_ok_iff operands result

theorem subtract_conversion_overflow_iff (operands : FloatOperands) :
    subtract operands = .error .conversionOverflow ↔ operands.convert? = none :=
  Proofs.Languages.Python.Core.Binary64.subtract_conversion_overflow_iff operands

theorem subtract_nonfinite_iff {operands : FloatOperands} {left right : F64.Finite} {lhs rhs : ℚ}
    (converted : operands.convert? = some (left, right))
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs) :
    subtract operands = .error .nonfiniteResult ↔ overflowThreshold ≤ |lhs - rhs| :=
  Proofs.Languages.Python.Core.Binary64.subtract_nonfinite_iff converted leftValue rightValue

theorem mulFinite_ok_iff {left right result : F64.Finite} {lhs rhs : ℚ}
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs) :
    mulFinite? left right = some result ↔ |lhs * rhs| < overflowThreshold ∧
      result.val = F64.ofBits (roundSigned (left.val.signBit != right.val.signBit) |lhs * rhs|) :=
  Proofs.Languages.Python.Core.Binary64.mulFinite_ok_iff leftValue rightValue

theorem mulFinite_nearestEven {left right result : F64.Finite} {lhs rhs : ℚ}
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs)
    (multiplied : mulFinite? left right = some result) :
    result.val.signBit = (left.val.signBit != right.val.signBit) ∧
      NearestEven magnitude |lhs * rhs| (magnitudeBits result.val.bits).toNat :=
  Proofs.Languages.Python.Core.Binary64.mulFinite_nearestEven leftValue rightValue multiplied

theorem mulFinite_zero {left right : F64.Finite} {lhs rhs : ℚ}
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs)
    (zero : lhs * rhs = 0) :
    (mulFinite? left right).map (fun result => result.val.bits) =
      some (if left.val.signBit != right.val.signBit then 0x8000000000000000 else 0) :=
  Proofs.Languages.Python.Core.Binary64.mulFinite_zero leftValue rightValue zero

theorem multiply_ok_iff (operands : FloatOperands) (result : F64.Finite) :
    multiply operands = .ok result ↔ ∃ left right,
      operands.convert? = some (left, right) ∧ mulFinite? left right = some result :=
  Proofs.Languages.Python.Core.Binary64.multiply_ok_iff operands result

theorem multiply_conversion_overflow_iff (operands : FloatOperands) :
    multiply operands = .error .conversionOverflow ↔ operands.convert? = none :=
  Proofs.Languages.Python.Core.Binary64.multiply_conversion_overflow_iff operands

theorem multiply_nonfinite_iff {operands : FloatOperands} {left right : F64.Finite} {lhs rhs : ℚ}
    (converted : operands.convert? = some (left, right))
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs) :
    multiply operands = .error .nonfiniteResult ↔ overflowThreshold ≤ |lhs * rhs| :=
  Proofs.Languages.Python.Core.Binary64.multiply_nonfinite_iff converted leftValue rightValue

theorem trueDivide_zeroDivision_iff (numerator divisor : Int) :
    trueDivide numerator divisor = .error .zeroDivisionError ↔ divisor = 0 :=
  Proofs.Languages.Python.Core.Binary64.trueDivide_zeroDivision_iff numerator divisor

theorem trueDivide_overflow_iff (numerator divisor : Int) :
    trueDivide numerator divisor = .error .overflowError ↔
      divisor ≠ 0 ∧ overflowThreshold ≤ quotientMagnitude numerator divisor :=
  Proofs.Languages.Python.Core.Binary64.trueDivide_overflow_iff numerator divisor

theorem trueDivide_ok_iff (numerator divisor : Int) (result : F64.Finite) :
    trueDivide numerator divisor = .ok result ↔
      divisor ≠ 0 ∧ quotientMagnitude numerator divisor < overflowThreshold ∧
        result.val = F64.ofBits (roundSigned (quotientNegative numerator divisor) (quotientMagnitude numerator divisor)) :=
  Proofs.Languages.Python.Core.Binary64.trueDivide_ok_iff numerator divisor result

theorem trueDivide_nearestEven {numerator divisor : Int} {result : F64.Finite}
    (computed : trueDivide numerator divisor = .ok result) :
    result.val.signBit = quotientNegative numerator divisor ∧
      NearestEven magnitude |(numerator : ℚ) / (divisor : ℚ)|
        (magnitudeBits result.val.bits).toNat :=
  Proofs.Languages.Python.Core.Binary64.trueDivide_nearestEven computed

theorem divideFloat_conversion_overflow (operands : FloatOperands) (failed : operands.convert? = none) :
    divideFloat operands = .error .conversionOverflow :=
  Proofs.Languages.Python.Core.Binary64.divideFloat_conversion_overflow operands failed

theorem divideFloat_zeroDivision_iff {operands : FloatOperands} {left right : F64.Finite} {lhs rhs : ℚ}
    (converted : operands.convert? = some (left, right))
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs) :
    divideFloat operands = .error .zeroDivisionError ↔ rhs = 0 :=
  Proofs.Languages.Python.Core.Binary64.divideFloat_zeroDivision_iff converted leftValue rightValue

theorem divideFloat_nonfinite_iff {operands : FloatOperands} {left right : F64.Finite} {lhs rhs : ℚ}
    (converted : operands.convert? = some (left, right))
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs) :
    divideFloat operands = .error .nonfiniteResult ↔ rhs ≠ 0 ∧ overflowThreshold ≤ |lhs / rhs| :=
  Proofs.Languages.Python.Core.Binary64.divideFloat_nonfinite_iff converted leftValue rightValue

theorem divideFloat_ok_iff {operands : FloatOperands} {left right result : F64.Finite} {lhs rhs : ℚ}
    (converted : operands.convert? = some (left, right))
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs) :
    divideFloat operands = .ok result ↔ rhs ≠ 0 ∧ |lhs / rhs| < overflowThreshold ∧
      result.val = F64.ofBits (roundSigned (left.val.signBit != right.val.signBit) |lhs / rhs|) :=
  Proofs.Languages.Python.Core.Binary64.divideFloat_ok_iff converted leftValue rightValue

theorem divideFloat_nearestEven {operands : FloatOperands} {left right result : F64.Finite} {lhs rhs : ℚ}
    (converted : operands.convert? = some (left, right))
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs)
    (divided : divideFloat operands = .ok result) :
    result.val.signBit = (left.val.signBit != right.val.signBit) ∧
      NearestEven magnitude |lhs / rhs| (magnitudeBits result.val.bits).toNat :=
  Proofs.Languages.Python.Core.Binary64.divideFloat_nearestEven converted leftValue rightValue divided

end Silmaril.Languages.Python.Core.Binary64
