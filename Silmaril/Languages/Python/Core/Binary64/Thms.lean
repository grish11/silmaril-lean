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

end Silmaril.Languages.Python.Core.Binary64
