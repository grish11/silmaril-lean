module

public import Silmaril.Languages.Python.Core.Binary64.Defs
import Silmaril.Proofs.Languages.Python.Core.Binary64.Division

public section
namespace Silmaril.Proofs.Languages.Python.Core.Binary64

open Silmaril.Languages.Python.Core.Binary64
open Silmaril.Numeric.Ieee754 (F64)
open Silmaril.Numeric.Ieee754.AdjacentRounding (NearestEven)
open Silmaril.Numeric.Ieee754.RationalRounding
open Silmaril.Numeric.Ieee754.Binary64Signs (magnitudeBits)

theorem intToFinite_none_iff (integer : Int) :
    intToFinite? integer = none ↔ overflowThreshold ≤ (integer.natAbs : ℚ) := by
  rw [← not_lt, ← rounded_finite_iff (decide (integer < 0))
    (Nat.cast_nonneg integer.natAbs : 0 ≤ (_ : ℚ))]
  unfold intToFinite? F64.Finite.ofRaw?
  split
  next finite =>
    constructor
    · intro impossible
      cases impossible
    · intro invalid
      exact (invalid finite).elim
  next invalid => exact ⟨fun _ => invalid, fun _ => rfl⟩

theorem intToFinite_nearestEven {integer : Int} {result : F64.Finite}
    (converted : intToFinite? integer = some result) :
    result.val.signBit = decide (integer < 0) ∧
      NearestEven magnitude (integer.natAbs : ℚ) (magnitudeBits result.val.bits).toNat := by
  unfold intToFinite? F64.Finite.ofRaw? at converted
  split at converted
  next finite =>
    cases converted
    exact ⟨signBit_roundSigned _ _, (roundSigned_nearestEven _ _ (Nat.cast_nonneg _)
      ((rounded_finite_iff _ (Nat.cast_nonneg _)).mp finite)).2⟩
  next => cases converted

theorem addFinite_none_iff {left right : F64.Finite} {lhs rhs : ℚ}
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs) :
    addFinite? left right = none ↔ overflowThreshold ≤ |lhs + rhs| := by
  have finite := rounded_finite_iff (sumNegative left right (lhs + rhs)) (abs_nonneg (lhs + rhs))
  by_cases below : |lhs + rhs| < overflowThreshold
  · simp [addFinite?, leftValue, rightValue, F64.Finite.ofRaw?, finite.mpr below, not_le_of_gt below]
  · simp [addFinite?, leftValue, rightValue, F64.Finite.ofRaw?, mt finite.mp below, le_of_not_gt below]

theorem addFinite_nearestEven {left right result : F64.Finite} {lhs rhs : ℚ}
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs)
    (added : addFinite? left right = some result) :
    result.val.signBit = sumNegative left right (lhs + rhs) ∧
      NearestEven magnitude |lhs + rhs| (magnitudeBits result.val.bits).toNat := by
  unfold addFinite? at added
  rw [leftValue, rightValue] at added
  change F64.Finite.ofRaw? (F64.ofBits (roundSigned (sumNegative left right (lhs + rhs)) |lhs + rhs|)) =
    some result at added
  unfold F64.Finite.ofRaw? at added
  split at added
  next finite =>
    cases added
    exact ⟨signBit_roundSigned _ _, (roundSigned_nearestEven _ _ (abs_nonneg _)
      ((rounded_finite_iff _ (abs_nonneg _)).mp finite)).2⟩
  next => cases added

theorem addFinite_comm (left right : F64.Finite) : addFinite? left right = addFinite? right left := by
  cases hl : left.val.toRat? <;> cases hr : right.val.toRat? <;>
    simp [addFinite?, hl, hr, sumNegative, add_comm, Bool.and_comm]

theorem addFinite_zero {left right : F64.Finite} {lhs rhs : ℚ}
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs)
    (zero : lhs + rhs = 0) :
    (addFinite? left right).map (fun result => result.val.bits) =
      some (if left.val.signBit && right.val.signBit then 0x8000000000000000 else 0) := by
  cases sign : (left.val.signBit && right.val.signBit) <;>
    simp [addFinite?, leftValue, rightValue, zero, sumNegative, sign, F64.Finite.ofRaw?] <;> decide

theorem addFinite_subnormal {left right : F64.Finite} {lhs rhs : ℚ} {index : Nat}
    (leftValue : left.val.toRat? = some lhs) (rightValue : right.val.toRat? = some rhs)
    (positive : 0 < index) (subnormal : index < 2 ^ 52)
    (sum : |lhs + rhs| = magnitude index) :
    (addFinite? left right).map (fun result => (magnitudeBits result.val.bits).toNat) = some index := by
  have bound : index ≤ limit - 1 := by
    unfold limit
    omega
  have below : magnitude index < overflowThreshold :=
    (magnitude_strictMono.monotone bound).trans_lt maxFinite_lt_overflowThreshold
  have encoded : (UInt64.ofNat index).toNat = index := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    exact subnormal.trans (by decide)
  have inRange : (UInt64.ofNat index).toNat ≤ 0x7fefffffffffffff := by
    rw [encoded]
    omega
  have fixedPoint := Silmaril.Numeric.Ieee754.Decimal.rational_roundtrips (UInt64.ofNat index)
    (by rwa [encoded]) inRange
  rw [Silmaril.Numeric.Ieee754.Decimal.rational_eq_binaryMagnitude _ inRange, encoded] at fixedPoint
  change roundPositive (magnitude index) = _ at fixedPoint
  have finite := (rounded_finite_iff (sumNegative left right (lhs + rhs))
    (abs_nonneg (lhs + rhs))).mpr (sum.symm ▸ below)
  unfold addFinite?
  rw [leftValue, rightValue]
  change (F64.Finite.ofRaw? (F64.ofBits (roundSigned (sumNegative left right (lhs + rhs)) |lhs + rhs|))).map
    (fun result => (magnitudeBits result.val.bits).toNat) = some index
  rw [F64.Finite.ofRaw?, dite_eq_left finite]
  change some (magnitudeBits (roundSigned (sumNegative left right (lhs + rhs)) |lhs + rhs|)).toNat = some index
  rw [magnitudeBits_roundSigned, sum, fixedPoint, encoded]

theorem mixedAdd_conversion_overflow_iff (integer : Int) (floating : F64.Finite) :
    mixedAdd integer floating = .error .conversionOverflow ↔ overflowThreshold ≤ (integer.natAbs : ℚ) := by
  rw [← intToFinite_none_iff]
  unfold mixedAdd
  cases intToFinite? integer with
  | none => simp
  | some converted => cases sum : addFinite? converted floating <;> simp [sum]

theorem mixedAdd_ok_iff (integer : Int) (floating result : F64.Finite) :
    mixedAdd integer floating = .ok result ↔
      ∃ converted, intToFinite? integer = some converted ∧ addFinite? converted floating = some result := by
  cases coercion : intToFinite? integer with
  | none => simp [mixedAdd, coercion]
  | some converted => cases sum : addFinite? converted floating <;> simp [mixedAdd, coercion, sum]

theorem mixedAdd_nonfinite_iff {integer : Int} {floating converted : F64.Finite} {lhs rhs : ℚ}
    (coercion : intToFinite? integer = some converted)
    (leftValue : converted.val.toRat? = some lhs) (rightValue : floating.val.toRat? = some rhs) :
    mixedAdd integer floating = .error .nonfiniteResult ↔ overflowThreshold ≤ |lhs + rhs| := by
  rw [← addFinite_none_iff leftValue rightValue]
  simp only [mixedAdd, coercion]
  cases addFinite? converted floating <;> simp

end Silmaril.Proofs.Languages.Python.Core.Binary64
