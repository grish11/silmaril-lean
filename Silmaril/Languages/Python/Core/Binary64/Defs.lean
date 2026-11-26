module

public import Silmaril.Numeric.Ieee754.SignedRationalRounding

/-! # Python finite binary64

Round exact integer quotients, decimal literals and finite sums. The sign
is separate so arithmetic and literal conversion can retain negative zero.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Core.Binary64

open Silmaril.Numeric.Ieee754 (F64)
open Silmaril.Numeric.Ieee754.RationalRounding (roundSigned)

/-- Exact nonnegative value of a decimal coefficient and power of ten. -/
def decimalMagnitude (coefficient : Nat) (exponent : Int) : ℚ :=
  (coefficient : ℚ) * (10 : ℚ) ^ exponent

/-- Bound the size of an input to rational conversion before exponentiation. -/
def decimalInProfile (coefficient : Nat) (exponent : Int) : Prop :=
  coefficient.log2 ≤ 4096 ∧ exponent.natAbs ≤ 4096

instance (coefficient : Nat) (exponent : Int) : Decidable (decimalInProfile coefficient exponent) := by
  unfold decimalInProfile
  infer_instance

/-- Convert a bounded decimal value, admitting only finite binary64 encodings. -/
def ofDecimal? (negative : Bool) (coefficient : Nat) (exponent : Int) : Option F64.Finite :=
  if decimalInProfile coefficient exponent then
    F64.Finite.ofRaw? (F64.ofBits (roundSigned negative (decimalMagnitude coefficient exponent)))
  else none

/-- Compare finite numbers by their exact dyadic values. -/
def equal (left right : F64.Finite) : Bool := decide (left.val.toRat? = right.val.toRat?)

/-- Compare a finite number to an integer without rounding the integer. -/
def equalInt (left : F64.Finite) (right : Int) : Bool := decide (left.val.toRat? = some (right : ℚ))

/-- The exact tags and values participating in numeric equality. -/
inductive NumericOperand where
  | integer (value : Int)
  | float64 (value : F64.Finite)
  deriving DecidableEq, Repr

def NumericOperand.equal : NumericOperand → NumericOperand → Bool
  | .integer left, .integer right => decide (left = right)
  | .float64 left, .float64 right => Binary64.equal left right
  | .float64 left, .integer right => equalInt left right
  | .integer left, .float64 right => equalInt right left

/-- CPython's mixed arithmetic first converts the exact integer to binary64. -/
def intToFinite? (integer : Int) : Option F64.Finite :=
  F64.Finite.ofRaw? (F64.ofBits (roundSigned (decide (integer < 0)) (integer.natAbs : ℚ)))

/-- A zero sum is negative only for two negative zeros under nearest-even. -/
def sumNegative (left right : F64.Finite) (sum : ℚ) : Bool :=
  decide (sum < 0) || (decide (sum = 0) && (left.val.signBit && right.val.signBit))

/-- Round the exact dyadic sum once. The finite profile excludes overflow. -/
def addFinite? (left right : F64.Finite) : Option F64.Finite := do
  let lhs ← left.val.toRat?
  let rhs ← right.val.toRat?
  let sum := lhs + rhs
  F64.Finite.ofRaw? (F64.ofBits (roundSigned (sumNegative left right sum) |sum|))

inductive MixedAddError where
  | conversionOverflow
  | nonfiniteResult
  deriving DecidableEq, Repr

/-- Coercion overflow is a defined exception. A nonfinite sum is outside
the checked result profile. -/
def mixedAdd (integer : Int) (floating : F64.Finite) : Except MixedAddError F64.Finite :=
  match intToFinite? integer with
  | none => .error .conversionOverflow
  | some converted => (addFinite? converted floating).elim (.error .nonfiniteResult) .ok

inductive DivisionError where
  | zeroDivisionError
  | overflowError
  deriving DecidableEq, Repr

def quotientMagnitude (numerator divisor : Int) : ℚ :=
  (numerator.natAbs : ℚ) / (divisor.natAbs : ℚ)

def quotientNegative (numerator divisor : Int) : Bool :=
  decide (numerator < 0) != decide (divisor < 0)

/-- Python's integer `/` returns a finite float, or raises if the divisor
is zero or rounding reaches infinity. -/
def trueDivide (numerator divisor : Int) : Except DivisionError F64.Finite :=
  if divisor = 0 then .error .zeroDivisionError
  else
    let bits := roundSigned (quotientNegative numerator divisor) (quotientMagnitude numerator divisor)
    match F64.Finite.ofRaw? (F64.ofBits bits) with
    | some result => .ok result
    | none => .error .overflowError

end Silmaril.Languages.Python.Core.Binary64
