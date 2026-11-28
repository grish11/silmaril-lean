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
def sumSign (leftNegative rightNegative : Bool) (sum : ℚ) : Bool :=
  decide (sum < 0) || (decide (sum = 0) && (leftNegative && rightNegative))

def sumNegative (left right : F64.Finite) (sum : ℚ) : Bool :=
  sumSign left.val.signBit right.val.signBit sum

def roundExact? (negative : Bool) (value : ℚ) : Option F64.Finite :=
  F64.Finite.ofRaw? (F64.ofBits (roundSigned negative |value|))

def roundSum? (leftNegative rightNegative : Bool) (sum : ℚ) : Option F64.Finite :=
  roundExact? (sumSign leftNegative rightNegative sum) sum

/-- Round the exact dyadic sum once. The finite profile excludes overflow. -/
def addFinite? (left right : F64.Finite) : Option F64.Finite := do
  let lhs ← left.val.toRat?
  let rhs ← right.val.toRat?
  roundSum? left.val.signBit right.val.signBit (lhs + rhs)

/-- Negate the exact right addend and invert its sign, including for zero. -/
def subFinite? (left right : F64.Finite) : Option F64.Finite := do
  let lhs ← left.val.toRat?
  let rhs ← right.val.toRat?
  roundSum? left.val.signBit (!right.val.signBit) (lhs - rhs)

/-- Round the exact dyadic product once, keeping XOR of the input signs
even when the product is zero or rounds to zero. -/
def mulFinite? (left right : F64.Finite) : Option F64.Finite := do
  let lhs ← left.val.toRat?
  let rhs ← right.val.toRat?
  roundExact? (left.val.signBit != right.val.signBit) (lhs * rhs)

/-- Conversion and result errors shared by floating-point arithmetic. -/
inductive MixedAddError where
  | conversionOverflow
  | nonfiniteResult
  deriving DecidableEq, Repr

abbrev FloatArithmeticError := MixedAddError

/-- Coercion overflow is a defined exception. A nonfinite sum is outside
the checked result profile. -/
def mixedAdd (integer : Int) (floating : F64.Finite) : Except MixedAddError F64.Finite :=
  match intToFinite? integer with
  | none => .error .conversionOverflow
  | some converted => (addFinite? converted floating).elim (.error .nonfiniteResult) .ok

/-- Ordered exact operands with at least one finite float. -/
inductive FloatOperands where
  | intFloat (left : Int) (right : F64.Finite)
  | floatInt (left : F64.Finite) (right : Int)
  | floatFloat (left right : F64.Finite)

def FloatOperands.convert? : FloatOperands → Option (F64.Finite × F64.Finite)
  | .intFloat left right => (intToFinite? left).map (·, right)
  | .floatInt left right => (intToFinite? right).map (left, ·)
  | .floatFloat left right => some (left, right)

/-- Convert the integer, if any, before evaluating the finite operation. -/
def FloatOperands.evaluate (operands : FloatOperands) (operation : F64.Finite → F64.Finite → Option F64.Finite) :
    Except FloatArithmeticError F64.Finite :=
  match operands.convert? with
  | none => .error .conversionOverflow
  | some (left, right) => (operation left right).elim (.error .nonfiniteResult) .ok

def subtract (operands : FloatOperands) : Except FloatArithmeticError F64.Finite :=
  operands.evaluate subFinite?

def multiply (operands : FloatOperands) : Except FloatArithmeticError F64.Finite :=
  operands.evaluate mulFinite?

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

inductive FloatDivisionError where
  | conversionOverflow
  | zeroDivisionError
  | nonfiniteResult
  deriving DecidableEq, Repr

/-- CPython converts an integer operand before testing the binary64 divisor
for zero. The finite profile rounds the exact ratio once. -/
def divideFloat (operands : FloatOperands) : Except FloatDivisionError F64.Finite := do
  let some (left, right) := operands.convert? | .error .conversionOverflow
  let some lhs := left.val.toRat? | .error .nonfiniteResult
  let some rhs := right.val.toRat? | .error .nonfiniteResult
  if rhs = 0 then .error .zeroDivisionError
  else (roundExact? (left.val.signBit != right.val.signBit) (lhs / rhs)).elim (.error .nonfiniteResult) .ok

/-- Encode an exact representable value and verify its decoded value. -/
def encodeExact? (negative : Bool) (value : ℚ) : Option F64.Finite :=
  (roundExact? negative value).filter fun result => result.val.toRat? == some value

/-- The remainder for truncation toward zero, before Python's sign adjustment. -/
def truncatingRemainder (lhs rhs : ℚ) : ℚ :=
  let divisor := |rhs|
  let quotient := (|lhs| / divisor).floor
  let magnitude := |lhs| - (quotient : ℚ) * divisor
  if lhs < 0 then -magnitude else magnitude

def fmodFinite? (left right : F64.Finite) : Option F64.Finite := do
  let lhs ← left.val.toRat?
  let rhs ← right.val.toRat?
  if rhs = 0 then none else encodeExact? left.val.signBit (truncatingRemainder lhs rhs)

/-- The correction uses the signs of the divisor and nonzero raw remainder. -/
def needsDivModCorrection (right remainder : F64.Finite) (value : ℚ) : Bool :=
  decide (value ≠ 0) && (right.val.signBit != remainder.val.signBit)

def signRemainder? (right remainder : F64.Finite) (value : ℚ) : Option F64.Finite :=
  if value = 0 then roundExact? right.val.signBit 0
  else if needsDivModCorrection right remainder value then addFinite? remainder right
  else some remainder

def divModOne : F64.Finite := ⟨F64.ofBits 0x3ff0000000000000, by decide⟩

/-- Snap CPython's rounded quotient to an integral float. The fractional
test itself uses rounded subtraction and a strict comparison with one half. -/
def snapQuotient? (negative : Bool) (quotient : F64.Finite) : Option F64.Finite := do
  let value ← quotient.val.toRat?
  if value = 0 then roundExact? negative 0
  else
    let floor := value.floor
    let integral ← encodeExact? (decide (floor < 0)) (floor : ℚ)
    let fraction ← subFinite? quotient integral
    let delta ← fraction.val.toRat?
    if delta > 1 / 2 then addFinite? integral divModOne else some integral

/-- CPython forms a rounded difference before dividing. It subtracts one
from that binary64 quotient when the remainder's sign needs correction. -/
def floorQuotient? (left right remainder : F64.Finite) (adjust : Bool) :
    Option F64.Finite := do
  let rhs ← right.val.toRat?
  (subFinite? left remainder).bind fun difference => do
    let delta ← difference.val.toRat?
    let negative := left.val.signBit != right.val.signBit
    let quotient ← roundExact? (difference.val.signBit != right.val.signBit) (delta / rhs)
    let corrected := if adjust then subFinite? quotient divModOne else some quotient
    corrected.bind (snapQuotient? negative)

inductive FloatDivModOp where
  | floorDiv
  | modulo

def FloatDivModOp.finite? (op : FloatDivModOp) (left right : F64.Finite) :
    Option F64.Finite := do
  let remainder ← fmodFinite? left right
  let value ← remainder.val.toRat?
  match op with
  | .floorDiv => floorQuotient? left right remainder (needsDivModCorrection right remainder value)
  | .modulo => signRemainder? right remainder value

/-- Finite-operand CPython float floor division and modulo. Modulo does
not compute a quotient, so quotient overflow does not restrict it. -/
def FloatDivModOp.eval (op : FloatDivModOp) (operands : FloatOperands) :
    Except FloatDivisionError F64.Finite := do
  let some (left, right) := operands.convert? | .error .conversionOverflow
  let some rhs := right.val.toRat? | .error .nonfiniteResult
  if rhs = 0 then .error .zeroDivisionError
  else (op.finite? left right).elim (.error .nonfiniteResult) .ok

end Silmaril.Languages.Python.Core.Binary64
