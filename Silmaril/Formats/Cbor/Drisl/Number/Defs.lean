module

public import Silmaril.Formats.Cbor.Drisl.Ast.Defs

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl

def intDecimal : Int → JsonWire.Decimal
  | .ofNat value => ⟨false, value, 0⟩
  | .negSucc argument => ⟨true, argument + 1, 0⟩

def Integer.toInt : Integer → Int
  | .uint argument => .ofNat argument.toNat
  | .nint argument => .negSucc argument.toNat

def Integer.ofInt? : Int → Option Integer
  | .ofNat value => if value < 2 ^ 64 then some (.uint (UInt64.ofNat value)) else none
  | .negSucc argument => if argument < 2 ^ 64 then some (.nint (UInt64.ofNat argument)) else none

def Integer.ofInt64 (value : Int64) : Integer :=
  match value.toInt with
  | .ofNat amount => .uint (UInt64.ofNat amount)
  | .negSucc amount => .nint (UInt64.ofNat amount)

def int64? (value : Int) : Option Int64 :=
  if -(2 ^ 63 : Int) ≤ value ∧ value < 2 ^ 63 then some (Int64.ofInt value) else none

def exactInt? (value : JsonWire.Decimal) : Option Int :=
  if value.negative && value.coefficient == 0 then none else
  if value.coefficient != 0 && value.exponent > 20 then none else value.toInt?

def decimalI64? (value : JsonWire.Decimal) : Option Int64 :=
  (exactInt? value).bind int64?

def floatExponent (bits : Nat) : Nat := bits / 2 ^ 52 % 2048

def floatScaleFactor (exp : Nat) : Nat :=
  2 ^ (if exp = 0 then 973 else 972 : Nat) * 5 ^ (2047 - exp)

/-- Exact decimal spelling of a finite double. Use decimal scale `2047 - exp`
to carry the exponent field in the spelling, and a distinguishable number
token even for integral doubles. The coefficient is the significand times
`2^(scale + binaryExponent) * 5^scale`. No floating arithmetic is used. -/
def floatDecimal (bits : Float64Bits) : JsonWire.Decimal :=
  let exp := floatExponent bits.val
  let fraction := bits.val % 2 ^ 52
  let significand := if exp = 0 then fraction else 2 ^ 52 + fraction
  ⟨decide (2 ^ 63 ≤ bits.val), significand * floatScaleFactor exp, -(2047 - (exp : Int))⟩

def readFloatDecimal? (value : JsonWire.Decimal) : Option Float64Bits := do
  if ¬ (-(2047 : Int) ≤ value.exponent ∧ value.exponent ≤ -1) then none else
  let exp := (2047 + value.exponent).toNat
  let factor := floatScaleFactor exp
  if value.coefficient % factor ≠ 0 then none else
  let significand := value.coefficient / factor
  if ¬ (if exp = 0 then significand < 2 ^ 52 else 2 ^ 52 ≤ significand ∧ significand < 2 ^ 53)
    then none else
  let fraction := if exp = 0 then significand else significand - 2 ^ 52
  let bits := (if value.negative then 2 ^ 63 else 0) + exp * 2 ^ 52 + fraction
  if valid : okFloat64 bits = true then some ⟨bits, valid⟩ else none

def Number.toDecimal : Number → JsonWire.Decimal
  | .integer value => intDecimal value.toInt
  | .float bits => floatDecimal bits

/-- An exact, potentially subnormal double on the `2^-1074` dyadic grid. -/
def floatOfGrid? (negative : Bool) (grid : Nat) : Option Float64Bits := do
  let shift := grid.log2 - 52
  let scale := 2 ^ shift
  if grid % scale != 0 then none else
  let exponent := if grid < 2 ^ 52 then 0 else shift + 1
  if exponent ≥ 2047 then none else
  let bits := (if negative then 2 ^ 63 else 0) + exponent * 2 ^ 52 + grid / scale % 2 ^ 52
  if valid : okFloat64 bits = true then some ⟨bits, valid⟩ else none

/-- Lower by exact numerical value, not by the debug marker spelling. Prefer
integers, and reject out-of-profile integral decimals even if a double could
encode them. For fractional decimals, divisibility on the entire subnormal
grid and then on the local float grid is required; never round. -/
def Number.ofDecimal? (value : JsonWire.Decimal) : Option Number := do
  if value.negative && value.coefficient == 0 then none else
  if value.coefficient != 0 && value.exponent > 20 then none else
  match value.toInt? with
  | some integral => .integer <$> Integer.ofInt? integral
  | none =>
    let scale := value.exponent.natAbs
    if scale > value.coefficient.repr.length + 324 then none else
    let numerator := value.coefficient * 2 ^ 1074
    let denominator := 10 ^ scale
    if numerator % denominator != 0 then none else
    .float <$> floatOfGrid? value.negative (numerator / denominator)

/-- Prefer the typed debug spelling, then accept ordinary decimal spellings
when they can be converted exactly under `Number.ofDecimal?`. -/
def Number.readDecimal? (value : JsonWire.Decimal) : Option Number :=
  if value.exponent = 0 then
    .integer <$> ((exactInt? value).bind Integer.ofInt?)
  else match readFloatDecimal? value with
    | some bits => some (.float bits)
    | none => Number.ofDecimal? value

end Silmaril.Formats.Cbor.Drisl
