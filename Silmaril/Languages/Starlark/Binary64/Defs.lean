module

@[expose] public section

namespace Silmaril.Languages.Starlark.Binary64

/-- Clear the sign bit of an already encoded binary64 value. -/
def abs (bits : UInt64) : UInt64 := bits &&& 0x7fffffffffffffff

/-- Both signed zeros are false. All other encodings, including NaNs, are true. -/
def truth (bits : UInt64) : Bool := abs bits != 0

/-- The positive-sign encoding with the input's exponent and trailing significand. -/
def Absolute (input output : UInt64) : Prop :=
  output.toNat = input.toNat % 2 ^ 63

/-- Zero magnitude is the sole false case, regardless of the input's sign. -/
inductive Truth (input : UInt64) : Bool → Prop where
  | zero : input.toNat % 2 ^ 63 = 0 → Truth input false
  | nonzero : input.toNat % 2 ^ 63 ≠ 0 → Truth input true

/-- Exact numeric observations for comparison and dictionary keys. A finite value counts units
of the least positive subnormal, `2⁻¹⁰⁷⁴`. Signed zeros share one observation. -/
inductive Number where
  | negativeInfinity
  | finite (units : Int)
  | positiveInfinity
  | nan
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def Number.ofInt (value : Int) : Number := .finite (value * 2 ^ 1074)

structure Fields where
  negative : Bool
  exponent : Nat
  fraction : Nat

def fields (bits : UInt64) : Fields :=
  let magnitude := bits.toNat % 0x8000000000000000
  ⟨decide (0x8000000000000000 ≤ bits.toNat),
    magnitude / 0x10000000000000, magnitude % 0x10000000000000⟩

def signedUnits (negative : Bool) (magnitude : Nat) : Int :=
  if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude

def infinity (negative : Bool) : Number :=
  if negative then .negativeInfinity else .positiveInfinity

def decode (bits : UInt64) : Number :=
  let f := fields bits
  if f.exponent = 2047 then
    if f.fraction = 0 then infinity f.negative else .nan
  else if f.exponent = 0 then
    .finite (signedUnits f.negative f.fraction)
  else
    .finite (signedUnits f.negative ((0x10000000000000 + f.fraction) * 2 ^ (f.exponent - 1)))

/-- A reconstruction equation for the sign, exponent and fraction fields. -/
def Fields.Valid (f : Fields) (bits : UInt64) : Prop :=
  f.exponent < 2048 ∧ f.fraction < 0x10000000000000 ∧
    bits.toNat = (if f.negative then 0x8000000000000000 else 0) +
      f.exponent * 0x10000000000000 + f.fraction

inductive Decodes (bits : UInt64) : Number → Prop where
  | zeroOrSubnormal {f : Fields} : f.Valid bits → f.exponent = 0 →
      Decodes bits (.finite (signedUnits f.negative f.fraction))
  | normal {f : Fields} : f.Valid bits → 0 < f.exponent → f.exponent < 2047 →
      Decodes bits (.finite (signedUnits f.negative
        ((0x10000000000000 + f.fraction) * 2 ^ (f.exponent - 1))))
  | infinite {f : Fields} : f.Valid bits → f.exponent = 2047 → f.fraction = 0 →
      Decodes bits (infinity f.negative)
  | nan {f : Fields} : f.Valid bits → f.exponent = 2047 → f.fraction ≠ 0 →
      Decodes bits .nan

def Number.rank : Number → Nat
  | .negativeInfinity => 0
  | .finite _ => 1
  | .positiveInfinity => 2
  | .nan => 3

def compareNumbers : Number → Number → Ordering
  | .finite left, .finite right => compare left right
  | left, right => compare left.rank right.rank

/-- Starlark orders NaN above positive infinity and compares all NaNs equal. -/
def Number.Less : Number → Number → Prop
  | .negativeInfinity, .finite _ | .negativeInfinity, .positiveInfinity | .negativeInfinity, .nan => True
  | .finite left, .finite right => left < right
  | .finite _, .positiveInfinity | .finite _, .nan | .positiveInfinity, .nan => True
  | _, _ => False

def Orders (left right : Number) : Ordering → Prop
  | .lt => left.Less right
  | .eq => left = right
  | .gt => right.Less left

end Silmaril.Languages.Starlark.Binary64
