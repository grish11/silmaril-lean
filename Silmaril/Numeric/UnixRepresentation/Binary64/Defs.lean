module

public import Silmaril.Numeric.UnixRepresentation.Defs
public import Silmaril.Numeric.Ieee754.SignedRationalRounding
public import Mathlib.Data.Rat.Floor

/-! Checked conversions between binary64 payloads and ideal epoch-relative ticks. -/

@[expose] public section

namespace Silmaril.Numeric.UnixRepresentation.Binary64

open Timestamp Ieee754

inductive Error where
  | nonfinite
  | overflow
  | precisionLoss
  deriving DecidableEq, Repr

/-- The exact input offset, measured in ticks of the binary64 payload's unit. -/
def count {kind : Kind} {source : TickUnit} (value : Ticks kind source)
    (payloadUnit : TickUnit) : ℚ :=
  (value.denote.ticks : ℚ) / (payloadUnit.nanosecondsPerTick : ℚ)

/-- Decode to a rational destination tick count. Both signed zeros denote zero.
    Subnormals retain their exact dyadic value. NaNs and infinities yield none. -/
def decodeCount? (payload : F64) (payloadUnit target : TickUnit) : Option ℚ :=
  payload.toRat?.map fun x =>
    x * (payloadUnit.nanosecondsPerTick : ℚ) / (target.nanosecondsPerTick : ℚ)

/-- Decode and quantize to unbounded ticks. Fractional counts fail under exact rounding. -/
def decode (kind : Kind) (payload : F64) (payloadUnit target : TickUnit)
    (rounding : TickRounding := .exact) : Except Error (Ticks kind target) :=
  match decodeCount? payload payloadUnit target with
  | none => .error .nonfinite
  | some q =>
    match rounding with
    | .exact => if (⌊q⌋ : ℚ) = q then .ok ⟨⌊q⌋⟩ else .error .precisionLoss
    | .floor => .ok ⟨⌊q⌋⟩
    | .trunc => .ok ⟨if q < 0 then ⌈q⌉ else ⌊q⌋⟩

/-- Encode with one round-to-nearest, ties-to-even operation on the exact
    rational count. An infinity result is reported as overflow. Zero encodes
    as positive zero, and a negative count rounded to zero retains its sign. -/
def encodeRne {kind : Kind} {source : TickUnit} (value : Ticks kind source)
    (payloadUnit : TickUnit) : Except Error F64 :=
  let q := count value payloadUnit
  if RationalRounding.overflowThreshold ≤ |q| then .error .overflow
  else .ok (F64.ofBits (RationalRounding.roundRational q))

/-- Encode exactly, rejecting an in-range value whose rounded payload changes it. -/
def encodeExact {kind : Kind} {source : TickUnit} (value : Ticks kind source)
    (payloadUnit : TickUnit) : Except Error F64 :=
  match encodeRne value payloadUnit with
  | .error error => .error error
  | .ok payload =>
    if payload.toRat? = some (count value payloadUnit) then .ok payload
    else .error .precisionLoss

/-- The spacing of the binary64 interval bracketing the absolute input count.
    The upper end of the last interval is the virtual value 2^1024.
    The error theorem uses this spacing only below the overflow threshold. -/
def ulp (q : ℚ) : ℚ :=
  let lower := Bisection.lastLE RationalRounding.magnitude |q| 0 RationalRounding.limit
  BinaryMagnitude.spacing 52 1023 (lower / BinaryMagnitude.radix 52)

end Silmaril.Numeric.UnixRepresentation.Binary64
