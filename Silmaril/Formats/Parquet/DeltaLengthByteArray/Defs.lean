module

public import Silmaril.Formats.Parquet.DeltaBinaryPacked.Defs

/-! DELTA_LENGTH_BYTE_ARRAY over one exact scalar slice. Values are opaque bytes. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.DeltaLengthByteArray

structure Limits where
  /-- The delta byte cap applies to the whole encoded slice, including the values. -/
  lengths : DeltaBinaryPacked.Limits
  /-- Maximum total byte extent of the concatenated values. -/
  payloadBytes : Nat
  /-- Maximum length of one decoded value. -/
  valueBytes : Nat
  deriving DecidableEq, Repr

inductive Error where
  | lengths (error : DeltaBinaryPacked.Error)
  | negativeLength (length : Int32)
  | payloadLimit
  | valueLimit
  | truncated
  | trailingBytes
  deriving DecidableEq, Repr

/-- The signed length list matches the output sizes and the payload is exactly
those values concatenated in wire order. -/
structure Assembled (limits : Limits) (lengths : List Int32) (source : List UInt8)
    (values : List Bytes) : Prop where
  payloadLimit : source.length ≤ limits.payloadBytes
  sizes : lengths.map Int32.toInt = values.map (fun value => (value.length : Int))
  wire : source = values.flatMap Bytes.toList
  valueLimit : ∀ value ∈ values, value.length ≤ limits.valueBytes

namespace Internal

def readOne (limit : Nat) (length : Int32) (source : List UInt8) :
    Except Error (Bytes × List UInt8) :=
  if length.toInt < 0 then .error (.negativeLength length)
  else
    let size := length.toInt.toNat
    if limit < size then .error .valueLimit
    else
      match Hybrid.takeExact size source with
      | .error _ => .error .truncated
      | .ok (bytes, rest) => .ok (Bytes.ofList bytes, rest)

def readValues (limit : Nat) : List Int32 → List UInt8 → List Bytes → Except Error (List Bytes)
  | [], [], reversed => .ok reversed.reverse
  | [], _ :: _, _ => .error .trailingBytes
  | length :: lengths, source, reversed => do
    let (value, rest) ← readOne limit length source
    readValues limit lengths rest (value :: reversed)

end Internal

/-- Partition an exact value suffix according to its checked signed lengths. -/
def assemble (limits : Limits) (lengths : List Int32) (source : List UInt8) :
    Except Error (List Bytes) :=
  if limits.payloadBytes < source.length then .error .payloadLimit
  else Internal.readValues limits.valueBytes lengths source []

/-- Decode the INT32 length prefix, then consume exactly the concatenated values. -/
def decode (limits : Limits) (expected : Nat) (source : Bytes) : Except Error (List Bytes) := do
  let (lengthStream, payload) ←
    (DeltaBinaryPacked.parsePrefix .int32 limits.lengths expected source).mapError Error.lengths
  assemble limits (lengthStream.reconstruct .int32) payload

end Silmaril.Formats.Parquet.DeltaLengthByteArray
