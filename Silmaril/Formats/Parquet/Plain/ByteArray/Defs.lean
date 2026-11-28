module

public import Silmaril.Formats.Parquet.Plain.Defs

/-! Bounded PLAIN BYTE_ARRAY values. Each value has a four-byte little-endian
nonnegative signed-i32 length followed by its opaque octets. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray

structure Limits where
  /-- The entire encoded slice, including its length words. -/
  totalBytes : Nat
  /-- The payload length of any individual value. -/
  valueBytes : Nat
  deriving DecidableEq, Repr

def lengthLimit : Nat := 2 ^ 31

def valueWire (value : Bytes) : List UInt8 :=
  KBytes.unpack 4 value.length ++ value.toList

def wire (values : List Bytes) : List UInt8 := values.flatMap valueWire

def encodedSize (values : List Bytes) : Nat :=
  (values.map fun value => 4 + value.length).sum

/-- Validate every value and the total encoded extent before allocating output. -/
def encode (limits : Limits) (values : List Bytes) : Except Error Bytes :=
  if values.any (fun value => lengthLimit ≤ value.length) then .error .integerOverflow
  else if values.any (fun value => limits.valueBytes < value.length) then .error .valueByteLimit
  else if limits.totalBytes < encodedSize values then .error .totalByteLimit
  else .ok (Bytes.ofList (wire values))

namespace Internal

/-- The caller maintains the exact length of the source suffix. -/
def readOne (valueLimit remaining : Nat) (source : List UInt8) :
    Except Error (Bytes × List UInt8) :=
  if remaining < 4 then .error .truncated
  else
    let size := KBytes.leVal (source.take 4)
    if lengthLimit ≤ size then .error .integerOverflow
    else if valueLimit < size then .error .valueByteLimit
    else if remaining < 4 + size then .error .truncated
    else
      let tail := source.drop 4
      .ok (Bytes.ofList (tail.take size), tail.drop size)

def decodeLoop (valueLimit : Nat) :
    Nat → Nat → List UInt8 → List Bytes → Except Error (List Bytes)
  | 0, remaining, _, reversed =>
    if remaining = 0 then .ok reversed.reverse else .error .trailingBytes
  | count + 1, remaining, source, reversed => do
    let (value, suffix) ← readOne valueLimit remaining source
    decodeLoop valueLimit count (remaining - (4 + value.length)) suffix (value :: reversed)

end Internal

/-- Read exactly `count` values and consume the entire bounded slice. -/
def decode (limits : Limits) (count : Nat) (source : Bytes) : Except Error (List Bytes) :=
  if limits.totalBytes < source.length then .error .totalByteLimit
  else Internal.decodeLoop limits.valueBytes count source.length source.toList []

end Silmaril.Formats.Parquet.Plain.ByteArray
