module

public import Silmaril.Formats.Parquet.DeltaLengthByteArray.Defs

/-! DELTA_BYTE_ARRAY over an exact BYTE_ARRAY scalar slice starting with an empty predecessor. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.DeltaByteArray

structure Limits where
  /-- The outer byte cap includes both substreams. -/
  prefixes : DeltaBinaryPacked.Limits
  suffixes : DeltaLengthByteArray.Limits
  /-- Maximum size of a reconstructed value, including the copied prefix. -/
  valueBytes : Nat
  /-- Maximum sum of the reconstructed value sizes. -/
  decodedBytes : Nat
  deriving DecidableEq, Repr

inductive Error where
  | prefixStream (error : DeltaBinaryPacked.Error)
  | suffixStream (error : DeltaLengthByteArray.Error)
  | nonzeroFirstPrefix
  | negativePrefix (length : Int32)
  | prefixTooLong
  | valueOverflow
  | valueLimit
  | decodedByteLimit
  | countMismatch
  deriving DecidableEq, Repr

def valueLengthLimit : Nat := 2 ^ 31

/-- The decoded value starts with the claimed prefix of its predecessor and
ends with the complete decoded suffix. -/
structure Joined (valueLimit budget : Nat) (previous : Bytes) (prefixLength : Int32)
    (suffix value : Bytes) : Prop where
  nonnegative : 0 ≤ prefixLength.toInt
  prefixFits : prefixLength.toInt.toNat ≤ previous.length
  wire : value.toList = previous.toList.take prefixLength.toInt.toNat ++ suffix.toList
  representable : value.length < valueLengthLimit
  limit : value.length ≤ valueLimit
  budgetFits : value.length ≤ budget

/-- Each step passes the reconstructed value and the remaining byte budget to
its successor. Both input lists must be consumed in full. -/
inductive Reconstruction (valueLimit : Nat) :
    Nat → Bytes → List Int32 → List Bytes → List Bytes → Prop where
  | done (budget : Nat) (previous : Bytes) : Reconstruction valueLimit budget previous [] [] []
  | next {budget : Nat} {previous suffix value : Bytes} {prefixLength : Int32}
      {prefixes : List Int32} {suffixes values : List Bytes}
      (joined : Joined valueLimit budget previous prefixLength suffix value)
      (tail : Reconstruction valueLimit (budget - value.length) value prefixes suffixes values) :
      Reconstruction valueLimit budget previous (prefixLength :: prefixes) (suffix :: suffixes) (value :: values)

namespace Internal

/-- Check the combined size before allocating the output. Nat arithmetic covers
both the signed-i32 boundary and the cumulative byte budget. -/
def checkSize (limit budget prefixBytes suffixBytes : Nat) : Except Error Unit :=
  let size := prefixBytes + suffixBytes
  if valueLengthLimit ≤ size then .error .valueOverflow
  else if limit < size then .error .valueLimit
  else if budget < size then .error .decodedByteLimit
  else .ok ()

def extend (limit budget : Nat) (previous : Bytes) (prefixLength : Int32) (suffix : Bytes) :
    Except Error Bytes :=
  if prefixLength.toInt < 0 then .error (.negativePrefix prefixLength)
  else
    let count := prefixLength.toInt.toNat
    if previous.length < count then .error .prefixTooLong
    else do
      checkSize limit budget count suffix.length
      pure (.ofList (previous.toList.take count ++ suffix.toList))

def loop (limit : Nat) : Nat → Bytes → List Int32 → List Bytes → List Bytes →
    Except Error (List Bytes)
  | _, _, [], [], reversed => .ok reversed.reverse
  | budget, previous, prefixLength :: prefixes, suffix :: suffixes, reversed => do
    let value ← extend limit budget previous prefixLength suffix
    loop limit (budget - value.length) value prefixes suffixes (value :: reversed)
  | _, _, _, _, _ => .error .countMismatch

end Internal

/-- Rebuild one complete scalar stream from its prefixes and suffixes. -/
def reconstruct (limits : Limits) (prefixes : List Int32) (suffixes : List Bytes) :
    Except Error (List Bytes) :=
  if prefixes.headD 0 ≠ 0 then .error .nonzeroFirstPrefix
  else Internal.loop limits.valueBytes limits.decodedBytes .empty prefixes suffixes []

/-- Both substreams declare the same supplied count. The suffix reader consumes
its entire slice before previous-value reconstruction begins. -/
def decode (limits : Limits) (expected : Nat) (source : Bytes) : Except Error (List Bytes) := do
  let (prefixStream, suffixSource) ←
    (DeltaBinaryPacked.parsePrefix .int32 limits.prefixes expected source).mapError Error.prefixStream
  let suffixes ←
    (DeltaLengthByteArray.decode limits.suffixes expected (.ofList suffixSource)).mapError Error.suffixStream
  reconstruct limits (prefixStream.reconstruct .int32) suffixes

end Silmaril.Formats.Parquet.DeltaByteArray
