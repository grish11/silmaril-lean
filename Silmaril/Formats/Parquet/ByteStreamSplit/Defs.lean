module

public import Silmaril.Formats.Parquet.Plain.Defs
import Init.Omega

/-! Bounded BYTE_STREAM_SPLIT over an exact physical-value slice. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ByteStreamSplit

structure Limits where
  values : Nat
  bytes : Nat
  width : Nat
  deriving DecidableEq, Repr

inductive Kind where
  | int32 | int64 | floatBits | doubleBits | fixedLenBytes (width : Nat)
  deriving DecidableEq, Repr

def Kind.width : Kind → Nat
  | .int32 | .floatBits => 4
  | .int64 | .doubleBits => 8
  | .fixedLenBytes width => width

abbrev Kind.Value : Kind → Type
  | .int32 => Int32
  | .int64 => Int64
  | .floatBits => UInt32
  | .doubleBits => UInt64
  | .fixedLenBytes _ => Bytes

/-- Interpret the reconstructed word with the existing PLAIN physical readers. -/
def Kind.readWord : (kind : Kind) → List UInt8 → kind.Value
  | .int32 => fun word => (Plain.readUInt32Word word).toInt32
  | .int64 => fun word => (Plain.readUInt64Word word).toInt64
  | .floatBits => Plain.readUInt32Word
  | .doubleBits => Plain.readUInt64Word
  | .fixedLenBytes _ => Bytes.ofList

inductive Error where
  | invalidWidth
  | widthLimit
  | valueLimit
  | byteLimit
  | truncated
  | trailingBytes
  deriving DecidableEq, Repr

def signedSizeLimit : Nat := 2 ^ 31

/-- The caller's extent and resource checks hold before any transposition. -/
structure Admission (limits : Limits) (width count : Nat) (source : Bytes) : Prop where
  widthPositive : 0 < width
  widthFits : width < signedSizeLimit
  widthLimit : width ≤ limits.width
  countFits : count < signedSizeLimit
  valueLimit : count ≤ limits.values
  byteLimit : source.length ≤ limits.bytes
  extent : source.length = width * count

/-- Word `row` uses the `row`-th byte of each lane, in lane order. -/
structure LaneOrder (width count : Nat) (source : Bytes) (words : List (List UInt8)) : Prop where
  wordCount : words.length = count
  wordWidth (row : Nat) (bounded : row < words.length) : words[row].length = width
  octet (row : Nat) (bounded : row < words.length) (lane : Nat) (laneBound : lane < width) :
    words[row][lane]? = source.toList[lane * count + row]?

namespace Internal

theorem index_lt {width count row lane : Nat} (rowBound : row < count) (laneBound : lane < width) :
    lane * count + row < width * count := by
  have below : lane * count + row < (lane + 1) * count := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  exact Nat.lt_of_lt_of_le below (Nat.mul_le_mul_right count laneBound)

/-- Traverse the rows in order, taking one octet at a checked offset in each lane. -/
def transpose (width count : Nat) (source : Bytes)
    (sized : source.length = width * count) : List (List UInt8) :=
  List.ofFn fun row : Fin count =>
    List.ofFn fun lane : Fin width =>
      source.data[lane.val * count + row.val]'(by
        change lane.val * count + row.val < source.length
        rw [sized]
        exact index_lt row.isLt lane.isLt)

end Internal

/-- Check width, count, and exact input extent before reconstructing the words. -/
def decodeWords (limits : Limits) (width count : Nat) (source : Bytes) :
    Except Error (List (List UInt8)) :=
  if width = 0 ∨ signedSizeLimit ≤ width then .error .invalidWidth
  else if limits.width < width then .error .widthLimit
  else if signedSizeLimit ≤ count ∨ limits.values < count then .error .valueLimit
  else if limits.bytes < source.length then .error .byteLimit
  else if sized : source.length = width * count then .ok (Internal.transpose width count source sized)
  else if source.length < width * count then .error .truncated
  else .error .trailingBytes

def decode (kind : Kind) (limits : Limits) (count : Nat) (source : Bytes) :
    Except Error (List kind.Value) :=
  (decodeWords limits kind.width count source).map (List.map kind.readWord)

end Silmaril.Formats.Parquet.ByteStreamSplit
