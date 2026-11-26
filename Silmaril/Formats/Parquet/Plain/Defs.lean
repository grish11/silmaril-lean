module

public import Silmaril.Formats.Bytes
public import Silmaril.Prelude.Bytes.Digits.Defs
import Init.Omega

/-! Parquet PLAIN physical values on an exact byte slice. The caller supplies
the physical type, value count, and any fixed array width. See
`docs/projects/parquet-plain.md` for the wire reference and the checked profile. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Plain

inductive Error where
  | truncated
  | trailingBytes
  | invalidWidth
  | elementWidthMismatch
  | integerOverflow
  deriving DecidableEq, Repr

/-- Read consecutive fixed-width words into a reversed accumulator. -/
def decodeWords {α : Type} (width : Nat) (readWord : List UInt8 → α) :
    Nat → List UInt8 → List α → List α
  | 0, _, acc => acc.reverse
  | count + 1, bytes, acc =>
    decodeWords width readWord count (bytes.drop width) (readWord (bytes.take width) :: acc)

/-- Decode exactly `count` positive-width words. The size is checked before
conversion to a list or iteration. The natural-number product cannot wrap. -/
def decodeFixedWidth {α : Type} (width count : Nat) (readWord : List UInt8 → α)
    (source : Bytes) : Except Error (List α) :=
  if width = 0 then .error .invalidWidth
  else if source.length < count * width then .error .truncated
  else if count * width < source.length then .error .trailingBytes
  else .ok (decodeWords width readWord count source.toList [])

def encodeWords {α : Type} (writeWord : α → List UInt8) (values : List α) : Bytes :=
  Bytes.ofList (values.flatMap writeWord)

def readUInt32Word (word : List UInt8) : UInt32 := UInt32.ofNat (KBytes.leVal word)
def readUInt64Word (word : List UInt8) : UInt64 := UInt64.ofNat (KBytes.leVal word)
def writeUInt32Word (word : UInt32) : List UInt8 := KBytes.unpack 4 word.toNat
def writeUInt64Word (word : UInt64) : List UInt8 := KBytes.unpack 8 word.toNat

def decodeInt32 (count : Nat) (source : Bytes) : Except Error (List Int32) :=
  decodeFixedWidth 4 count (fun word => (readUInt32Word word).toInt32) source

def decodeInt64 (count : Nat) (source : Bytes) : Except Error (List Int64) :=
  decodeFixedWidth 8 count (fun word => (readUInt64Word word).toInt64) source

def encodeInt32 (values : List Int32) : Bytes :=
  encodeWords (fun value => writeUInt32Word value.toUInt32) values

def encodeInt64 (values : List Int64) : Bytes :=
  encodeWords (fun value => writeUInt64Word value.toUInt64) values

/-- Check representability before narrowing an unbounded integer. -/
def checkSigned {α : Type} (halfRange : Int) (narrow : Int → α) (value : Int) : Except Error α :=
  if -halfRange ≤ value ∧ value < halfRange then .ok (narrow value) else .error .integerOverflow

def encodeInt32Checked (values : List Int) : Except Error Bytes := do
  let narrowed ← values.mapM (checkSigned (2 ^ 31) Int32.ofInt)
  pure (encodeInt32 narrowed)

def encodeInt64Checked (values : List Int) : Except Error Bytes := do
  let narrowed ← values.mapM (checkSigned (2 ^ 63) Int64.ofInt)
  pure (encodeInt64 narrowed)

/-- IEEE binary32 bit patterns in physical order. -/
def decodeFloatBits (count : Nat) (source : Bytes) : Except Error (List UInt32) :=
  decodeFixedWidth 4 count readUInt32Word source

/-- IEEE binary64 bit patterns in physical order. -/
def decodeDoubleBits (count : Nat) (source : Bytes) : Except Error (List UInt64) :=
  decodeFixedWidth 8 count readUInt64Word source

def encodeFloatBits (values : List UInt32) : Bytes := encodeWords writeUInt32Word values
def encodeDoubleBits (values : List UInt64) : Bytes := encodeWords writeUInt64Word values

/-- The caller's width comes from a positive signed-i32 schema length. -/
def decodeFixedLenBytes (width count : Nat) (source : Bytes) : Except Error (List Bytes) :=
  if width < 2 ^ 31 then decodeFixedWidth width count Bytes.ofList source
  else .error .invalidWidth

def encodeFixedLenBytes (width : Nat) (values : List Bytes) : Except Error Bytes :=
  if 0 < width ∧ width < 2 ^ 31 then
    if values.all (fun value => value.length == width) then .ok (encodeWords Bytes.toList values)
    else .error .elementWidthMismatch
  else .error .invalidWidth

def booleanByteCount (count : Nat) : Nat := (count + 7) / 8

/-- PLAIN Boolean values start at the least significant bit of the first byte.
At most seven unused high bits in the last byte are ignored. -/
def decodeBoolean (count : Nat) (source : Bytes) : Except Error (List Bool) :=
  if sized : source.length = booleanByteCount count then
    .ok (List.ofFn fun (i : Fin count) =>
      let byte := source.data[i.val / 8]'(by
        have hi := i.isLt
        change i.val / 8 < source.length
        unfold booleanByteCount at sized
        omega)
      byte.toNat.testBit (i.val % 8))
  else if source.length < booleanByteCount count then .error .truncated
  else .error .trailingBytes

/-- Form one Boolean octet in LSB-first order, with missing bits set to zero. -/
def booleanOctet (values : Array Bool) (octet : Nat) : UInt8 :=
  let bits := List.ofFn fun (bit : Fin 8) => values[8 * octet + bit.val]?.getD false
  UInt8.ofNat (BitVec.ofBoolListLE bits).toNat

def encodeBoolean (values : List Bool) : Bytes :=
  let bits := values.toArray
  Bytes.ofList (List.ofFn fun (octet : Fin (booleanByteCount values.length)) =>
    booleanOctet bits octet.val)

end Silmaril.Formats.Parquet.Plain
