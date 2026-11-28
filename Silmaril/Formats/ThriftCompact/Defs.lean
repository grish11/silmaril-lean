module

public import Silmaril.Formats.Bytes
public import Silmaril.Prelude.Bytes.Digits.Defs
import Init.Omega

/-! Apache Thrift Compact Protocol value and header readers. Each reader takes a byte
offset and returns the first unread offset on success. See
`docs/projects/thrift-compact.md` for the wire specification and reader profile. -/

@[expose] public section

namespace Silmaril.Formats.ThriftCompact

inductive Width where
  | i16 | i32 | i64
  deriving DecidableEq, Repr

def Width.bits : Width → Nat
  | .i16 => 16
  | .i32 => 32
  | .i64 => 64

def Width.byteCount (width : Width) : Nat := (width.bits + 6) / 7

def Width.halfRange (width : Width) : Int := 2 ^ (width.bits - 1)

inductive VarintMode where
  /-- Reject redundant high zero groups. -/
  | canonical
  /-- Accept redundant high zero groups within the same width and byte budget. -/
  | permissive
  deriving DecidableEq, Repr

inductive Error where
  | truncated
  | varintOverflow
  | noncanonicalVarint
  | lengthOverflow
  | lengthLimit
  | invalidBoolean
  | invalidUtf8
  | invalidType (tag : Nat)
  | fieldIdOverflow
  | invalidCollectionSize
  deriving DecidableEq, Repr

/-- Arithmetic form of the signed-to-unsigned ZigZag mapping. -/
def zigzag (value : Int) : Nat :=
  if value < 0 then (-2 * value - 1).toNat else (2 * value).toNat

def unzigzag (value : Nat) : Int :=
  if value % 2 = 0 then (value / 2 : Nat) else -((value / 2 : Nat) : Int) - 1

/-- Wire relation for one terminated varint, before any width restriction.
A continuation contributes the low seven bits, followed by higher groups. -/
inductive VarintWire (mode : VarintMode) : List UInt8 → Nat → Prop where
  | last (byte : UInt8) (terminal : byte.toNat < 128) :
      VarintWire mode [byte] byte.toNat
  | more (byte : UInt8) (continued : 128 ≤ byte.toNat)
      {rest : List UInt8} {high : Nat} (wire : VarintWire mode rest high)
      (minimal : mode = .canonical → high ≠ 0) :
      VarintWire mode (byte :: rest) (byte.toNat - 128 + 128 * high)

/-- Minimal base-128 groups, least significant first. -/
def varintBytes (value : Nat) : List UInt8 :=
  if value < 128 then [UInt8.ofNat value]
  else UInt8.ofNat (128 + value % 128) :: varintBytes (value / 128)
termination_by value
decreasing_by omega

/-- Encode a signed integer when it fits its declared width. -/
def encodeSigned? (width : Width) (value : Int) : Option Bytes :=
  let code := zigzag value
  if code < 2 ^ width.bits then some (Bytes.ofList (varintBytes code)) else none

/-- Read a width-bounded base-128 value. Continuation on the last allowed octet
is an overflow, even if the source ends there. -/
def readVarint (width : Width) (mode : VarintMode) (source : Bytes) (offset : Nat) :
    Except Error (Nat × Nat) :=
  match go mode source width.byteCount offset with
  | .ok (value, next) =>
    if value < 2 ^ width.bits then .ok (value, next) else .error .varintOverflow
  | .error error => .error error
where
  go (mode : VarintMode) (source : Bytes) : Nat → Nat → Except Error (Nat × Nat)
    | 0, _ => .error .varintOverflow
    | fuel + 1, offset =>
      match source.data[offset]? with
      | none => .error .truncated
      | some byte =>
        let digit := byte.toNat
        if digit < 128 then .ok (digit, offset + 1)
        else
          match go mode source fuel (offset + 1) with
          | .error error => .error error
          | .ok (high, next) =>
            if mode = .canonical ∧ high = 0 then .error .noncanonicalVarint
            else .ok (digit - 128 + 128 * high, next)

def readSigned (width : Width) (mode : VarintMode) (source : Bytes) (offset : Nat) : Except Error (Int × Nat) := do
  let (code, next) ← readVarint width mode source offset
  pure (unzigzag code, next)

def readOctet (source : Bytes) (offset : Nat) : Except Error (UInt8 × Nat) :=
  match source.data[offset]? with
  | some byte => .ok (byte, offset + 1)
  | none => .error .truncated

/-- A raw i8 is one signed two's-complement octet. -/
def readI8 (source : Bytes) (offset : Nat) : Except Error (Int × Nat) := do
  let (byte, next) ← readOctet source offset
  let value : Int := byte.toNat
  pure (if value < 128 then value else value - 256, next)

/-- Standalone boolean values, as used in collections. A struct-field boolean
comes from the header and consumes zero payload bytes. -/
def readBool (source : Bytes) (offset : Nat) : Except Error (Bool × Nat) := do
  let (byte, next) ← readOctet source offset
  match byte.toNat with
  | 1 => pure (true, next)
  | 2 => pure (false, next)
  | _ => throw .invalidBoolean

def readFixed (count : Nat) (source : Bytes) (offset : Nat) : Except Error (Bytes × Nat) :=
  let next := offset + count
  if next ≤ source.length then .ok (⟨source.data.extract offset next⟩, next)
  else .error .truncated

/-- An unsigned varint length in the nonnegative i32 domain, with a caller-supplied cap. -/
def readLength (mode : VarintMode) (limit : Nat) (source : Bytes) (offset : Nat) :
    Except Error (Nat × Nat) :=
  match readVarint .i32 mode source offset with
  | .error error => .error error
  | .ok (count, next) =>
    if count < 2 ^ 31 then
      if count ≤ limit then .ok (count, next) else .error .lengthLimit
    else .error .lengthOverflow

def readBinary (mode : VarintMode) (limit : Nat) (source : Bytes) (offset : Nat) : Except Error (Bytes × Nat) := do
  let (count, next) ← readLength mode limit source offset
  readFixed count source next

def readString (mode : VarintMode) (limit : Nat) (source : Bytes) (offset : Nat) : Except Error (String × Nat) := do
  let (bytes, next) ← readBinary mode limit source offset
  let some value := String.fromUTF8? bytes.data | throw .invalidUtf8
  pure (value, next)

/-- Read the little-endian IEEE 754 encoding, preserving all bit patterns. -/
def readDoubleBits (source : Bytes) (offset : Nat) : Except Error (UInt64 × Nat) := do
  let (bytes, next) ← readFixed 8 source offset
  pure (UInt64.ofNat (KBytes.leVal bytes.toList), next)

/-- Read the 16 UUID octets in wire order. -/
def readUuid (source : Bytes) (offset : Nat) : Except Error (Bytes × Nat) :=
  readFixed 16 source offset

inductive ValueType where
  | bool | i8 | i16 | i32 | i64 | double | binary | list | set | map | struct | uuid
  deriving DecidableEq, Repr

def ValueType.ofTag? : Nat → Option ValueType
  | 1 | 2 => some .bool
  | 3 => some .i8
  | 4 => some .i16
  | 5 => some .i32
  | 6 => some .i64
  | 7 => some .double
  | 8 => some .binary
  | 9 => some .list
  | 10 => some .set
  | 11 => some .map
  | 12 => some .struct
  | 13 => some .uuid
  | _ => none

/-- A boolean struct field stores its value in the type nibble. -/
inductive FieldType where
  | bool (value : Bool)
  | payload (type : ValueType)
  deriving DecidableEq, Repr

inductive FieldHeader where
  | stop
  | field (id : Int) (type : FieldType)
  deriving DecidableEq, Repr

/-- Start each struct with previous field ID zero. After a field, use its ID
as the previous one for the next header in that struct. -/
def readFieldHeader (mode : VarintMode) (previousId : Int)
    (source : Bytes) (offset : Nat) : Except Error (FieldHeader × Nat) := do
  let (byte, next) ← readOctet source offset
  let header := byte.toNat
  if header = 0 then return (.stop, next)
  let tag := header % 16
  let some type := ValueType.ofTag? tag | throw (.invalidType tag)
  let fieldType := if tag = 1 then FieldType.bool true
    else if tag = 2 then FieldType.bool false else FieldType.payload type
  let delta := header / 16
  let (id, endOffset) ← if delta = 0 then readSigned .i16 mode source next
    else pure (previousId + delta, next)
  if id < -32768 ∨ 32768 ≤ id then throw .fieldIdOverflow
  else pure (.field id fieldType, endOffset)

structure CollectionHeader where
  size : Nat
  elementType : ValueType
  deriving DecidableEq, Repr

/-- Read a list or set header. Both boolean type nibbles are accepted. -/
def readCollectionHeader (mode : VarintMode) (limit : Nat)
    (source : Bytes) (offset : Nat) : Except Error (CollectionHeader × Nat) := do
  let (byte, next) ← readOctet source offset
  let tag := byte.toNat % 16
  let some type := ValueType.ofTag? tag | throw (.invalidType tag)
  let shortSize := byte.toNat / 16
  if shortSize = 15 then
    let (size, endOffset) ← readLength mode limit source next
    if size < 15 then throw .invalidCollectionSize
    else pure (⟨size, type⟩, endOffset)
  else if limit < shortSize then throw .lengthLimit
  else pure (⟨shortSize, type⟩, next)

inductive MapHeader where
  | empty
  | entries (size : Nat) (keyType valueType : ValueType)
  deriving DecidableEq, Repr

def readMapHeader (mode : VarintMode) (limit : Nat) (source : Bytes)
    (offset : Nat) : Except Error (MapHeader × Nat) := do
  let (size, next) ← readLength mode limit source offset
  if size = 0 then return (.empty, next)
  let (byte, endOffset) ← readOctet source next
  let key := byte.toNat / 16
  let value := byte.toNat % 16
  let some keyType := ValueType.ofTag? key | throw (.invalidType key)
  let some valueType := ValueType.ofTag? value | throw (.invalidType value)
  pure (.entries size keyType valueType, endOffset)

end Silmaril.Formats.ThriftCompact
