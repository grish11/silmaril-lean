module

public import Init.Data.ByteArray
public import Init.Data.Float.Model.Float

/-! SQLite storage values and the extra observations of a `sqlite3_value` object. -/

@[expose] public section

namespace Silmaril.SQLite.Relational

universe u v

inductive StorageClass where
  | null | integer | real | text | blob
  deriving DecidableEq, Repr

inductive TextEncoding where
  | utf8 | utf16le | utf16be
  deriving DecidableEq, Repr

/-- Encoded bytes with their interpretation tag. Payloads retain embedded zero bytes and
need not be well-formed Unicode. There is no implicit decoding or normalization. -/
structure Text where
  encoding : TextEncoding
  bytes : ByteArray
  deriving DecidableEq

/-- Encode a Lean string as UTF-8 with no added terminator. -/
def Text.utf8 (s : String) : Text := ⟨.utf8, s.toUTF8⟩

/-- IEEE binary64 bits, excluding NaNs. Equality distinguishes signed zeros and admits both
infinities. This is representation equality, separate from SQL equality. -/
structure Real where
  bits : UInt64
  notNaN : (Float.Model.ofBits bits).isNaN = false
  deriving DecidableEq, Repr

/-- Reject every NaN bit pattern and retain the original bits otherwise. -/
def Real.ofBits (bits : UInt64) : Option Real :=
  if h : (Float.Model.ofBits bits).isNaN = false then some ⟨bits, h⟩ else none

/-- The five SQL-visible storage classes, without C API metadata. -/
inductive SqlValue where
  | null
  | integer (value : Int64)
  | real (value : Real)
  | text (value : Text)
  | blob (bytes : ByteArray)
  deriving DecidableEq

namespace SqlValue

def storageClass : SqlValue → StorageClass
  | .null => .null
  | .integer _ => .integer
  | .real _ => .real
  | .text _ => .text
  | .blob _ => .blob

/-- SQLite's REAL input convention maps NaN to SQL NULL. -/
def ofRealBits (bits : UInt64) : SqlValue :=
  match Real.ofBits bits with
  | some r => .real r
  | none => .null

end SqlValue

/-- Bytes of the C pointer type name before its terminator. Matching is bytewise. -/
def PointerTag := {bytes : ByteArray // 0 ∉ bytes.data.toList}

instance : DecidableEq PointerTag := inferInstanceAs (DecidableEq (Subtype _))

/-- A value object can carry an eight-bit subtype or hide a typed pointer behind SQL NULL.
Instantiate `P` with `Empty` to rule out pointer objects. -/
inductive Value (P : Type u) where
  | sql (value : SqlValue) (subtype : Option UInt8)
  | pointer (tag : PointerTag) (payload : P)

namespace Value

/-- Regard a storage value as an untagged object. -/
def ofSql {P : Type u} (value : SqlValue) : Value P := .sql value none

/-- SQL observes pointers as NULL. The projection also drops value subtypes. -/
def toSql {P : Type u} : Value P → SqlValue
  | .sql value _ => value
  | .pointer _ _ => .null

/-- Change the pointer payload carrier while preserving the tags and storage values. -/
def mapPointer {P : Type u} {Q : Type v} (f : P → Q) : Value P → Value Q
  | .sql value subtype => .sql value subtype
  | .pointer tag payload => .pointer tag (f payload)

/-- Erase pointers, retaining subtypes of ordinary storage values. -/
def forgetPointers {P : Type u} : Value P → Value Empty
  | .sql value subtype => .sql value subtype
  | .pointer _ _ => .ofSql .null

end Value

inductive Protection where
  | protectedValue | unprotectedValue
  deriving DecidableEq, Repr

/-- The protection index controls the modeled C API readers. It records no live lock or lifetime. -/
structure ValueObject (P : Type u) (_ : Protection) where
  value : Value P

namespace ValueObject

/-- `sqlite3_value_subtype` observes zero for an absent subtype and the byte for `p` on pointers. -/
def subtypeCode {P : Type u} (obj : ValueObject P .protectedValue) : UInt8 :=
  match obj.value with
  | .sql _ subtype => subtype.getD 0
  | .pointer _ _ => 112

/-- Recover a pointer only from an actual pointer object with a matching type tag. -/
def pointer? {P : Type u} (obj : ValueObject P .protectedValue) (tag : PointerTag) : Option P :=
  match obj.value with
  | .sql _ _ => none
  | .pointer actual payload => if actual = tag then some payload else none

/-- Successful `sqlite3_value_dup` observation. It gives a protected copy, drops pointers and
clears subtypes on SQL NULL. Allocation failure is outside the model. -/
def dup {P : Type u} {protection : Protection} (obj : ValueObject P protection) :
    ValueObject Empty .protectedValue :=
  match obj.value.forgetPointers with
  | .sql .null _ => ⟨.ofSql .null⟩
  | value => ⟨value⟩

end ValueObject

end Silmaril.SQLite.Relational
