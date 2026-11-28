module

public import Silmaril.Formats.ThriftCompact.Traversal.Defs

/-! Plaintext PageHeader projection for Parquet format 2.14.0. -/

public section

namespace Silmaril.Formats.Parquet.Page

open ThriftCompact

/-- Encoding fields retain the numeric ID from `parquet.thrift`. -/
structure DataV1 where
  numValues : Nat
  encoding : Int
  definitionLevelEncoding : Int
  repetitionLevelEncoding : Int
  deriving Repr, DecidableEq

structure DataV2 where
  numValues : Nat
  numNulls : Nat
  numRows : Nat
  encoding : Int
  definitionBytes : Nat
  repetitionBytes : Nat
  isCompressed : Bool
  deriving Repr, DecidableEq

structure Dictionary where
  numValues : Nat
  encoding : Int
  isSorted : Option Bool
  deriving Repr, DecidableEq

inductive SkippedKind where
  | indexPage
  | unknown (code : Int)
  deriving Repr, DecidableEq

inductive Kind where
  | dataV1 (header : DataV1)
  | dictionary (header : Dictionary)
  | dataV2 (header : DataV2)
  | skipped (kind : SkippedKind)
  deriving Repr, DecidableEq

structure Header where
  uncompressedSize : Nat
  compressedSize : Nat
  crc : Option UInt32
  kind : Kind
  deriving Repr, DecidableEq

structure HeaderLimits where
  compact : Traversal.Limits := {}
  varintMode : VarintMode := .canonical

inductive HeaderError where
  | traversal (error : Traversal.Error)
  | missingField (id : Int)
  | duplicateField (id : Int)
  | fieldType (id : Int) (actual : FieldType)
  | fieldConsumption (id : Int)
  | headerConsumption
  | negativeField (id : Int)
  | conflictingKind (code : Int)
  | invalidV2Counts
  | invalidV2Lengths
  deriving Repr, DecidableEq

open Traversal (Reader Field)

private abbrev Projection (α : Type) := Except HeaderError α

private def field? (fields : List Field) (id : Int) : Projection (Option Field) :=
  match fields.filter (·.id == id) with
  | [] => .ok none
  | [field] => .ok (some field)
  | _ => .error (.duplicateField id)

private def requireField (fields : List Field) (id : Int) : Projection Field := do
  let some field ← field? fields id | throw (.missingField id)
  pure field

private def integer (reader : Reader) (field : Field) : Projection Int := do
  if field.type ≠ .payload .i32 then throw (.fieldType field.id field.type)
  let (value, next) ← (readSigned .i32 reader.mode reader.source field.start).mapError
    (fun error => .traversal (.compact error))
  if next ≠ field.stop then throw (.fieldConsumption field.id)
  pure value

private def integerAt (reader : Reader) (fields : List Field) (id : Int) : Projection Int := do
  integer reader (← requireField fields id)

private def countAt (reader : Reader) (fields : List Field) (id : Int) : Projection Nat := do
  let value ← integerAt reader fields id
  if value < 0 then throw (.negativeField id)
  pure value.toNat

private def boolAt (fields : List Field) (id : Int) : Projection (Option Bool) := do
  match ← field? fields id with
  | none => pure none
  | some field =>
    match field.type with
    | .bool value => pure (some value)
    | _ => throw (.fieldType id field.type)

private def detail (reader : Reader) (field : Field) : Projection (List Field) := do
  if field.type ≠ .payload .struct then throw (.fieldType field.id field.type)
  let (fields, next) ← (Traversal.readStruct reader field.start).mapError .traversal
  if next ≠ field.stop then throw (.fieldConsumption field.id)
  pure fields

private def dataV1 (reader : Reader) (fields : List Field) : Projection DataV1 := do
  return ⟨← countAt reader fields 1, ← integerAt reader fields 2,
    ← integerAt reader fields 3, ← integerAt reader fields 4⟩

private def dictionary (reader : Reader) (fields : List Field) : Projection Dictionary := do
  return ⟨← countAt reader fields 1, ← integerAt reader fields 2, ← boolAt fields 3⟩

private def dataV2 (reader : Reader) (fields : List Field) (compressed uncompressed : Nat) :
    Projection DataV2 := do
  let values ← countAt reader fields 1
  let nulls ← countAt reader fields 2
  let rows ← countAt reader fields 3
  if values < nulls || values < rows then throw .invalidV2Counts
  let encoding ← integerAt reader fields 4
  let definition ← countAt reader fields 5
  let repetition ← countAt reader fields 6
  let isCompressed := (← boolAt fields 7).getD true
  if compressed < definition + repetition || uncompressed < definition + repetition ||
      (!isCompressed && compressed != uncompressed) then throw .invalidV2Lengths
  return ⟨values, nulls, rows, encoding, definition, repetition, isCompressed⟩

private def project (reader : Reader) (fields : List Field) : Projection Header := do
  let code ← integerAt reader fields 1
  let uncompressed ← countAt reader fields 2
  let compressed ← countAt reader fields 3
  let crc ← (← field? fields 4).mapM fun field => UInt32.ofInt <$> integer reader field
  let knownDetails := fields.filter fun field => 5 ≤ field.id && field.id ≤ 8
  let kind ← match code with
    | 0 => Kind.dataV1 <$> dataV1 reader (← detail reader (← expectDetail knownDetails 5 code))
    | 1 => do
      let _ ← detail reader (← expectDetail knownDetails 6 code)
      pure (.skipped .indexPage)
    | 2 => Kind.dictionary <$> dictionary reader (← detail reader (← expectDetail knownDetails 7 code))
    | 3 => do
      let fields ← detail reader (← expectDetail knownDetails 8 code)
      Kind.dataV2 <$> dataV2 reader fields compressed uncompressed
    | code =>
      if knownDetails.isEmpty then pure (.skipped (.unknown code)) else throw (.conflictingKind code)
  pure ⟨uncompressed, compressed, crc, kind⟩
where
  expectDetail (details : List Field) (id code : Int) : Projection Field := do
    let field ← requireField details id
    if details.length ≠ 1 then throw (.conflictingKind code)
    pure field

/-- Consume one Compact PageHeader starting at zero. The structural reader
returns the first byte after STOP and all typed reads use only that prefix. -/
def readHeaderPrefix (limits : HeaderLimits) (window : Bytes) : Except HeaderError (Header × Nat) := do
  let reader : Reader := ⟨window, limits.compact, limits.varintMode⟩
  let (fields, next) ← (Traversal.readStruct reader 0).mapError .traversal
  if next = 0 ∨ window.length < next then throw .headerConsumption
  let consumed : Bytes := ⟨window.data.extract 0 next⟩
  pure (← project {reader with source := consumed} fields, next)

end Silmaril.Formats.Parquet.Page
