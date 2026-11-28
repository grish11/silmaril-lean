module

public import Silmaril.Formats.ThriftCompact.Traversal.Defs

/-! The typed plaintext projection of the pinned `parquet.thrift` file metadata. -/

public section

namespace Silmaril.Formats.Parquet.Footer

open ThriftCompact

inductive PhysicalType where
  | boolean | int32 | int64 | int96 | float | double | byteArray | fixedLenByteArray
  deriving DecidableEq, Repr

inductive Repetition where
  | required | optional | repeated
  deriving DecidableEq, Repr

structure SchemaElement where
  physicalType : Option PhysicalType
  typeLength : Option Int
  repetition : Option Repetition
  name : String
  numChildren : Option Int
  deriving Repr

structure ColumnMetadata where
  physicalType : PhysicalType
  /-- Numeric `Encoding` IDs from the IDL, retained for forward compatibility. -/
  encodings : List Int
  pathInSchema : List String
  /-- Numeric `CompressionCodec` ID from the IDL. -/
  codec : Int
  numValues : Int
  totalUncompressedSize : Int
  totalCompressedSize : Int
  dataPageOffset : Int
  indexPageOffset : Option Int
  dictionaryPageOffset : Option Int
  bloomFilterOffset : Option Int
  bloomFilterLength : Option Int
  deriving Repr

structure ColumnChunk where
  fileOffset : Int
  metadata : ColumnMetadata
  offsetIndexOffset : Option Int
  offsetIndexLength : Option Int
  columnIndexOffset : Option Int
  columnIndexLength : Option Int
  deriving Repr

structure RowGroup where
  columns : List ColumnChunk
  totalByteSize : Int
  numRows : Int
  fileOffset : Option Int
  totalCompressedSize : Option Int
  deriving Repr

structure Metadata where
  version : Int
  schema : List SchemaElement
  numRows : Int
  rowGroups : List RowGroup
  createdBy : Option String
  deriving Repr

inductive MetadataError where
  | traversal (error : Traversal.Error)
  | missingField (id : Int)
  | duplicateField (id : Int)
  | fieldType (id : Int) (expected : ValueType) (actual : FieldType)
  | fieldConsumption (id : Int)
  | physicalType (code : Int)
  | repetition (code : Int)
  | externalColumn
  | encryption
  deriving DecidableEq, Repr

open Traversal (Reader Field)

private abbrev Read (α : Type) := Nat → Except MetadataError (α × Nat)

private def fromTraversal {α : Type} (read : Traversal.Read α) : Read α :=
  fun offset => (read offset).mapError .traversal

private def scalar {α : Type} (read : Nat → Except ThriftCompact.Error (α × Nat)) : Read α :=
  fromTraversal (fun offset => (read offset).mapError .compact)

private def integer (reader : Reader) (width : Width) : Read Int :=
  scalar (readSigned width reader.mode reader.source)

private def string (reader : Reader) : Read String :=
  scalar (readString reader.mode reader.limits.maxBinaryBytes reader.source)

private def list (reader : Reader) {α : Type} (type : ValueType) (read : Read α) : Read (List α) :=
  Traversal.readList reader .traversal type read

private def readStruct {α : Type} (reader : Reader)
    (project : List Field → Except MetadataError α) : Read α := fun offset => do
  let (fields, next) ← fromTraversal (Traversal.readStruct reader) offset
  pure (← project fields, next)

private def optional {α : Type} (fields : List Field) (id : Int) (type : ValueType)
    (read : Read α) : Except MetadataError (Option α) := do
  match fields.filter (·.id == id) with
  | [] => pure none
  | [field] =>
    if field.type ≠ .payload type then throw (.fieldType id type field.type)
    let (value, next) ← read field.start
    if next ≠ field.stop then throw (.fieldConsumption id)
    pure (some value)
  | _ => throw (.duplicateField id)

private def required {α : Type} (fields : List Field) (id : Int) (type : ValueType)
    (read : Read α) : Except MetadataError α := do
  let some value ← optional fields id type read | throw (.missingField id)
  pure value

private def physicalType (reader : Reader) : Read PhysicalType := fun offset => do
  let (code, next) ← integer reader .i32 offset
  let type ← match code with
    | 0 => pure .boolean
    | 1 => pure .int32
    | 2 => pure .int64
    | 3 => pure .int96
    | 4 => pure .float
    | 5 => pure .double
    | 6 => pure .byteArray
    | 7 => pure .fixedLenByteArray
    | _ => throw (.physicalType code)
  pure (type, next)

private def repetition (reader : Reader) : Read Repetition := fun offset => do
  let (code, next) ← integer reader .i32 offset
  let value ← match code with
    | 0 => pure .required
    | 1 => pure .optional
    | 2 => pure .repeated
    | _ => throw (.repetition code)
  pure (value, next)

private def schemaElement (reader : Reader) : Read SchemaElement := readStruct reader fun fields => do
  return {
    physicalType := ← optional fields 1 .i32 (physicalType reader)
    typeLength := ← optional fields 2 .i32 (integer reader .i32)
    repetition := ← optional fields 3 .i32 (repetition reader)
    name := ← required fields 4 .binary (string reader)
    numChildren := ← optional fields 5 .i32 (integer reader .i32) }

private def columnMetadata (reader : Reader) : Read ColumnMetadata := readStruct reader fun fields => do
  let i64 := integer reader .i64
  let i32 := integer reader .i32
  return {
    physicalType := ← required fields 1 .i32 (physicalType reader)
    encodings := ← required fields 2 .list (list reader .i32 i32)
    pathInSchema := ← required fields 3 .list (list reader .binary (string reader))
    codec := ← required fields 4 .i32 i32
    numValues := ← required fields 5 .i64 i64
    totalUncompressedSize := ← required fields 6 .i64 i64
    totalCompressedSize := ← required fields 7 .i64 i64
    dataPageOffset := ← required fields 9 .i64 i64
    indexPageOffset := ← optional fields 10 .i64 i64
    dictionaryPageOffset := ← optional fields 11 .i64 i64
    bloomFilterOffset := ← optional fields 14 .i64 i64
    bloomFilterLength := ← optional fields 15 .i32 i32 }

private def columnChunk (reader : Reader) : Read ColumnChunk := readStruct reader fun fields => do
  if fields.any (fun field => field.id == 8 || field.id == 9) then throw .encryption
  if (← optional fields 1 .binary (string reader)).any (· != "") then throw .externalColumn
  let i64 := integer reader .i64
  let i32 := integer reader .i32
  return {
    fileOffset := ← required fields 2 .i64 i64
    metadata := ← required fields 3 .struct (columnMetadata reader)
    offsetIndexOffset := ← optional fields 4 .i64 i64
    offsetIndexLength := ← optional fields 5 .i32 i32
    columnIndexOffset := ← optional fields 6 .i64 i64
    columnIndexLength := ← optional fields 7 .i32 i32 }

private def rowGroup (reader : Reader) : Read RowGroup := readStruct reader fun fields => do
  let i64 := integer reader .i64
  return {
    columns := ← required fields 1 .list (list reader .struct (columnChunk reader))
    totalByteSize := ← required fields 2 .i64 i64
    numRows := ← required fields 3 .i64 i64
    fileOffset := ← optional fields 5 .i64 i64
    totalCompressedSize := ← optional fields 6 .i64 i64 }

/-- Decode one headerless `FileMetaData` struct and return the first byte after STOP.
The structural pass checks every field before projecting the represented IDs. -/
def readMetadataPrefix (reader : Reader) (offset : Nat) : Except MetadataError (Metadata × Nat) :=
  readStruct reader (fun fields => do
    if fields.any (fun field => field.id == 8 || field.id == 9) then throw .encryption
    return {
      version := ← required fields 1 .i32 (integer reader .i32)
      schema := ← required fields 2 .list (list reader .struct (schemaElement reader))
      numRows := ← required fields 3 .i64 (integer reader .i64)
      rowGroups := ← required fields 4 .list (list reader .struct (rowGroup reader))
      createdBy := ← optional fields 6 .binary (string reader) }) offset

end Silmaril.Formats.Parquet.Footer
