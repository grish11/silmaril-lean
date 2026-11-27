module

public import Silmaril.Formats.Arrow.MixedFlat.Defs
public import Silmaril.Formats.Arrow.Writer.Defs
public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Defs

/-! Completely prepare the checked two-column file source for a typed
consumer of INT32-first BinaryView batches. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.Prepare

open Silmaril.Relational

/-- Field declarations are separate from the batches, including for an empty file. -/
structure Schema where
  intName : String
  intNullable : Bool
  viewName : String
  viewNullable : Bool
  deriving DecidableEq, Repr

def Schema.fields (schema : Schema) : List Arrow.MixedFlat.Field :=
  [⟨schema.intName, schema.intNullable, .primitive .int32⟩,
    ⟨schema.viewName, schema.viewNullable, .view .binary⟩]

def Schema.ofSelection (int32 byteArray : Field) : Schema :=
  ⟨int32.name, decide (int32.layout = .optional), byteArray.name, decide (byteArray.layout = .optional)⟩

/-- One complete group with the row count and paired nullable values
in the carriers accepted by mixed Arrow batch consumers. -/
structure Batch where
  rowCount : Nat
  intValues : List (Option Int32)
  viewValues : List (Option KBytes)

def Batch.ofRows (int32 byteArray : Field) (rows : Reader.RowGroup (File.schema int32 byteArray) File.Value) :
    Batch :=
  let columns := AlignedColumns.ofRows rows
  let integers := columns.values ⟨0, by change 0 < 2; decide⟩
  let binary := columns.values ⟨1, by change 1 < 2; decide⟩
  ⟨columns.rowCount, integers,
    binary.map (Option.map fun bytes => Arrow.Writer.emitWords 1 (bytes.toList.map UInt8.toNat))⟩

structure Prepared where
  schema : Schema
  batches : List Batch

/-- Exhaust an already checked file, retaining the caller's original projection. -/
def prepareChecked {limits : File.Limits} {int32 byteArray : Field}
    (checked : File.Checked limits int32 byteArray) : Except File.Error Prepared := do
  let source := checked.source
  let groups ← source.groups.mapM source.readGroup
  return ⟨Schema.ofSelection int32 byteArray, groups.map (Batch.ofRows int32 byteArray)⟩

/-- Consume the actual checked source in footer order. The first indexed
failure returns its original payload and no prepared result. -/
def prepare (limits : File.Limits) (input : Bytes) (int32 byteArray : Field) :
    Except File.Error Prepared := do
  let checked ← File.openFile limits input int32 byteArray
  prepareChecked checked

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.Prepare
