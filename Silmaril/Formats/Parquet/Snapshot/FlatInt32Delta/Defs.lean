module

public import Silmaril.Formats.Parquet.Snapshot.FlatInt32.Defs
public import Silmaril.Formats.Parquet.FlatScan.Delta.Defs

/-! Opt-in uncompressed flat INT32 snapshots with PLAIN and DELTA_BINARY_PACKED. -/

public section

namespace Silmaril.Formats.Parquet.Snapshot.FlatInt32Delta

open Silmaril.Relational Silmaril.Formats.Arrow
open FlatInt32 (Cell)

structure Limits where
  flat : FlatInt32.Limits := {}
  packed : DeltaBinaryPacked.Limits := ⟨16 * 1024 * 1024, 1024 * 1024, 4096, 128, 1024 * 1024⟩
  maxFileBytes : Nat := 256 * 1024 * 1024
  maxGroups : Nat := 4096
  maxFileRows : Nat := 4 * 1024 * 1024
  maxFileCells : Nat := 16 * 1024 * 1024

private def Limits.decoder (limits : Limits) : DeltaPage.Limits :=
  -- The INT32 dispatch never selects either byte-array decoder.
  let inactive : DeltaLengthByteArray.Limits := ⟨limits.packed, 0, 0⟩
  ⟨limits.flat.pages, limits.packed, inactive, ⟨limits.packed, inactive, 0, 0⟩⟩

inductive Error where
  | fileByteLimit | groupLimit | fileRowLimit | fileCellLimit
  | schema (reason : FlatScan.Error Unit)
  | schemaNames (expected actual : List String)
  | groupRowLimit | groupCellLimit
  | columnArity (expected actual : Nat)
  | column (index : Nat) (field : String) (reason : FlatScan.ColumnFailure FlatScan.Delta.Error)
  | rowWidth (expected actual : Nat)
  deriving DecidableEq, Repr

private def typedRow (schema : Scan.Schema String Unit) (row : List (Option Int32)) :
    Except Error (Scan.Row schema Cell) :=
  if width : row.length = schema.width then
    .ok (fun index => row[index.val]'(width.symm ▸ index.isLt))
  else .error (.rowWidth schema.width row.length)

private def decodeGroup (limits : Limits) (schema : Scan.Schema String Unit)
    (fields : List FlatScan.Field) : DecodeGroup schema Cell Error := fun snapshot _ group => do
  let rows := group.numRows.toNat
  if group.numRows < 0 || rows > limits.flat.groups.maxRows then throw .groupRowLimit
  if rows * fields.length > limits.flat.groups.maxCells then throw .groupCellLimit
  if fields.length != group.columns.length then throw (.columnArity fields.length group.columns.length)
  let decoder := FlatScan.Delta.decodePage limits.decoder
  let columns ← (fields.zip group.columns).zipIdx.mapM fun ((field, column), index) =>
    (FlatScan.scanColumnPlainDelta limits.flat.groups decoder snapshot.bytes snapshot.footer.start field rows column)
      |>.map (field, ·) |>.mapError (.column index field.name)
  FlatScan.Batch.rows ⟨rows, columns⟩ |>.mapM (typedRow schema)

/-- Bind the ordered flat schema and file budgets before reading any group.
All CRC-bearing data pages are rejected by this profile. Callers using this
binder directly apply the file byte cap before opening the snapshot. -/
def bind (limits : Limits) (schema : Scan.Schema String Unit) : Bind schema Cell Error := fun metadata => do
  let fields ← (FlatScan.flatSchema limits.flat.groups metadata.schema).mapError .schema
  let expected := List.ofFn (fun index => (schema.kind index).1)
  let actual := fields.map (·.name)
  if expected != actual then throw (.schemaNames expected actual)
  if metadata.rowGroups.length > limits.maxGroups then throw .groupLimit
  if metadata.numRows < 0 || metadata.numRows.toNat > limits.maxFileRows then throw .fileRowLimit
  if metadata.numRows.toNat * fields.length > limits.maxFileCells then throw .fileCellLimit
  pure (decodeGroup limits schema fields)

/-- Emit complete batches in footer order through EOF or the first indexed error. -/
def readAll (limits : Limits) (schema : Scan.Schema String Unit) (bytes : Bytes) :
    Events.EventStream String Cell (Snapshot.Error Error) :=
  if bytes.length > limits.maxFileBytes then .error (.input .fileByteLimit)
  else Snapshot.readAll limits.flat.snapshot (bind limits schema) bytes

end Silmaril.Formats.Parquet.Snapshot.FlatInt32Delta
