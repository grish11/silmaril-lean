module

public import Silmaril.Formats.Parquet.Snapshot.FlatInt32.Defs
public import Silmaril.Formats.Parquet.DictionaryChunk.Defs

/-! Opt-in snapshots for flat, uncompressed PLAIN and dictionary INT32 columns. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary

open Silmaril.Relational Silmaril.Formats.Arrow
open FlatInt32 (Cell)

structure Limits where
  plain : FlatInt32.Limits := {}
  dictionary : DictionaryChunk.Limits := {}
  maxFileBytes : Nat := 256 * 1024 * 1024
  maxGroups : Nat := 4096
  maxFileRows : Nat := 4 * 1024 * 1024
  maxFileCells : Nat := 16 * 1024 * 1024

inductive ColumnError where
  | path (actual : List String)
  | physicalType (actual : Footer.PhysicalType)
  | slotCount (actual : Int)
  | codec (actual : Int)
  | plain (reason : FlatScan.Error FlatScan.AdapterError)
  | dictionary (reason : DictionaryChunk.Error)
  deriving DecidableEq, Repr

inductive Error where
  | fileByteLimit | groupLimit | fileRowLimit | fileCellLimit
  | schema (reason : FlatScan.Error Unit)
  | schemaNames (expected actual : List String)
  | groupRowLimit | groupCellLimit
  | columnArity (expected actual : Nat)
  | column (index : Nat) (field : String) (reason : ColumnError)
  | rowWidth (expected actual : Nat)
  deriving DecidableEq, Repr

namespace Internal

/-- Establish schema and codec admission before consulting either page offset.
The selected reader owns framing, CRC rejection, and exact body decoding. -/
def readColumn (limits : Limits) (source : Bytes) (footerStart : Nat) (field : FlatScan.Field)
    (rows : Nat) (column : Footer.ColumnChunk) : Except ColumnError (FlatScan.ColumnValues rows) :=
  let metadata := column.metadata
  if metadata.pathInSchema ≠ [field.name] then .error (.path metadata.pathInSchema)
  else if metadata.physicalType ≠ .int32 then .error (.physicalType metadata.physicalType)
  else if metadata.numValues ≠ (rows : Int) then .error (.slotCount metadata.numValues)
  else if metadata.codec ≠ 0 then .error (.codec metadata.codec)
  else match metadata.dictionaryPageOffset with
    | none =>
      (FlatScan.scanColumn limits.plain.groups (FlatScan.decodeInt32Page limits.plain.pages)
        source footerStart field rows column).mapError .plain
    | some _ => do
      let slots ← (DictionaryChunk.scanColumn limits.dictionary source footerStart
        field rows metadata).mapError .dictionary
      let cells := slots.toArray
      if sized : cells.size = rows then .ok ⟨cells, sized⟩
      else .error (.slotCount cells.size)

def readField (limits : Limits) (source : Bytes) (footerStart rows : Nat)
    (item : (FlatScan.Field × Footer.ColumnChunk) × Nat) :
    Except Error (FlatScan.Field × FlatScan.ColumnValues rows) :=
  let ((field, column), index) := item
  (readColumn limits source footerStart field rows column).map (field, ·) |>.mapError
    (.column index field.name)

def scanGroup (limits : Limits) (source : Bytes) (footerStart : Nat)
    (fields : List FlatScan.Field) (group : Footer.RowGroup) : Except Error FlatScan.Batch :=
  let rows := group.numRows.toNat
  if group.numRows < 0 ∨ limits.plain.groups.maxRows < rows then .error .groupRowLimit
  else if limits.plain.groups.maxCells < rows * fields.length then .error .groupCellLimit
  else if fields.length ≠ group.columns.length then
    .error (.columnArity fields.length group.columns.length)
  else do
    let columns ← (fields.zip group.columns).zipIdx.mapM (readField limits source footerStart rows)
    pure ⟨rows, columns⟩

def typedRow (schema : Scan.Schema String Unit) (row : List (Option Int32)) :
    Except Error (Scan.Row schema Cell) :=
  if width : row.length = schema.width then
    .ok (fun index => row[index.val]'(width.symm ▸ index.isLt))
  else .error (.rowWidth schema.width row.length)

/-- A group is published only after every column and row check succeeds. -/
def decodeGroup (limits : Limits) (schema : Scan.Schema String Unit) (fields : List FlatScan.Field) :
    DecodeGroup schema Cell Error := fun snapshot _ group => do
  let batch ← scanGroup limits snapshot.bytes snapshot.footer.start fields group
  batch.rows.mapM (typedRow schema)

end Internal

/-- Bind the full ordered physical schema once and bound total materialization.
The caller supplying a snapshot directly also enforces the input byte cap. -/
def bind (limits : Limits) (schema : Scan.Schema String Unit) : Bind schema Cell Error :=
  fun metadata => do
    let fields ← (FlatScan.flatSchema limits.plain.groups metadata.schema).mapError .schema
    let expected := List.ofFn (fun index => (schema.kind index).1)
    let actual := fields.map (·.name)
    if expected ≠ actual then .error (.schemaNames expected actual)
    else if limits.maxGroups < metadata.rowGroups.length then .error .groupLimit
    else if metadata.numRows < 0 ∨ limits.maxFileRows < metadata.numRows.toNat then
      .error .fileRowLimit
    else if limits.maxFileCells < metadata.numRows.toNat * fields.length then .error .fileCellLimit
    else .ok (Internal.decodeGroup limits schema fields)

/-- Open one bounded byte snapshot and pull complete batches in footer order. -/
def readAll (limits : Limits) (schema : Scan.Schema String Unit) (bytes : Bytes) :
    Events.EventStream String Cell (Snapshot.Error Error) :=
  if limits.maxFileBytes < bytes.length then .error (.input .fileByteLimit)
  else Snapshot.readAll limits.plain.snapshot (bind limits schema) bytes

end Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary
