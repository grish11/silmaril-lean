module

public import Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.Defs
public import Silmaril.Formats.Arrow.StreamWriter.Defs

/-! Emit a complete primitive Arrow IPC stream from a checked flat INT32
Parquet snapshot after all footer-indexed groups succeed. -/

public section

namespace Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc

open Silmaril.Relational
open FlatInt32 (Cell)

abbrev SourceError := Snapshot.Error FlatInt32Dictionary.Error

inductive Error where
  | source (cause : SourceError)
  | schemaMismatch (actual : List Arrow.Field)
  | writer (cause : Arrow.Error)
  deriving DecidableEq, Repr

@[expose] def schema (fields : List FlatScan.Field) : Scan.Schema String Unit :=
  ⟨fields.length, fun index => (fields[index.val].name, ())⟩

@[expose] def ipcField (field : FlatScan.Field) : Arrow.Field :=
  ⟨field.name, field.layout == .optional, .int32⟩

/-- The original snapshot, ordered descriptor and decoder returned by openSource. -/
structure Bound where
  snapshot : Snapshot.Checked
  fields : List FlatScan.Field
  decode : Snapshot.DecodeGroup (schema fields) Cell FlatInt32Dictionary.Error

/-- Check exact ordered IPC fields before any group is read. -/
@[expose] def openSource (limits : FlatInt32Dictionary.Limits) (expected : List Arrow.Field)
    (input : Bytes) : Except Error Bound := do
  if limits.maxFileBytes < input.length then throw (.source (.input .fileByteLimit))
  let snapshot ← (Snapshot.check limits.plain.snapshot input).mapError .source
  let fields ← (FlatScan.flatSchema limits.plain.groups snapshot.metadata.schema).mapError
    fun cause => .source (.schema (.schema cause))
  let actual := fields.map ipcField
  if actual ≠ expected then throw (.schemaMismatch actual)
  let decode ← (FlatInt32Dictionary.bind limits (schema fields) snapshot.metadata).mapError
    fun cause => .source (.schema cause)
  return ⟨snapshot, fields, decode⟩

/-- Exhaust the footer indices in order, stopping on the first source error. -/
@[expose] def Bound.readGroups (bound : Bound) :
    Except SourceError (List (Reader.RowGroup (schema bound.fields) Cell)) :=
  (List.range bound.snapshot.groupCount).mapM (bound.snapshot.readGroup bound.decode)

/-- An admitted empty group still contributes a batch with an explicit row count. -/
@[expose] def batchInput (fields : List FlatScan.Field) (rows : Reader.RowGroup (schema fields) Cell) :
    Arrow.Writer.BatchInput :=
  let columns := AlignedColumns.ofRows rows
  ⟨columns.rowCount, List.ofFn fun index : Fin fields.length =>
    let field := fields[index.val]
    ⟨field.name, field.layout == .optional, .int32 (columns.values index)⟩⟩

/-- The row observation uses the primitive INT32 constructor at every slot. -/
@[expose] def ipcRows (fields : List FlatScan.Field) (rows : Reader.RowGroup (schema fields) Cell) :
    List Arrow.Row :=
  rows.map fun row => List.ofFn fun index : Fin fields.length =>
    (row index).map Arrow.Value.int32

/-- Emit only after a complete source read. The indexed source API retains
earlier groups on failure, and this conversion returns just the error. -/
@[expose] def convert (limits : FlatInt32Dictionary.Limits) (ipc : Arrow.ObservationLimits)
    (expected : List Arrow.Field) (input : Bytes) : Except Error KBytes := do
  let bound ← openSource limits expected input
  let groups ← bound.readGroups.mapError .source
  (Arrow.StreamWriter.emit ipc expected (groups.map (batchInput bound.fields))).mapError .writer

end Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc
