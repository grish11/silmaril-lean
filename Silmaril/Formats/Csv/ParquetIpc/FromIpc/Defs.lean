module

public import Silmaril.Formats.Csv.ParquetIpc.Defs

/-! Checked Arrow IPC to the flat nullable INT32 Parquet writer. -/

@[expose] public section

namespace Silmaril.Formats.Csv.ParquetIpc.FromIpc

open Silmaril.Relational
open Silmaril.Formats.Parquet
open Silmaril.Formats.Relational.NamedTable (Packed)
open Snapshot.FlatInt32 (Cell)
open Snapshot.FlatInt32.ToCsv (csvSchema)

inductive Error where
  | nameConflict
  | input (reason : Arrow.ToCsv.InputError)
  | schemaMismatch
  | writeParquet (reason : FlatInt32Writer.FromCsv.Error)
  deriving DecidableEq

/-- Move checked Arrow cells to the corresponding typed CSV positions. -/
def toRows (schema : Scan.Schema String Unit)
    (rows : Scan.Table (Arrow.ToCsv.schemaOf (fields schema)) Arrow.ToCsv.Cell) :
    Csv.Typed.Table (csvSchema schema) Cell :=
  rows.map fun row i =>
    let index : Fin (Arrow.ToCsv.schemaOf (fields schema)).width :=
      i.cast (by simp [Arrow.ToCsv.schemaOf, fields, csvSchema])
    cast (by simp [Arrow.ToCsv.Cell, Arrow.ToCsv.schemaOf, Arrow.ToCsv.labelOf, fields,
      Function.comp_def]) (row index)

/-- Require complete IPC readback with the declared ordered nullable INT32
fields. Reuse the typed CSV row adapter and write those rows directly. -/
def convert {Name : Type*} [DecidableEq Name] (db : Packed Name Csv.Field Cell) (name : Name)
    (schema : Scan.Schema String Unit) (ipcLimits : Arrow.ObservationLimits)
    (parquetLimits : FlatInt32Writer.Limits) (input : KBytes) :
    Except Error (FlatInt32Writer.FromCsv.Result Name) :=
  if (db name).isSome then .error .nameConflict
  else
    match Arrow.readRows ipcLimits input with
    | .error reason => .error (.input (.ipc reason))
    | .ok observed =>
      if observed.fields = fields schema then
        match Arrow.ToCsv.typedRows ⟨fields schema, observed.batches⟩ with
        | .error reason => .error (.input reason)
        | .ok rows =>
          (FlatInt32Writer.FromCsv.convertRows db name schema parquetLimits (toRows schema rows)).mapError
            .writeParquet
      else .error .schemaMismatch

end Silmaril.Formats.Csv.ParquetIpc.FromIpc
