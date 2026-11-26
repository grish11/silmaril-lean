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

/-- Consume the completed observation supplied by an IPC reader. The typed
row check and Parquet writer enforce the declared nullable INT32 schema. -/
def convertWithReader {Name : Type*} [DecidableEq Name]
    (read : KBytes → Except Arrow.Error Arrow.ObservedStream)
    (db : Packed Name Csv.Field Cell) (name : Name)
    (schema : Scan.Schema String Unit) (parquetLimits : FlatInt32Writer.Limits) (input : KBytes) :
    Except Error (FlatInt32Writer.FromCsv.Result Name) :=
  if (db name).isSome then .error .nameConflict
  else
    match read input with
    | .error reason => .error (.input (.ipc reason))
    | .ok observed =>
      if observed.fields = fields schema then
        match Arrow.ToCsv.typedRows ⟨fields schema, observed.batches⟩ with
        | .error reason => .error (.input reason)
        | .ok rows =>
          (FlatInt32Writer.FromCsv.convertRows db name schema parquetLimits (toRows schema rows)).mapError
            .writeParquet
      else .error .schemaMismatch

/-- Require complete stream readback with the declared ordered nullable
INT32 fields and pass the checked rows directly to the Parquet writer. -/
def convert {Name : Type*} [DecidableEq Name] (db : Packed Name Csv.Field Cell) (name : Name)
    (schema : Scan.Schema String Unit) (ipcLimits : Arrow.ObservationLimits)
    (parquetLimits : FlatInt32Writer.Limits) (input : KBytes) :
    Except Error (FlatInt32Writer.FromCsv.Result Name) :=
  convertWithReader (Arrow.readRows ipcLimits) db name schema parquetLimits input

end Silmaril.Formats.Csv.ParquetIpc.FromIpc
