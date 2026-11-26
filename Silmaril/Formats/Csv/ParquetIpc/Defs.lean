module

public import Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv.Defs
public import Silmaril.Formats.Arrow.FromCsv.Stream.Defs

/-! Compose the shared nullable INT32 profile through Parquet and Arrow IPC. -/

@[expose] public section

namespace Silmaril.Formats.Csv.ParquetIpc

open Silmaril.Relational
open Silmaril.Formats
open Silmaril.Formats.Arrow (ObservationLimits)
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Snapshot.FlatInt32 (Cell)
open Silmaril.Formats.Relational.NamedTable (Packed)

structure Limits where
  csv : FlatInt32Writer.FromCsv.CsvLimits
  parquet : FlatInt32Writer.Limits
  snapshot : Snapshot.FlatInt32.Limits
  ipc : ObservationLimits

inductive Error where
  | writeParquet (reason : FlatInt32Writer.FromCsv.Error)
  | exportCsv (reason : EventStream.Error (Snapshot.Error (Snapshot.FlatInt32.Error Unit)))
  | writeIpc (reason : Arrow.FromCsv.Stream.EmitError)
  deriving DecidableEq

structure Result (Name : Type*) where
  db : Packed Name Csv.Field Cell
  parquet : Silmaril.Formats.Bytes
  csv : Csv.Bytes
  ipc : Silmaril.KBytes

/-- Interpret every declared position as a nullable signed INT32 Arrow field. -/
def fields (schema : Scan.Schema String Unit) : List Arrow.Field :=
  List.ofFn fun i => ⟨(schema.kind i).1, true, .int32⟩

/-- Use the original database for both named operations so they can share
one vacant name. Return the update and wire results after all stages succeed. -/
def convert {Name : Type*} [DecidableEq Name] (db : Packed Name Csv.Field Cell) (name : Name)
    (schema : Scan.Schema String Unit) (limits : Limits) (wire : Csv.Bytes) :
    Except Error (Result Name) :=
  match FlatInt32Writer.FromCsv.convert db name schema limits.csv limits.parquet wire with
  | .error reason => .error (.writeParquet reason)
  | .ok written =>
    match Snapshot.FlatInt32.ToCsv.convert db name schema limits.snapshot written.bytes with
    | .error reason => .error (.exportCsv reason)
    | .ok exported =>
      match Arrow.FromCsv.Stream.emitCsvUtf8 limits.ipc (fields schema) exported.wire with
      | .error reason => .error (.writeIpc reason)
      | .ok ipc => .ok ⟨exported.db, written.bytes, exported.wire, ipc⟩

end Silmaril.Formats.Csv.ParquetIpc
