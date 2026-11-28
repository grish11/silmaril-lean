module

public import Silmaril.Formats.Arrow.FileReader.Defs
public import Silmaril.Formats.Csv.ParquetIpc.FromIpc.Defs

/-! Checked flat Arrow IPC files to the existing nullable INT32 Parquet writer. -/

@[expose] public section

namespace Silmaril.Formats.Csv.ParquetIpc.FromFile

open Silmaril.Relational
open Silmaril.Formats.Relational.NamedTable (Packed)
open Parquet
open Snapshot.FlatInt32 (Cell)

/-- Keep the file reader's exact checked schema and ordered indexed batches. -/
def readObserved (limits : Arrow.ObservationLimits) (input : KBytes) :
    Except Arrow.Error Arrow.ObservedStream :=
  (Arrow.FileReader.readRows limits input).map fun file => ⟨file.fields, file.batches⟩

/-- Consume the checked file at a vacant name. Handoff uses the existing
typed rows directly, with no CSV serialization or parsing. -/
def convert {Name : Type*} [DecidableEq Name] (db : Packed Name Csv.Field Cell) (name : Name)
    (schema : Scan.Schema String Unit) (ipcLimits : Arrow.ObservationLimits)
    (parquetLimits : FlatInt32Writer.Limits) (input : KBytes) :
    Except FromIpc.Error (FlatInt32Writer.FromCsv.Result Name) :=
  FromIpc.convertWithReader (readObserved ipcLimits) db name schema parquetLimits input

end Silmaril.Formats.Csv.ParquetIpc.FromFile
