module

public import Silmaril.Formats.Csv.ParquetIpc.Defs
public import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Arrow.Defs
import Silmaril.Proofs.Formats.Csv.ParquetIpc.Correctness

/-! Completion and readback for the checked CSV, Parquet and IPC composition. -/

public section

namespace Silmaril.Formats.Csv.ParquetIpc

open Silmaril.Relational
open Silmaril.Formats.Parquet
open Snapshot.FlatInt32 (Cell)
open Snapshot.FlatInt32.ToCsv (csvSchema codecs)
open Silmaril.Formats.Relational.NamedTable (Packed)

variable {Name : Type*} [DecidableEq Name]
variable {db : Packed Name Csv.Field Cell} {name : Name} {schema : Scan.Schema String Unit}
variable {limits : Limits} {wire : Csv.Bytes}

/-- Completion follows from an admitted Parquet write, matching snapshot limits,
and IPC admission of the original CSV under the shared schema. -/
theorem convert_of_admitted {written : FlatInt32Writer.FromCsv.Result Name} {ipc : KBytes}
    (parquet : FlatInt32Writer.FromCsv.convert db name schema limits.csv limits.parquet wire = .ok written)
    (matching : ∀ rows, Csv.Typed.Utf8.decode (csvSchema schema) codecs wire = .ok rows →
      limits.snapshot = limits.parquet.snapshotLimits (FlatInt32Writer.FromCsv.writerInput schema rows))
    (ipcAdmitted : Arrow.FromCsv.Stream.emitCsvUtf8 limits.ipc (fields schema) wire = .ok ipc) :
    ∃ result, convert db name schema limits wire = .ok result :=
  Proofs.Formats.Csv.ParquetIpc.convert_of_admitted parquet matching ipcAdmitted

/-- Successful composition at the matching snapshot limits returns the exact
named update, the original ordered nullable rows at snapshot EOS and CSV
readback, and the same ordered fields and rows on checked IPC readback. -/
theorem convert_readback {result : Result Name}
    (converted : convert db name schema limits wire = .ok result)
    (matching : ∀ rows, Csv.Typed.Utf8.decode (csvSchema schema) codecs wire = .ok rows →
      limits.snapshot = limits.parquet.snapshotLimits (FlatInt32Writer.FromCsv.writerInput schema rows)) :
    db name = none ∧ ∃ rows : Csv.Typed.Table (csvSchema schema) Cell,
      Csv.Typed.Utf8.decode (csvSchema schema) codecs wire = .ok rows ∧
      result.db = Function.update db name (some ⟨csvSchema schema, rows⟩) ∧
      (Snapshot.FlatInt32.ToCsv.readEvents limits.snapshot schema result.parquet).collect =
        .ok ⟨⟨csvSchema schema, rows⟩, .eos⟩ ∧
      Csv.Typed.Utf8.decode (csvSchema schema) codecs result.csv = .ok rows ∧
      Arrow.readRows limits.ipc result.ipc =
        .ok ⟨fields schema, [rows.map fun row => List.ofFn fun i => (row i).map Arrow.Value.int32]⟩ :=
  Proofs.Formats.Csv.ParquetIpc.convert_readback converted matching

end Silmaril.Formats.Csv.ParquetIpc
