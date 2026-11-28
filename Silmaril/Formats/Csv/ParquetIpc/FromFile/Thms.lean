module

public import Silmaril.Formats.Csv.ParquetIpc.FromFile.Defs
public import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Defs
import Silmaril.Proofs.Formats.Csv.ParquetIpc.FromFile.Correctness
import Silmaril.Formats.Csv.ParquetIpc.FromIpc.Thms

/-! Indexed file observations and exact Parquet readback at the named boundary. -/

public section

namespace Silmaril.Formats.Csv.ParquetIpc.FromFile

open Silmaril.Relational
open Silmaril.Formats.Csv.ParquetIpc (fields)
open Silmaril.Formats.Relational.NamedTable (Packed)
open Silmaril.Formats.Parquet
open Snapshot.FlatInt32 (Cell)
open Snapshot.FlatInt32.ToCsv (csvSchema)

variable {Name : Type*} [DecidableEq Name]
variable {db : Packed Name Csv.Field Cell} {name : Name} {schema : Scan.Schema String Unit}
variable {ipcLimits : Arrow.ObservationLimits} {parquetLimits : FlatInt32Writer.Limits} {input : KBytes}

/-- At a vacant destination, any file-reader failure returns its original
error. A failing record therefore returns neither a database nor Parquet bytes. -/
theorem convert_read_error {cause : Arrow.Error} (vacant : db name = none)
    (failed : Arrow.FileReader.readRows ipcLimits input = .error cause) :
    convert db name schema ipcLimits parquetLimits input = .error (.input (.ipc cause)) :=
  FromIpc.convertWithReader_error vacant (by simp [readObserved, failed, Except.map])

/-- Success preserves the exact indexed file observations, their ordered
nullable slots, and the sole named update in the writer's OPTIONAL profile. -/
theorem convert_readback {result : FlatInt32Writer.FromCsv.Result Name}
    (converted : convert db name schema ipcLimits parquetLimits input = .ok result) :
    db name = none ∧ ∃ (file : Arrow.FileReader.ObservedFile) (index : Arrow.FileReader.Index input)
      (rows : Csv.Typed.Table (csvSchema schema) Cell) (batch : FlatScan.Batch),
      Arrow.FileReader.readRows ipcLimits input = .ok file ∧
      Arrow.FileReader.readIndex ipcLimits.ipc input = .ok index ∧
      file.fields = fields schema ∧ file.batches.length = index.footer.blocks.length ∧
      (∀ n, index.readRowsAt ipcLimits n = .ok file.batches[n]?) ∧
      result.db = Function.update db name (some ⟨csvSchema schema, rows⟩) ∧
      FlatScan.scanFileRowGroup (parquetLimits.scanLimits (FlatInt32Writer.FromCsv.writerInput schema rows))
        (FlatScan.decodeInt32Page parquetLimits.page.scalar) result.bytes 0 = .ok batch ∧
      batch.columns.map Prod.fst = List.ofFn (fun i => ⟨(schema.kind i).1, .optional⟩) ∧
      batch.rowCount = file.batches.flatten.length ∧
      batch.rows.map (List.map (Option.map Arrow.Value.int32)) = file.batches.flatten :=
  Proofs.Formats.Csv.ParquetIpc.FromFile.convert_readback converted

end Silmaril.Formats.Csv.ParquetIpc.FromFile
