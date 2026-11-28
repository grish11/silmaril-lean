module

public import Silmaril.Formats.Csv.ParquetIpc.FromFile.Defs
public import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Defs
import Silmaril.Formats.Arrow.FileReader.Thms
import Silmaril.Formats.Csv.ParquetIpc.FromIpc.Thms

public section

namespace Silmaril.Proofs.Formats.Csv.ParquetIpc.FromFile

open Silmaril.Formats Silmaril.Relational
open Silmaril.Formats.Csv.ParquetIpc (fields)
open Silmaril.Formats.Csv.ParquetIpc.FromFile
open Silmaril.Formats.Relational.NamedTable (Packed)
open Parquet
open Snapshot.FlatInt32 (Cell)
open Snapshot.FlatInt32.ToCsv (csvSchema)

variable {Name : Type*} [DecidableEq Name]
variable {db : Packed Name Csv.Field Cell} {name : Name} {schema : Scan.Schema String Unit}
variable {ipcLimits : Arrow.ObservationLimits} {parquetLimits : FlatInt32Writer.Limits} {input : KBytes}

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
      batch.rows.map (List.map (Option.map Arrow.Value.int32)) = file.batches.flatten := by
  obtain ⟨vacant, observed, rows, batch, read, exactFields, updated, scanned, columns, count, slots⟩ :=
    Csv.ParquetIpc.FromIpc.convertWithReader_readback converted
  cases fileRead : Arrow.FileReader.readRows ipcLimits input with
  | error cause => simp [readObserved, fileRead, Except.map] at read
  | ok file =>
    have same : (⟨file.fields, file.batches⟩ : Arrow.ObservedStream) = observed := by
      simpa [readObserved, fileRead, Except.map] using read
    subst observed
    obtain ⟨index, indexed, _, blocks, readAt⟩ := Arrow.FileReader.readRows_indexed fileRead
    exact ⟨vacant, file, index, rows, batch, rfl, indexed, exactFields, blocks, readAt,
      updated, scanned, columns, count, slots⟩

end Silmaril.Proofs.Formats.Csv.ParquetIpc.FromFile
