module

public import Silmaril.Formats.Csv.ParquetIpc.FromIpc.Defs
public import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Defs
import Silmaril.Proofs.Formats.Csv.ParquetIpc.FromIpc.Correctness

/-! Ordered nullable rows and exact IPC errors through the typed bridge. -/

public section

namespace Silmaril.Formats.Csv.ParquetIpc.FromIpc

open Silmaril.Relational
open Silmaril.Formats.Parquet
open Silmaril.Formats.Relational.NamedTable (Packed)
open Snapshot.FlatInt32 (Cell)
open Snapshot.FlatInt32.ToCsv (csvSchema)

variable {Name : Type*} [DecidableEq Name]
variable {db : Packed Name Csv.Field Cell} {name : Name} {schema : Scan.Schema String Unit}
variable {ipcLimits : Arrow.ObservationLimits} {parquetLimits : FlatInt32Writer.Limits} {input : KBytes}

variable {read : KBytes → Except Arrow.Error Arrow.ObservedStream}

/-- At a vacant name, propagate the exact error returned by the IPC reader. -/
theorem convertWithReader_error {reason : Arrow.Error} (vacant : db name = none)
    (failed : read input = .error reason) :
    convertWithReader read db name schema parquetLimits input =
      .error (.input (.ipc reason)) := by
  simp [convertWithReader, vacant, failed]

/-- At a vacant destination, an IPC read failure returns its exact cause and
no named update or Parquet bytes. This also applies to missing EOS. -/
theorem convert_read_error {reason : Arrow.Error} (vacant : db name = none)
    (read : Arrow.readRows ipcLimits input = .error reason) :
    convert db name schema ipcLimits parquetLimits input = .error (.input (.ipc reason)) :=
  convertWithReader_error vacant read

/-- Converting a completed IPC observation fixes the named update and reads back as the exact
declared OPTIONAL fields and flattened ordered nullable IPC rows. -/
theorem convertWithReader_readback {result : FlatInt32Writer.FromCsv.Result Name}
    (converted : convertWithReader read db name schema parquetLimits input = .ok result) :
    db name = none ∧ ∃ (observed : Arrow.ObservedStream)
      (rows : Csv.Typed.Table (csvSchema schema) Cell) (batch : FlatScan.Batch),
      read input = .ok observed ∧ observed.fields = fields schema ∧
      result.db = Function.update db name (some ⟨csvSchema schema, rows⟩) ∧
      FlatScan.scanFileRowGroup (parquetLimits.scanLimits (FlatInt32Writer.FromCsv.writerInput schema rows))
        (FlatScan.decodeInt32Page parquetLimits.page.scalar) result.bytes 0 = .ok batch ∧
      batch.columns.map Prod.fst = List.ofFn (fun i => ⟨(schema.kind i).1, .optional⟩) ∧
      batch.rowCount = observed.batches.flatten.length ∧
      batch.rows.map (List.map (Option.map Arrow.Value.int32)) = observed.batches.flatten :=
  Proofs.Formats.Csv.ParquetIpc.FromIpc.convertWithReader_readback converted

/-- Successful conversion fixes the named update and reads back as the exact
declared OPTIONAL fields and flattened ordered nullable IPC rows. -/
theorem convert_readback {result : FlatInt32Writer.FromCsv.Result Name}
    (converted : convert db name schema ipcLimits parquetLimits input = .ok result) :
    db name = none ∧ ∃ (observed : Arrow.ObservedStream)
      (rows : Csv.Typed.Table (csvSchema schema) Cell) (batch : FlatScan.Batch),
      Arrow.readRows ipcLimits input = .ok observed ∧ observed.fields = fields schema ∧
      result.db = Function.update db name (some ⟨csvSchema schema, rows⟩) ∧
      FlatScan.scanFileRowGroup (parquetLimits.scanLimits (FlatInt32Writer.FromCsv.writerInput schema rows))
        (FlatScan.decodeInt32Page parquetLimits.page.scalar) result.bytes 0 = .ok batch ∧
      batch.columns.map Prod.fst = List.ofFn (fun i => ⟨(schema.kind i).1, .optional⟩) ∧
      batch.rowCount = observed.batches.flatten.length ∧
      batch.rows.map (List.map (Option.map Arrow.Value.int32)) = observed.batches.flatten :=
  convertWithReader_readback converted

end Silmaril.Formats.Csv.ParquetIpc.FromIpc
