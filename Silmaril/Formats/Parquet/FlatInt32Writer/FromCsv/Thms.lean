module

public import Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv.Defs
public import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Defs
import Silmaril.Proofs.Formats.Parquet.FlatInt32Writer.FromCsv.Correctness

public section

namespace Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv

open Silmaril.Relational
open Silmaril.Formats.Relational.NamedTable (Packed)
open Silmaril.Formats.Parquet.Snapshot.FlatInt32 (Cell)
open Silmaril.Formats.Parquet.Snapshot.FlatInt32.ToCsv (csvSchema codecs)

variable {Name : Type*} [DecidableEq Name]
variable {db : Packed Name Csv.Field Cell} {name : Name} {schema : Scan.Schema String Unit}
variable {csvLimits : CsvLimits} {parquetLimits : FlatInt32Writer.Limits} {wire : Csv.Bytes}

/-- Success identifies the exact named update and independently readable file.
The scanner observes the declared fields and all nullable slots in order. -/
theorem convert_readback {result : Result Name}
    (converted : convert db name schema csvLimits parquetLimits wire = .ok result) :
    db name = none ∧ wire.length ≤ csvLimits.maxBytes ∧ schema.width ≤ csvLimits.maxColumns ∧
      result.bytes.length ≤ parquetLimits.maxFileBytes ∧
      ∃ (rows : Csv.Typed.Table (csvSchema schema) Cell) (batch : FlatScan.Batch),
        rows.length ≤ csvLimits.maxRows ∧
        Csv.Typed.Utf8.decode (csvSchema schema) codecs wire = .ok rows ∧
        result.db = Function.update db name (some ⟨csvSchema schema, rows⟩) ∧
        FlatScan.scanFileRowGroup (parquetLimits.scanLimits (writerInput schema rows))
          (FlatScan.decodeInt32Page parquetLimits.page.scalar) result.bytes 0 = .ok batch ∧
        batch.rowCount = rows.length ∧
        batch.columns.map (fun (field, values) => (field, values.cells.toList)) =
          List.ofFn (fun i => (⟨(schema.kind i).1, .optional⟩, rows.map (· i))) :=
  Proofs.Formats.Parquet.FlatInt32Writer.FromCsv.convert_readback converted

/-- A writer failure at a vacant destination returns the writer error alone. -/
theorem convert_parquet_error (vacant : db name = none)
    {rows : Csv.Typed.Table (csvSchema schema) Cell} {reason : FlatInt32Writer.Error}
    (read : readCsv csvLimits schema wire = .ok rows)
    (written : FlatInt32Writer.emit parquetLimits (writerInput schema rows) = .error reason) :
    convert db name schema csvLimits parquetLimits wire = .error (.parquet reason) :=
  Proofs.Formats.Parquet.FlatInt32Writer.FromCsv.convert_parquet_error vacant read written

/-- An occupied destination returns the existing named-table conflict. -/
theorem convert_name_conflict {entry} (occupied : db name = some entry) :
    convert db name schema csvLimits parquetLimits wire = .error (.destination .nameConflict) := by
  simp [convert, occupied]

end Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv
