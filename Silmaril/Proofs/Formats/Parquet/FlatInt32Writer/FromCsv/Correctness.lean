module

public import Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv.Defs
public import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Defs
import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Thms
import Silmaril.Formats.Parquet.FlatInt32Writer.Thms
import Silmaril.Formats.Relational.NamedTable.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatInt32Writer.FromCsv

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv
open Silmaril.Formats.Relational.NamedTable (Packed importCollected importCollected_ok_iff)
open Silmaril.Formats.Parquet.Snapshot.FlatInt32 (Cell)
open Silmaril.Formats.Parquet.Snapshot.FlatInt32.ToCsv (csvSchema codecs)

variable {Name : Type*} [DecidableEq Name]
variable {db : Packed Name Csv.Field Cell} {name : Name} {schema : Scan.Schema String Unit}
variable {csvLimits : CsvLimits} {parquetLimits : FlatInt32Writer.Limits} {wire : Csv.Bytes}

private theorem readCsv_ok {rows : Csv.Typed.Table (csvSchema schema) Cell}
    (read : readCsv csvLimits schema wire = .ok rows) :
    wire.length ≤ csvLimits.maxBytes ∧ schema.width ≤ csvLimits.maxColumns ∧
      rows.length ≤ csvLimits.maxRows ∧ Csv.Typed.Utf8.decode (csvSchema schema) codecs wire = .ok rows := by
  unfold readCsv at read
  split at read
  · cases read
  · rename_i bytesBound
    split at read
    · cases read
    · rename_i widthBound
      cases decoded : Csv.Typed.Utf8.decode (csvSchema schema) codecs wire with
      | error reason => simp [decoded] at read
      | ok data =>
        simp only [decoded] at read
        split at read
        · cases read
        · rename_i rowBound
          cases read
          exact ⟨Nat.le_of_not_gt bytesBound, Nat.le_of_not_gt widthBound, Nat.le_of_not_gt rowBound, rfl⟩

private theorem install_ok (vacant : db name = none) (rows : Csv.Typed.Table (csvSchema schema) Cell) :
    importCollected (Error := Csv.Typed.Error) db name (csvSchema schema)
      (.ok ⟨⟨csvSchema schema, rows⟩, .eos⟩) =
      .ok (Function.update db name (some ⟨csvSchema schema, rows⟩)) :=
  (importCollected_ok_iff db _ name (csvSchema schema) _).mpr ⟨vacant, rows, rfl, rfl⟩

theorem convert_parquet_error (vacant : db name = none)
    {rows : Csv.Typed.Table (csvSchema schema) Cell} {reason : FlatInt32Writer.Error}
    (read : readCsv csvLimits schema wire = .ok rows)
    (written : FlatInt32Writer.emit parquetLimits (writerInput schema rows) = .error reason) :
    convert db name schema csvLimits parquetLimits wire = .error (.parquet reason) := by
  simp only [convert, vacant, Option.isSome_none, Bool.false_eq_true, ite_false, read]
  rw [show _ from install_ok vacant rows]
  rw [written]

private theorem convert_stages {result : Result Name}
    (converted : convert db name schema csvLimits parquetLimits wire = .ok result) :
    db name = none ∧
      ∃ (rows : Csv.Typed.Table (csvSchema schema) Cell) (output : FlatInt32Writer.Encoded),
        readCsv csvLimits schema wire = .ok rows ∧
        FlatInt32Writer.emit parquetLimits (writerInput schema rows) = .ok output ∧
        result = ⟨Function.update db name (some ⟨csvSchema schema, rows⟩), output.bytes⟩ := by
  cases existing : db name with
  | some table => simp [convert, existing] at converted
  | none =>
    simp only [convert, existing, Option.isSome_none, Bool.false_eq_true, ite_false] at converted
    cases read : readCsv csvLimits schema wire with
    | error reason => simp [read] at converted
    | ok rows =>
      simp only [read, install_ok existing rows] at converted
      cases written : FlatInt32Writer.emit parquetLimits (writerInput schema rows) with
      | error reason => simp [written] at converted
      | ok encoded =>
        rw [written] at converted
        change Except.ok
          { db := Function.update db name (some ⟨csvSchema schema, rows⟩), bytes := encoded.bytes } =
          .ok result at converted
        cases converted
        exact ⟨rfl, rows, encoded, rfl, written, rfl⟩

theorem convert_written {result : Result Name}
    (converted : convert db name schema csvLimits parquetLimits wire = .ok result) :
    db name = none ∧
      ∃ (rows : Csv.Typed.Table (csvSchema schema) Cell) (output : FlatInt32Writer.Encoded),
        Csv.Typed.Utf8.decode (csvSchema schema) codecs wire = .ok rows ∧
        FlatInt32Writer.emit parquetLimits (writerInput schema rows) = .ok output ∧
        result = ⟨Function.update db name (some ⟨csvSchema schema, rows⟩), output.bytes⟩ := by
  obtain ⟨vacant, rows, output, read, written, resultEq⟩ := convert_stages converted
  exact ⟨vacant, rows, output, (readCsv_ok read).2.2.2, written, resultEq⟩

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
          List.ofFn (fun i => (⟨(schema.kind i).1, .optional⟩, rows.map (· i))) := by
  obtain ⟨vacant, rows, output, read, written, rfl⟩ := convert_stages converted
  obtain ⟨bytesBound, widthBound, rowBound, decoded⟩ := readCsv_ok read
  obtain ⟨batch, scanned, rowCount, columns, _⟩ := FlatInt32Writer.emit_scanFileRowGroup written
  have fileBound := (FlatInt32Writer.emit_layout written).2.1.1
  refine ⟨vacant, bytesBound, widthBound, fileBound, rows, batch, rowBound, decoded, rfl, scanned, rowCount, ?_⟩
  rw [columns]
  simp [writerInput, List.map_ofFn, Function.comp_def, FlatInt32Writer.Column.scanObservation,
    FlatInt32Writer.Column.scanField, PlainV1Writer.Input.slots, csvSchema]

end Silmaril.Proofs.Formats.Parquet.FlatInt32Writer.FromCsv
