module

public import Silmaril.Formats.Csv.ParquetIpc.FromIpc.Defs
public import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Defs
import Silmaril.Formats.Arrow.ToCsv.Thms
import Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv.Thms
import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Thms

public section

namespace Silmaril.Proofs.Formats.Csv.ParquetIpc.FromIpc

open Silmaril.Relational Silmaril.Formats
open Silmaril.Formats.Csv.ParquetIpc (fields)
open Silmaril.Formats.Csv.ParquetIpc.FromIpc
open Silmaril.Formats.Parquet
open Silmaril.Formats.Relational.NamedTable (Packed)
open Snapshot.FlatInt32 (Cell)
open Snapshot.FlatInt32.ToCsv (csvSchema)

private theorem erase_int32 (kind : Arrow.ToCsv.Kind) (isInt32 : kind.1 = .int32)
    (cell : Option (Arrow.ToCsv.Cell kind)) :
    Arrow.ToCsv.eraseCell kind cell =
      Option.map Arrow.Value.int32 (cast (by cases kind with | mk kind nullable => cases isInt32; rfl) cell) := by
  cases kind with
  | mk type nullable =>
    cases isInt32
    rfl

private theorem erase_toRows (schema : Scan.Schema String Unit)
    (rows : Scan.Table (Arrow.ToCsv.schemaOf (fields schema)) Arrow.ToCsv.Cell) :
    ((toRows schema rows).map List.ofFn).map (List.map (Option.map Arrow.Value.int32)) =
      rows.map (Arrow.ToCsv.eraseRow (fields schema)) := by
  simp only [toRows, List.map_map, Function.comp_def, List.map_ofFn]
  apply List.map_congr_left
  intro row _
  apply List.ext_getElem
  · simp [Arrow.ToCsv.eraseRow, Arrow.ToCsv.schemaOf, fields, csvSchema]
  · intro index left right
    simp only [Arrow.ToCsv.eraseRow, List.getElem_ofFn]
    have isInt32 :
        ((Arrow.ToCsv.schemaOf (fields schema)).kind ⟨index, by
          simpa [Arrow.ToCsv.eraseRow] using right⟩).2.1 = .int32 := by
      simp [Arrow.ToCsv.schemaOf, Arrow.ToCsv.labelOf, fields, Function.comp_def]
    exact (erase_int32 _ isInt32 _).symm

variable {Name : Type*} [DecidableEq Name]
variable {db : Packed Name Csv.Field Cell} {name : Name} {schema : Scan.Schema String Unit}
variable {read : KBytes → Except Arrow.Error Arrow.ObservedStream} {parquetLimits : FlatInt32Writer.Limits} {input : KBytes}

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
      batch.rows.map (List.map (Option.map Arrow.Value.int32)) = observed.batches.flatten := by
  cases occupied : db name with
  | some entry => simp [convertWithReader, occupied] at converted
  | none =>
    simp only [convertWithReader, occupied, Option.isSome_none, Bool.false_eq_true, ite_false] at converted
    cases reading : read input with
    | error reason => simp [reading] at converted
    | ok observed =>
      by_cases matched : observed.fields = fields schema
      · simp only [reading, matched, ite_true] at converted
        cases checked : Arrow.ToCsv.typedRows ⟨fields schema, observed.batches⟩ with
        | error reason => simp [checked] at converted
        | ok typed =>
          simp only [checked] at converted
          cases writing : FlatInt32Writer.FromCsv.convertRows db name schema parquetLimits
              (toRows schema typed) with
          | error reason => simp [writing, Except.mapError] at converted
          | ok output =>
            simp only [writing, Except.mapError, Except.ok.injEq] at converted
            subst result
            obtain ⟨_, encoded, emitted, rfl⟩ := FlatInt32Writer.FromCsv.convertRows_written writing
            obtain ⟨batch, scanned, count, columns, raw⟩ := FlatInt32Writer.emit_scanFileRowGroup emitted
            have typedRaw := Arrow.ToCsv.typedRows_preserve checked
            rw [FlatInt32Writer.FromCsv.writerInput_rows] at raw
            refine ⟨rfl, observed, toRows schema typed, batch, rfl, matched, rfl, scanned, ?_, ?_, ?_⟩
            · have names := congrArg (List.map Prod.fst) columns
              simpa [List.map_map, List.map_ofFn, Function.comp_def, FlatInt32Writer.Column.scanObservation,
                FlatInt32Writer.Column.scanField, FlatInt32Writer.FromCsv.writerInput] using names
            · calc
                batch.rowCount = (toRows schema typed).length := count
                _ = typed.length := by simp only [toRows, List.length_map]
                _ = observed.batches.flatten.length := by
                  simpa only [List.length_map] using congrArg List.length typedRaw
            · rw [raw, erase_toRows]
              exact typedRaw
      · simp only [reading, matched, ite_false, reduceCtorEq] at converted

end Silmaril.Proofs.Formats.Csv.ParquetIpc.FromIpc
