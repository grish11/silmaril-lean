module

public import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Defs
public import Batteries.Data.List.Basic
import Silmaril.Formats.Parquet.FlatInt32Writer.Thms
import Silmaril.Proofs.Formats.Parquet.FlatInt32Writer.Readback.Decode
import Silmaril.Formats.Parquet.FlatScan.RoundTrip.Thms
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatInt32Writer.Readback

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.FlatInt32Writer

private theorem scanChunk {limits : Limits} {input : Input} {output : Encoded} {column : Column}
    {chunk : Chunk} (same : chunk.column = column)
    (count : column.values.numValues = input.rowCount)
    (checked : chunk.Checked limits output.bytes output.footer.start input.rowCount)
    (header : chunk.frame.value = column.values.header) (fits : column.values.Fits limits.page)
    (framed : Page.readChunk limits.pageReader output.bytes chunk.index.span = .ok [chunk.frame])
    (decoded : FlatScan.decodeInt32Page limits.page.scalar column.scanField chunk.frame.value
      (Footer.fileBytes output.bytes chunk.frame.payload.start chunk.frame.payload.stop) =
        .ok column.values.slots) :
    ∃ cells, FlatScan.scanColumn (limits.scanLimits input) (FlatScan.decodeInt32Page limits.page.scalar)
      output.bytes output.footer.start column.scanField input.rowCount (chunk.index.metadata input.rowCount) =
        .ok cells ∧ cells.cells.toList = column.values.slots := by
  have slotCount : column.values.slots.length = input.rowCount := by
    rw [← count]
    rcases column with ⟨_, values⟩
    cases values <;> simp [PlainV1Writer.Input.slots, PlainV1Writer.Input.numValues]
  have required : column.scanField.layout = .required → column.values.slots.any Option.isNone = false := by
    rcases column with ⟨_, values⟩
    cases values <;> simp [Column.scanField, PlainV1Writer.Input.slots, List.any_map, Function.comp_def]
  apply FlatScan.scanColumn_singleV1 (bodySize := column.values.bodySize) (span := chunk.index.span)
    (frame := chunk.frame)
  · exact Nat.le_refl _
  · exact fits.2.2.2.2.1
  · simp [Compact.ColumnIndex.metadata, Chunk.index, Column.scanField, same]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact checked.1
  · exact framed
  · simpa only [PlainV1Writer.Input.header, count] using header
  · exact decoded
  · exact slotCount
  · exact required

private theorem zipObservations {ε : Type} {limits : FlatScan.Limits} {decoder : FlatScan.DecodePage ε}
    {source : Bytes} {footerStart rows : Nat} {columns : List Column} {chunks : List Chunk}
    (ready : List.Forall₂ (fun column chunk => ∃ cells,
      FlatScan.scanColumn limits decoder source footerStart column.scanField rows (chunk.index.metadata rows) =
        .ok cells ∧ cells.cells.toList = column.values.slots) columns chunks) :
    List.Forall₂ (fun pair observation => pair.1 = observation.1 ∧
      ∃ cells, FlatScan.scanColumn limits decoder source footerStart pair.1 rows pair.2 = .ok cells ∧
        cells.cells.toList = observation.2)
      ((columns.map Column.scanField).zip (chunks.map fun chunk => chunk.index.metadata rows))
      (columns.map Column.scanObservation) := by
  induction ready with
  | nil => exact .nil
  | cons head _ ih => exact .cons ⟨rfl, head⟩ ih

private theorem leafSchema {columns : List Column} {chunks : List Chunk}
    (aligned : List.Forall₂ (fun column chunk => chunk.column = column) columns chunks) :
    chunks.map (fun chunk => chunk.index.schema) =
      (columns.map Column.scanField).map (fun field =>
        ⟨some .int32, none, some (if field.layout = .required then .required else .optional), field.name, none⟩) := by
  induction aligned with
  | nil => rfl
  | @cons column chunk _ _ same _ ih =>
    simp only [List.map_cons, ih, List.cons.injEq, and_true]
    rcases column with ⟨_, values⟩
    cases values <;> simp [Chunk.index, Compact.ColumnIndex.schema, Column.scanField, same]

theorem emit_scanFileRowGroup {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    ∃ batch, FlatScan.scanFileRowGroup (limits.scanLimits input) (FlatScan.decodeInt32Page limits.page.scalar)
      output.bytes 0 = .ok batch ∧ batch.rowCount = input.rowCount ∧
      batch.columns.map (fun (field, cells) => (field, cells.cells.toList)) =
        input.columns.map Column.scanObservation ∧ batch.rows = input.rows := by
  obtain ⟨valid, checked, metadata, _, _⟩ := emit_layout written
  have columns := emit_columns written
  have decoded := emit_decodeScanPages written
  have ready : List.Forall₂ (fun column chunk => ∃ cells,
      FlatScan.scanColumn (limits.scanLimits input) (FlatScan.decodeInt32Page limits.page.scalar)
        output.bytes output.footer.start column.scanField input.rowCount (chunk.index.metadata input.rowCount) =
        .ok cells ∧ cells.cells.toList = column.values.slots) input.columns output.chunks := by
    have counted := (List.forall₂_and_left (p := fun column : Column =>
      column.values.numValues = input.rowCount) _ _).2
      ⟨fun column present => (valid.2.2.2.2 column present).1, columns⟩
    exact counted.mp (fun _ _ ⟨count, same, located, header, fits, _⟩ ⟨_, framed, page⟩ =>
      scanChunk same count located header fits framed page) decoded
  have read := checked.2.2.2.1
  rw [metadata] at read
  have schemaOk := FlatScan.flatSchema_of_fields (ε := FlatScan.AdapterError)
    (limits := limits.scanLimits input) "schema" (input.columns.map Column.scanField)
    (by simp [Limits.scanLimits]) (by simpa [List.map_map, Function.comp_def, Column.scanField] using valid.2.2.2.1)
  rw [← leafSchema (columns.imp (fun _ _ related => related.1))] at schemaOk
  have schemaWidth : (input.columns.map Column.scanField).length = (output.chunks.map Chunk.index).length := by
    simpa using columns.length_eq
  rw [schemaWidth] at schemaOk
  have recovered := FlatScan.scanFileRowGroup_single
    (limits := limits.scanLimits input) (decoder := FlatScan.decodeInt32Page limits.page.scalar)
    (source := output.bytes) (footer := output.footer)
    (schema := Compact.schemaRoot output.chunks.length :: output.chunks.map (fun chunk => chunk.index.schema))
    (rows := input.rowCount) (schemaFields := input.columns.map Column.scanField)
    (chunks := output.chunks.map (fun chunk => chunk.index.metadata input.rowCount))
    (totalSize := ((output.chunks.map Chunk.index).map Compact.ColumnIndex.size).sum)
    (expected := input.columns.map Column.scanObservation)
  have arity : (input.columns.map Column.scanField).length =
      (output.chunks.map (fun chunk => chunk.index.metadata input.rowCount)).length := by
    simpa only [List.length_map] using columns.length_eq
  have full := recovered
    (by simpa only [Limits.scanLimits, Compact.metadata, List.length_map, List.map_map, Function.comp_def] using read)
    (by simpa only [Compact.schemaRoot, List.length_map] using schemaOk)
    (Nat.le_refl _) (by simp [Limits.scanLimits]) arity (zipObservations ready)
  obtain ⟨batch, run, rows, observed⟩ := full
  refine ⟨batch, run, rows, observed, ?_⟩
  have values := congrArg (List.map Prod.snd) observed
  simp only [List.map_map, Function.comp_def, Column.scanObservation] at values
  have cellLists : (batch.columns.map fun (_, cells) => cells.cells.toList) =
      input.columns.map (·.values.slots) := by
    rw [← values]
  rw [FlatScan.rows_eq_fold, cellLists, rows]
  rfl

end Silmaril.Proofs.Formats.Parquet.FlatInt32Writer.Readback
