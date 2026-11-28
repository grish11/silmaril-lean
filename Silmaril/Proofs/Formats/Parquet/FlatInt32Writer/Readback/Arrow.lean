module

public import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Arrow.Defs
import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Thms
import Silmaril.Formats.Parquet.FlatInt32Writer.Thms
import Silmaril.Formats.Parquet.FlatScan.Thms
import Silmaril.Formats.Parquet.Snapshot.FlatInt32.Thms
import Silmaril.Formats.Arrow.Events.Thms
import Silmaril.Semantics.Relational.Table.Thms
import Silmaril.Semantics.Relational.Scan.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatInt32Writer.Readback

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Parquet Silmaril.Formats.Parquet.FlatInt32Writer
open Snapshot.FlatInt32 (Cell)

private theorem inputNames (input : Input) :
    List.ofFn (fun index => (input.arrowSchema.kind index).1) =
      (input.columns.map Column.scanField).map (·.name) := by
  apply List.ext_getElem
  · simp [Input.arrowSchema]
  · intro index left right
    simp [Input.arrowSchema, Column.scanField]

/-- A successful writer opens with its full declared physical schema and
emits one Arrow batch with the original ordered nullable rows, then EOS. -/
theorem emit_snapshot_readAll {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    ∃ rows : Scan.Table input.arrowSchema Cell, rows.map List.ofFn = input.rows ∧
      rows.length = input.rowCount ∧
      Snapshot.FlatInt32.readAll (limits.snapshotLimits input) input.arrowSchema output.bytes =
        .ok ⟨input.arrowSchema, ⟨[AlignedColumns.ofRows rows], .eos⟩⟩ := by
  obtain ⟨_, checked, metadata, _, _⟩ := emit_layout written
  obtain ⟨batch, scanned, count, columns, rows⟩ := emit_scanFileRowGroup written
  let indexes := output.chunks.map Chunk.index
  let group : Footer.RowGroup := ⟨indexes.map (fun column => column.metadata input.rowCount),
    (indexes.map Compact.ColumnIndex.size).sum, input.rowCount, none, none⟩
  have singleton : output.metadata.rowGroups = [group] := by
    rw [metadata]
    rfl
  have version : output.metadata.version = 1 := by
    rw [metadata]
    rfl
  have total : (output.metadata.rowGroups.map (·.numRows)).sum = output.metadata.numRows := by
    rw [metadata]
    simp [Compact.metadata]
  have fileRead : Footer.readFooter (limits.scanLimits input).footer output.bytes =
      .ok (output.footer, output.metadata) := checked.2.2.2.1
  have atZero : output.metadata.rowGroups[0]? = some group := by simp [singleton]
  have nonnegative : (output.metadata.rowGroups.all fun g => 0 ≤ g.numRows) = true := by
    simp [singleton, group]
  rw [FlatScan.scanFileRowGroup_of_footer fileRead (.inl version) nonnegative total atZero] at scanned
  have width : batch.columns.length = input.arrowSchema.width := by
    simpa [Input.arrowSchema] using congrArg List.length columns
  obtain ⟨typed, observed, opened⟩ := Snapshot.FlatInt32.readAll_single
    (limits := limits.snapshotLimits input) (schema := input.arrowSchema)
    fileRead checked.2.2.2.2.1 singleton (emit_flatSchema written) (inputNames input) scanned width
  refine ⟨typed, observed.trans rows, ?_, opened⟩
  exact (by simpa using congrArg List.length observed : typed.length = batch.rows.length).trans
    ((FlatScan.rows_length batch).trans count)

/-- On the actual opened trace, keep rows in input order and project arbitrary
typed positions. EOS and one output row per kept row are observed even at
width zero, and the projection may repeat or reorder positions. -/
theorem emit_snapshot_scan {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) (projection : Scan.Projection input.arrowSchema)
    (keep : Scan.Predicate input.arrowSchema Cell) :
    ∃ (rows : Scan.Table input.arrowSchema Cell)
      (trace : Events.Trace input.arrowSchema Cell (Snapshot.Error (Snapshot.FlatInt32.Error Unit))),
      rows.map List.ofFn = input.rows ∧
      Snapshot.FlatInt32.readAll (limits.snapshotLimits input) input.arrowSchema output.bytes =
        .ok ⟨input.arrowSchema, trace⟩ ∧
      (trace.scan projection keep).collect = ⟨⟨projection.schema, projection.scan keep rows⟩, .eos⟩ ∧
      (trace.scan projection keep).collect.table.rowCount = (Scan.select keep rows).length ∧
      (trace.scan projection keep).batches.map (·.rowCount) = [(Scan.select keep rows).length] := by
  obtain ⟨rows, observed, _, opened⟩ := emit_snapshot_readAll written
  let trace : Events.Trace input.arrowSchema Cell (Snapshot.Error (Snapshot.FlatInt32.Error Unit)) :=
    ⟨[AlignedColumns.ofRows rows], .eos⟩
  have flattened : trace.rows = rows := by
    simp [trace, Events.Trace.rows, AlignedColumns.toRows_ofRows]
  refine ⟨rows, trace, observed, opened, ?_, ?_, ?_⟩
  · change Events.Observation.mk ⟨_, (trace.scan projection keep).rows⟩
      (trace.scan projection keep).termination = _
    rw [Events.Trace.rows_scan, flattened, Events.Trace.termination_scan]
  · rw [Events.Trace.rowCount_scan, flattened]
  · change [(AlignedColumns.ofRows (projection.scan keep (AlignedColumns.ofRows rows).toRows)).rowCount] =
      [(Scan.select keep rows).length]
    rw [AlignedColumns.toRows_ofRows]
    change [(projection.scan keep rows).length] = _
    rw [projection.length_scan]

end Silmaril.Proofs.Formats.Parquet.FlatInt32Writer.Readback
