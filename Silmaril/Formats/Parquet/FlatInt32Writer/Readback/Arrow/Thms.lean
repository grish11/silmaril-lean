module

public import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Arrow.Defs
import Silmaril.Proofs.Formats.Parquet.FlatInt32Writer.Readback.Arrow

/-! Checked file readback and post-read logical projection into Arrow events. -/

public section

namespace Silmaril.Formats.Parquet.FlatInt32Writer

open Silmaril.Relational Silmaril.Formats.Arrow
open Snapshot.FlatInt32 (Cell)

/-- A successful writer opens with its full declared physical schema and
emits one Arrow batch with the original ordered nullable rows, then EOS. -/
theorem emit_snapshot_readAll {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    ∃ rows : Scan.Table input.arrowSchema Cell, rows.map List.ofFn = input.rows ∧
      rows.length = input.rowCount ∧
      Snapshot.FlatInt32.readAll (limits.snapshotLimits input) input.arrowSchema output.bytes =
        .ok ⟨input.arrowSchema, ⟨[AlignedColumns.ofRows rows], .eos⟩⟩ :=
  Proofs.Formats.Parquet.FlatInt32Writer.Readback.emit_snapshot_readAll written

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
      (trace.scan projection keep).batches.map (·.rowCount) = [(Scan.select keep rows).length] :=
  Proofs.Formats.Parquet.FlatInt32Writer.Readback.emit_snapshot_scan written projection keep

end Silmaril.Formats.Parquet.FlatInt32Writer
