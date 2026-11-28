module

public import Silmaril.Formats.Arrow.MixedFlat.File.Window.Projection.Thms
import Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Window.Projection.Strict

public section

namespace Silmaril.Formats.Arrow.MixedFlat.File.Window

open Silmaril.Relational

/-- After successful strict traversal in footer order, an indexed projection
through the full carrier window agrees at each batch ordinal. A present
batch retains its row count, even at width zero, and each output position
keeps its exact descriptor and column. The agreement requires every strict
record read to succeed under the same limits. -/
theorem Index.readProjectedAt_strict {limits : MixedFlat.Limits} {input : KBytes}
    {strict : MixedFlat.File.Index input} {window : Index input 0 input.len}
    (strictRead : MixedFlat.File.readIndex limits.observation.ipc input = .ok strict)
    (windowRead : readIndex limits.observation.ipc input 0 input.len = .ok window)
    {batches : List MixedFlat.Observed}
    (drained : strict.footer.blocks.mapM
      (MixedFlat.File.readRecord limits input strict.footer.fields) = .ok batches)
    (projection : Scan.Projection window.projectionSchema) (n : Nat) :
    match batches[n]? with
    | none => window.readProjectedAt limits n projection = .ok none
    | some batch =>
      ∃ output, window.readProjectedAt limits n projection = .ok (some output) ∧
        output.rowCount = batch.rowCount ∧ output.columns.length = projection.width ∧
        ∀ i : Fin projection.width, output.columns[i.val]? = batch.columns[(projection.index i).val]? :=
  Proofs.Formats.Arrow.MixedFlat.File.Window.Projection.Strict.readProjectedAt_strict
    strictRead windowRead drained projection n

end Silmaril.Formats.Arrow.MixedFlat.File.Window
