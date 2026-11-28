module

public import Silmaril.Formats.Arrow.MixedFlat.File.Window.Projection.Defs

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.File.Window

open Silmaril.Relational

/-- A successful projection keeps the original row count and selects each
descriptor and column at its exact declared position. -/
theorem Index.readProjectedAt_exact {input : KBytes} {start stop : Nat} (index : Index input start stop)
    {limits : MixedFlat.Limits} {n : Nat} (projection : Scan.Projection index.projectionSchema)
    {observed : MixedFlat.Observed} (read : index.readAt limits n = .ok (some observed)) :
    ∃ output, index.readProjectedAt limits n projection = .ok (some output) ∧
      output.rowCount = observed.rowCount ∧ output.columns.length = projection.width ∧
      ∀ i : Fin projection.width, output.columns[i.val]? = observed.columns[(projection.index i).val]? := by
  unfold Index.readProjectedAt
  split <;> simp_all

theorem Index.readProjectedAt_error {input : KBytes} {start stop : Nat} (index : Index input start stop)
    {limits : MixedFlat.Limits} {n : Nat} (projection : Scan.Projection index.projectionSchema)
    {cause : Error} (read : index.readAt limits n = .error cause) :
    index.readProjectedAt limits n projection = .error cause := by
  unfold Index.readProjectedAt
  split <;> simp_all

theorem Index.readProjectedAt_absent {input : KBytes} {start stop : Nat} (index : Index input start stop)
    {limits : MixedFlat.Limits} {n : Nat} (projection : Scan.Projection index.projectionSchema)
    (read : index.readAt limits n = .ok none) :
    index.readProjectedAt limits n projection = .ok none := by
  unfold Index.readProjectedAt
  split <;> simp_all

end Silmaril.Formats.Arrow.MixedFlat.File.Window
