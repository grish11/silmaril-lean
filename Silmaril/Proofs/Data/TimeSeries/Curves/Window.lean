module

public import Silmaril.Data.TimeSeries.Curves.Defs

public section

namespace Silmaril.Proofs.Data.TimeSeries.Curves.Window

open Set
open scoped ContDiff Manifold
open Silmaril.Data.TimeSeries.Curves

variable {M E H : Type*} [TopologicalSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  {a b : ℝ} [h : Fact (a < b)]

theorem contMDiffOn_iff (f : ℝ → M) :
    ContMDiffOn 𝓘(ℝ) I ∞ f (Icc a b) ↔
      ContMDiff (𝓡∂ 1) I ∞ (fun t : Icc a b => f t) := by
  constructor
  · intro hf
    exact (Silmaril.Data.TimeSeries.Curves.Window.ofContMDiffOn f hf).contMDiff
  · intro hf
    exact (contMDiffOn_comp_projIcc_iff.mpr hf).congr
      (fun t ht => by simp [projIcc_of_mem h.out.le ht])

end Silmaril.Proofs.Data.TimeSeries.Curves.Window
