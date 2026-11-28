module

import Silmaril.Data.TimeSeries.Quantization.Thms
import Mathlib.Tactic.NormNum

/-! # Attaining the combined uniform error bound -/

namespace Silmaril.Data.TimeSeries.Quantization.Examples

private noncomputable def timeGrid : Uniform := ⟨2, by norm_num⟩
private noncomputable def valueGrid : Uniform := ⟨4, by norm_num⟩

/-- The identity signal at time 1 has value 1. The timestamp tie gives time 2,
then the value tie gives 4. The total error is 3, the sum of the two half-steps. -/
example : |uniformSamples timeGrid valueGrid (fun t => t) (fun (_ : Fin 1) => 1) 0 - 1| =
    valueGrid.step / 2 + timeGrid.step / 2 := by
  have ht : timeGrid.quantize 1 = 2 := by
    simpa [timeGrid] using timeGrid.quantize_midpoint 0
  have hv := valueGrid.quantize_midpoint 0
  norm_num [show valueGrid.step = 4 from rfl] at hv
  simp only [uniformSamples, ht, hv]
  norm_num [timeGrid, valueGrid]

end Silmaril.Data.TimeSeries.Quantization.Examples
