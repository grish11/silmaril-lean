module

public import Silmaril.Data.TimeSeries.Quantization.Defs
public import Silmaril.Data.TimeSeries.Sampling.Defs

/-! Store quantized readings as typed series and use half steps as nonnegative budgets. -/

@[expose] public section

namespace Silmaril.Data.TimeSeries.Quantization

open scoped NNReal

/-- The maximum rounding error for a single coordinate on the grid. -/
noncomputable def Uniform.halfStep (grid : Uniform) : ℝ≥0 :=
  ⟨grid.step / 2, div_nonneg grid.step_pos.le zero_le_two⟩

/-- Store both axes as integer codes. Evaluate the input signal at the decoded
rounded time before encoding its value. -/
noncomputable def uniformSeries {n : Nat} (timeGrid valueGrid : Uniform)
    (f : ℝ → ℝ) (times : Fin n → ℝ) : Series n Int Int :=
  let time := fun i => timeGrid.encode (times i)
  Series.ofColumns time (fun i => valueGrid.encode (f (timeGrid.decode (time i))))

end Silmaril.Data.TimeSeries.Quantization
