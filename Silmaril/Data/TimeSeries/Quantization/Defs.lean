module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Round

/-! # Uniform quantization on finite time series -/

@[expose] public section

namespace Silmaril.Data.TimeSeries.Quantization

/-- An unbounded, zero-origin real grid with a positive step. -/
structure Uniform where
  step : ℝ
  step_pos : 0 < step

/-- Encode to the closest grid index. At a midpoint, choose the larger index. -/
noncomputable def Uniform.encode (grid : Uniform) (x : ℝ) : ℤ := round (x / grid.step)

/-- Interpret the integer index as a real grid point. -/
noncomputable def Uniform.decode (grid : Uniform) (index : ℤ) : ℝ := (index : ℝ) * grid.step

/-- Replace a real value by its nearest grid point. -/
noncomputable def Uniform.quantize (grid : Uniform) (x : ℝ) : ℝ := grid.decode (grid.encode x)

/-- Round each timestamp, evaluate the signal there, then round its value. -/
noncomputable def uniformSamples {n : Nat} (timeGrid valueGrid : Uniform) (f : ℝ → ℝ)
    (times : Fin n → ℝ) : Fin n → ℝ :=
  fun i => valueGrid.quantize (f (timeGrid.quantize (times i)))

end Silmaril.Data.TimeSeries.Quantization
