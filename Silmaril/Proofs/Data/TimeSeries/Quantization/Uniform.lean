module

public import Silmaril.Data.TimeSeries.Quantization.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

open Silmaril.Data.TimeSeries.Quantization

namespace Silmaril.Proofs.Data.TimeSeries.Quantization

theorem encode_midpoint (grid : Uniform) (k : ℤ) :
    grid.encode (((k : ℝ) + 1 / 2) * grid.step) = k + 1 := by
  rw [Uniform.encode, mul_div_cancel_right₀ _ grid.step_pos.ne', round_eq_iff]
  simp only [Set.mem_Ico, Int.cast_add, Int.cast_one]
  constructor <;> linarith

theorem quantize_error (grid : Uniform) (x : ℝ) : |grid.quantize x - x| ≤ grid.step / 2 := by
  have hscaled : |(grid.encode x : ℝ) - x / grid.step| ≤ 1 / 2 := by
    rw [abs_sub_comm]
    exact abs_sub_round (x / grid.step)
  calc
    |grid.quantize x - x| = |((grid.encode x : ℝ) - x / grid.step) * grid.step| := by
      rw [sub_mul, div_mul_cancel₀ _ grid.step_pos.ne']
      rfl
    _ = |(grid.encode x : ℝ) - x / grid.step| * grid.step := by
      rw [abs_mul, abs_of_pos grid.step_pos]
    _ ≤ (1 / 2) * grid.step := mul_le_mul_of_nonneg_right hscaled grid.step_pos.le
    _ = grid.step / 2 := by ring

end Silmaril.Proofs.Data.TimeSeries.Quantization
