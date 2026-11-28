module

import Silmaril.Data.TimeSeries
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Read a typed relational table, compare its values with additive samples of a
continuous curve, and compute the recorded slope. Both samples are window endpoints. -/

namespace Silmaril.Data.TimeSeries.Examples

open scoped NNReal

noncomputable section

private inductive RecordingColumn
  | timestamp
  | measurement

private def kind : RecordingColumn → Type
  | .timestamp => Nat
  | .measurement => Int

private def row (t : Nat) (x : Int) : Relational.Row kind id
  | .timestamp => t
  | .measurement => x

private def table : Relational.Table kind id := [row 0 2, row 1 4]

private def recorded : Series 2 Nat Int := Series.ofTable table .timestamp .measurement

private def decodeTime (t : Nat) : ℝ := t
private def decodeValue (x : Int) : ℝ := x

private def model : ErrorModel ℝ ℝ Nat Int := ErrorModel.ofDecode decodeTime decodeValue

private def curve : Curves.OpenContinuous ℝ :=
  ⟨fun t => 2 * t + 1, (continuous_const.mul continuous_id).add continuous_const⟩

private def grid : Fin 2 → ℝ := ![0, 1]

private def validTimes (times : Fin 2 → ℝ) : Prop := times = grid

private def decoded : Series 2 ℝ ℝ := recorded.map decodeTime decodeValue

/-- The stored measurements are the samples of the curve plus the same unit error. -/
private theorem decoded_eq_noisy :
    decoded = (Series.sample grid curve).addNoise (fun _ => 1) := by
  apply congrArg Series.mk
  funext i
  fin_cases i
  · change Observation.mk (decodeTime 0) (decodeValue 2) = ⟨0, 2 * 0 + 1 + 1⟩
    norm_num [decodeTime, decodeValue]
  · change Observation.mk (decodeTime 1) (decodeValue 4) = ⟨1, 2 * 1 + 1 + 1⟩
    norm_num [decodeTime, decodeValue]

private theorem sampleError_within (i : Fin 2) :
    (model.sampleError curve grid recorded i).Within ⟨0, 1⟩ := by
  have ht := congrArg (fun s : Series 2 ℝ ℝ => s.timestamps i) decoded_eq_noisy
  have hv := congrArg (fun s : Series 2 ℝ ℝ => s.values i) decoded_eq_noisy
  change decodeTime (recorded.get i).timestamp = grid i at ht
  change decodeValue (recorded.get i).value = curve (grid i) + 1 at hv
  change nndist (grid i) (decodeTime (recorded.get i).timestamp) ≤ 0 ∧
    nndist (curve (grid i)) (decodeValue (recorded.get i).value) ≤ 1
  rw [ht, hv]
  refine ⟨by simp, ?_⟩
  change (↑(nndist (curve (grid i)) (curve (grid i) + 1)) : ℝ) ≤ ↑(1 : ℝ≥0)
  simp

/-- The curve is admitted with zero time error and a unit value budget. -/
example : curve ∈ continuousCandidates model recorded validTimes ⟨0, 1⟩ :=
  ⟨trivial, trivial, grid, rfl, (ErrorModel.seriesError_within_iff _ _ _ _ _).2 sampleError_within⟩

private def windowGrid (i : Fin 2) : Set.Icc (0 : ℝ) 1 :=
  ⟨grid i, by fin_cases i <;> norm_num [grid, Set.mem_Icc]⟩

/-- The same observations are admissible at the closed window's endpoints. -/
example : curve.window 0 1 ∈
    windowContinuousCandidates (show (0 : ℝ) ≤ 1 by norm_num) model recorded validTimes ⟨0, 1⟩ := by
  apply (mem_windowCurveCandidates_iff _ _ _ _ _ _ _).2
  exact ⟨trivial, windowGrid, rfl, sampleError_within⟩

/-- Forward slope uses the recorded columns directly after decoding. -/
example : Operations.forwardSlope? decoded.timestamps decoded.values 0 = some (2 : ℝ) := by
  change Operations.forwardSlope? ![(decodeTime 0 : ℝ), decodeTime 1]
    ![(decodeValue 2 : ℝ), decodeValue 4] 0 = some 2
  norm_num [Operations.forwardSlope?, Operations.forwardDiff, Operations.segmentLeft,
    Operations.segmentRight, decodeTime, decodeValue, smul_eq_mul]

end

end Silmaril.Data.TimeSeries.Examples
