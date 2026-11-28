module

public import Silmaril.Data.TimeSeries.Quantization.Series.Defs
public import Silmaril.Data.TimeSeries.Thms
import Silmaril.Data.TimeSeries.Quantization.Thms

public section

namespace Silmaril.Proofs.Data.TimeSeries.Quantization

open Silmaril.Data.TimeSeries Silmaril.Data.TimeSeries.Quantization
open scoped NNReal

variable {n : Nat} {Time Value Ideal : Type*}

theorem mem_candidates_of_recorded_error [PseudoMetricSpace Ideal]
    (s : Series n Time Value) (decodeTime : Time → ℝ) (decodeValue : Value → Ideal)
    {f : ℝ → Ideal} {K : ℝ≥0} (hf : LipschitzWith K f)
    (times : Fin n → ℝ) {validTimes : (Fin n → ℝ) → Prop} (hvalid : validTimes times)
    {eligible : Series n Time Value → (ℝ → Ideal) → Prop} (heligible : eligible s f)
    (budget : Error)
    (ht : ∀ i, nndist (decodeTime (s.timestamps i)) (times i) ≤ budget.time)
    (hv : ∀ i, nndist (decodeValue (s.values i)) (f (decodeTime (s.timestamps i))) ≤ budget.value) :
    f ∈ candidates (ErrorModel.ofDecode decodeTime decodeValue) s validTimes
      ⟨budget.time, budget.value + K * budget.time⟩ eligible := by
  refine ⟨heligible, times, hvalid, (ErrorModel.seriesError_within_iff _ _ _ _ _).2 ?_⟩
  intro i
  change nndist (times i) (decodeTime (s.timestamps i)) ≤ budget.time ∧
    nndist (f (times i)) (decodeValue (s.values i)) ≤ budget.value + K * budget.time
  refine ⟨by rw [nndist_comm]; exact ht i, ?_⟩
  rw [nndist_comm]
  exact Silmaril.Data.TimeSeries.Quantization.sample_error hf times (fun j => decodeTime (s.timestamps j))
    (fun j => decodeValue (s.values j)) (fun j => ht j) (fun j => hv j) i

theorem uniformSeries_mem_candidates (timeGrid valueGrid : Uniform)
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (times : Fin n → ℝ) {validTimes : (Fin n → ℝ) → Prop} (hvalid : validTimes times)
    {eligible : Series n Int Int → (ℝ → ℝ) → Prop}
    (heligible : eligible (uniformSeries timeGrid valueGrid f times) f) :
    f ∈ candidates (ErrorModel.ofDecode timeGrid.decode valueGrid.decode)
      (uniformSeries timeGrid valueGrid f times) validTimes
      ⟨timeGrid.halfStep, valueGrid.halfStep + K * timeGrid.halfStep⟩ eligible := by
  refine mem_candidates_of_recorded_error _ _ _ hf times hvalid heligible
    ⟨timeGrid.halfStep, valueGrid.halfStep⟩ ?_ ?_
  · intro i
    change dist (timeGrid.quantize (times i)) (times i) ≤ timeGrid.step / 2
    simpa only [Real.dist_eq] using timeGrid.quantize_error (times i)
  · intro i
    change dist (valueGrid.quantize (f (timeGrid.quantize (times i))))
      (f (timeGrid.quantize (times i))) ≤ valueGrid.step / 2
    simpa only [Real.dist_eq] using valueGrid.quantize_error (f (timeGrid.quantize (times i)))

end Silmaril.Proofs.Data.TimeSeries.Quantization
