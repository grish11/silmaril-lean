module

public import Silmaril.Data.TimeSeries.Quantization.Series.Defs
public import Silmaril.Data.TimeSeries.Quantization.Thms
public import Silmaril.Data.TimeSeries.Thms
import Silmaril.Proofs.Data.TimeSeries.Quantization.Series

/-! Apply the quantization bounds to the shared time-series candidate test. -/

public section

namespace Silmaril.Data.TimeSeries.Quantization

open scoped NNReal

variable {n : Nat} {Time Value Ideal : Type*}

/-- Decoding the stored values recovers the existing uniform-quantization samples. -/
theorem uniformSeries_decoded_values (timeGrid valueGrid : Uniform) (f : ℝ → ℝ)
    (times : Fin n → ℝ) :
    ((uniformSeries timeGrid valueGrid f times).mapValue valueGrid.decode).values =
      uniformSamples timeGrid valueGrid f times := rfl

/-- Turn a value bound at the decoded recorded times into a candidate with a
value budget at the given valid latent times. The time budget is unchanged. -/
theorem mem_candidates_of_recorded_error [PseudoMetricSpace Ideal]
    (s : Series n Time Value) (decodeTime : Time → ℝ) (decodeValue : Value → Ideal)
    {f : ℝ → Ideal} {K : ℝ≥0} (hf : LipschitzWith K f)
    (times : Fin n → ℝ) {validTimes : (Fin n → ℝ) → Prop} (hvalid : validTimes times)
    {eligible : Series n Time Value → (ℝ → Ideal) → Prop} (heligible : eligible s f)
    (budget : Error)
    (ht : ∀ i, nndist (decodeTime (s.timestamps i)) (times i) ≤ budget.time)
    (hv : ∀ i, nndist (decodeValue (s.values i)) (f (decodeTime (s.timestamps i))) ≤ budget.value) :
    f ∈ candidates (ErrorModel.ofDecode decodeTime decodeValue) s validTimes
      ⟨budget.time, budget.value + K * budget.time⟩ eligible :=
  Proofs.Data.TimeSeries.Quantization.mem_candidates_of_recorded_error
    s decodeTime decodeValue hf times hvalid heligible budget ht hv

/-- The original schedule witnesses candidate membership for a uniformly quantized series.
Its time budget is half a time step, and its latent-time value budget includes both axes. -/
theorem uniformSeries_mem_candidates (timeGrid valueGrid : Uniform)
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (times : Fin n → ℝ) {validTimes : (Fin n → ℝ) → Prop} (hvalid : validTimes times)
    {eligible : Series n Int Int → (ℝ → ℝ) → Prop}
    (heligible : eligible (uniformSeries timeGrid valueGrid f times) f) :
    f ∈ candidates (ErrorModel.ofDecode timeGrid.decode valueGrid.decode)
      (uniformSeries timeGrid valueGrid f times) validTimes
      ⟨timeGrid.halfStep, valueGrid.halfStep + K * timeGrid.halfStep⟩ eligible :=
  Proofs.Data.TimeSeries.Quantization.uniformSeries_mem_candidates
    timeGrid valueGrid hf times hvalid heligible

end Silmaril.Data.TimeSeries.Quantization
