module

public import Silmaril.Data.TimeSeries.Quantization.Defs
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Lipschitz
import Silmaril.Proofs.Data.TimeSeries.Quantization.Uniform

/-! # Quantization error at the positions of a finite schedule -/

public section

namespace Silmaril.Data.TimeSeries.Quantization

/-- Every midpoint belongs to the upper grid cell, including at negative times. -/
theorem Uniform.encode_midpoint (grid : Uniform) (k : ℤ) :
    grid.encode (((k : ℝ) + 1 / 2) * grid.step) = k + 1 :=
  Proofs.Data.TimeSeries.Quantization.encode_midpoint grid k

theorem Uniform.quantize_midpoint (grid : Uniform) (k : ℤ) :
    grid.quantize (((k : ℝ) + 1 / 2) * grid.step) = ((k + 1 : ℤ) : ℝ) * grid.step := by
  rw [Uniform.quantize, grid.encode_midpoint, Uniform.decode]

/-- Half a step bounds the absolute error at every real input. -/
theorem Uniform.quantize_error (grid : Uniform) (x : ℝ) :
    |grid.quantize x - x| ≤ grid.step / 2 :=
  Proofs.Data.TimeSeries.Quantization.quantize_error grid x

/-- Bound the error against the original schedule from timestamp error and from
value error measured at the stored times. The observations can be decoded
values from any quantizer, and the signal can take values in a metric space. -/
theorem sample_error {n : Nat} {V : Type*} [PseudoMetricSpace V]
    {L : NNReal} {f : ℝ → V} (hf : LipschitzWith L f)
    (times storedTimes : Fin n → ℝ) (observed : Fin n → V) {timeError valueError : ℝ}
    (ht : ∀ i, dist (storedTimes i) (times i) ≤ timeError)
    (hv : ∀ i, dist (observed i) (f (storedTimes i)) ≤ valueError) (i : Fin n) :
    dist (observed i) (f (times i)) ≤ valueError + (L : ℝ) * timeError :=
  (dist_triangle _ (f (storedTimes i)) _).trans
    (add_le_add (hv i) (hf.dist_le_mul_of_le (ht i)))

/-- Uniform quantization of both timestamps and values gives a pointwise
bound against the original signal samples. -/
theorem uniformSamples_error {n : Nat} {L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (timeGrid valueGrid : Uniform) (times : Fin n → ℝ) (i : Fin n) :
    |uniformSamples timeGrid valueGrid f times i - f (times i)| ≤
      valueGrid.step / 2 + (L : ℝ) * (timeGrid.step / 2) := by
  rw [← Real.dist_eq]
  exact sample_error hf times (fun j => timeGrid.quantize (times j)) _
    (fun j => by rw [Real.dist_eq]; exact timeGrid.quantize_error (times j))
    (fun j => by rw [Real.dist_eq]; exact valueGrid.quantize_error (f (timeGrid.quantize (times j)))) i

end Silmaril.Data.TimeSeries.Quantization
