module

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Silmaril.Data.TimeSeries.Noise.Thms

/-! # Two sample times with a shared error -/

open MeasureTheory ProbabilityTheory Silmaril.Data.TimeSeries.Noise

namespace Silmaril.Data.TimeSeries.Noise.Examples

private noncomputable def shiftedTime : MeasurableFamily ℝ ℝ where
  eval offset time := time + offset
  measurable_eval _ := measurable_const.add measurable_id

private def sharedError (offset : ℝ) : Samples 2 ℝ := fun _ => offset

private theorem measurable_sharedError : Measurable sharedError :=
  Measurable.of_eval fun _ => measurable_id

private noncomputable def sharedErrorKernel : Kernel ℝ (Samples 2 ℝ) :=
  Kernel.deterministic sharedError measurable_sharedError

/-- One random offset selects the function `t ↦ t + offset` and also supplies the error at
both times. The observations at times 0 and 1 use the same draw for both additions. -/
example (prior : Measure ℝ) [IsProbabilityMeasure prior] :
    noiseLaw prior sharedErrorKernel = prior.map sharedError ∧
    randomObservationLaw shiftedTime (fun i => (i.val : ℝ)) prior sharedErrorKernel =
      prior.map (fun offset (i : Fin 2) => (i.val : ℝ) + offset + offset) := by
  refine ⟨Measure.deterministic_comp_eq_map measurable_sharedError, ?_⟩
  have hdraw : Measurable (fun offset => (offset, sharedError offset)) :=
    measurable_id.prodMk measurable_sharedError
  rw [randomObservationLaw, jointNoiseLaw, sharedErrorKernel,
    Measure.compProd_deterministic measurable_sharedError,
    Measure.map_map (measurable_observe _ _) hdraw]
  rfl

end Silmaril.Data.TimeSeries.Noise.Examples
