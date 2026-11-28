module

public import Silmaril.Data.TimeSeries.Noise.Thms
public import Silmaril.Data.TimeSeries.Sampling.Thms

/-! Relate the vector-valued Noise API to sampling and adding noise in a series. -/

public section

open MeasureTheory

namespace Silmaril.Data.TimeSeries.Noise

variable {n : Nat} {F Value : Type*}

/-- The value column of an exact series is the sample vector used by the noise model. -/
theorem sample_eq_series_values (f : ℝ → Value) (times : Schedule n) :
    sample f times = (Series.sample times f).values := rfl

/-- A fixed observation law pushes the joint noise vector through value-column extraction
from the perturbed series. -/
theorem fixedObservationLaw_eq_map_series_values [MeasurableSpace Value] [Add Value]
    [MeasurableAdd₂ Value] (f : ℝ → Value) (times : Schedule n)
    (noise : Measure (Samples n Value)) :
    fixedObservationLaw f times noise =
      noise.map (fun ε => ((Series.sample times f).addNoise ε).values) := rfl

/-- The random observation map uses the same extraction after sampling the selected function. -/
theorem observe_eq_series_values [MeasurableSpace F] [MeasurableSpace Value] [Add Value]
    (family : MeasurableFamily F Value) (times : Schedule n) (draw : F × Samples n Value) :
    observe family times draw = ((Series.sample times (family.eval draw.1)).addNoise draw.2).values :=
  rfl

end Silmaril.Data.TimeSeries.Noise
