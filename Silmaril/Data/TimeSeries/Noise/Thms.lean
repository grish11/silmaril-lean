module

public import Silmaril.Data.TimeSeries.Noise.Defs
import Silmaril.Proofs.Data.TimeSeries.Noise.Laws

/-! # Laws of sampling with additive noise -/

public section

open MeasureTheory ProbabilityTheory

namespace Silmaril.Data.TimeSeries.Noise

variable {n : Nat} {F V : Type*} [MeasurableSpace F] [MeasurableSpace V]

instance [Add V] [MeasurableAdd₂ V] (f : ℝ → V) (times : Schedule n)
    (noise : Measure (Samples n V)) [IsProbabilityMeasure noise] :
    IsProbabilityMeasure (fixedObservationLaw f times noise) := by
  unfold fixedObservationLaw
  infer_instance

instance (prior : Measure F) [IsProbabilityMeasure prior]
    (noise : Kernel F (Samples n V)) [IsMarkovKernel noise] :
    IsProbabilityMeasure (jointNoiseLaw prior noise) := by
  unfold jointNoiseLaw
  infer_instance

instance (prior : Measure F) [IsProbabilityMeasure prior]
    (noise : Kernel F (Samples n V)) [IsMarkovKernel noise] :
    IsProbabilityMeasure (noiseLaw prior noise) := by
  unfold noiseLaw
  infer_instance

instance [Add V] [MeasurableAdd₂ V] (family : MeasurableFamily F V) (times : Schedule n)
    (prior : Measure F) [IsProbabilityMeasure prior]
    (noise : Kernel F (Samples n V)) [IsMarkovKernel noise] :
    IsProbabilityMeasure (randomObservationLaw family times prior noise) := by
  unfold randomObservationLaw
  infer_instance

/-- For s-finite inputs, the mixed noise law is the second marginal of the joint law. -/
theorem jointNoiseLaw_snd (prior : Measure F) [SFinite prior]
    (noise : Kernel F (Samples n V)) [IsSFiniteKernel noise] :
    (jointNoiseLaw prior noise).snd = noiseLaw prior noise :=
  Measure.snd_compProd prior noise

/-- Zero noise concentrates the observation law on the clean sample vector. -/
theorem fixedObservationLaw_zero_noise [AddZeroClass V] [MeasurableAdd₂ V]
    (f : ℝ → V) (times : Schedule n) :
    fixedObservationLaw f times (Measure.dirac 0) = Measure.dirac (sample f times) := by
  have hadd : Measurable (fun ε : Samples n V => sample f times + ε) :=
    measurable_const.add measurable_id
  rw [fixedObservationLaw, Measure.map_dirac' hadd, add_zero]

/-- Subtracting a known function's samples recovers the entire joint noise law. -/
theorem fixedObservationLaw_residual [AddCommGroup V] [MeasurableAdd₂ V] [MeasurableSub₂ V]
    (f : ℝ → V) (times : Schedule n) (noise : Measure (Samples n V)) :
    (fixedObservationLaw f times noise).map (residual (sample f times)) = noise :=
  Proofs.Data.TimeSeries.Noise.fixedObservationLaw_residual f times noise

/-- A point mass on a parameter reduces the random model to the corresponding fixed function
with the kernel's noise law at that parameter. -/
theorem randomObservationLaw_dirac [Add V] [MeasurableAdd₂ V] [MeasurableSingletonClass F]
    (family : MeasurableFamily F V) (times : Schedule n) (a : F)
    (noise : Kernel F (Samples n V)) [IsMarkovKernel noise] :
    randomObservationLaw family times (Measure.dirac a) noise =
      fixedObservationLaw (family.eval a) times (noise a) :=
  Proofs.Data.TimeSeries.Noise.randomObservationLaw_dirac family times a noise

end Silmaril.Data.TimeSeries.Noise
