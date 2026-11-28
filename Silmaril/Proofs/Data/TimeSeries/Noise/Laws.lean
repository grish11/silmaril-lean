module

public import Silmaril.Data.TimeSeries.Noise.Defs

public section

open MeasureTheory ProbabilityTheory Silmaril.Data.TimeSeries.Noise

namespace Silmaril.Proofs.Data.TimeSeries.Noise

variable {n : Nat} {F V : Type*} [MeasurableSpace F] [MeasurableSpace V]

theorem fixedObservationLaw_residual [AddCommGroup V] [MeasurableAdd₂ V] [MeasurableSub₂ V]
    (f : ℝ → V) (times : Schedule n) (noise : Measure (Samples n V)) :
    (fixedObservationLaw f times noise).map (residual (sample f times)) = noise := by
  have hresidual : Measurable (residual (sample f times)) :=
    measurable_id.sub measurable_const
  have hadd : Measurable (fun ε : Samples n V => sample f times + ε) :=
    measurable_const.add measurable_id
  rw [fixedObservationLaw, Measure.map_map hresidual hadd]
  have hinverse : residual (sample f times) ∘ (fun ε => sample f times + ε) = id := by
    funext ε
    change sample f times + ε - sample f times = ε
    simp [add_comm (sample f times) ε]
  rw [hinverse, Measure.map_id]

theorem randomObservationLaw_dirac [Add V] [MeasurableAdd₂ V] [MeasurableSingletonClass F]
    (family : MeasurableFamily F V) (times : Schedule n) (a : F)
    (noise : Kernel F (Samples n V)) [IsMarkovKernel noise] :
    randomObservationLaw family times (Measure.dirac a) noise =
      fixedObservationLaw (family.eval a) times (noise a) := by
  have hobserve := measurable_observe family times
  have hfixed : Measurable (fun ε : Samples n V => sample (family.eval a) times + ε) :=
    measurable_const.add measurable_id
  ext s hs
  rw [randomObservationLaw, fixedObservationLaw, Measure.map_apply hobserve hs,
    jointNoiseLaw, Measure.dirac_compProd_apply (hobserve hs), Measure.map_apply hfixed hs]
  rfl

end Silmaril.Proofs.Data.TimeSeries.Noise
