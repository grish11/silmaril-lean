module

public import Silmaril.Data.TimeSeries.Kinematics.Defs

/-! The derivative contract in terms of the position and velocity projections. -/

@[expose] public section

namespace Silmaril.Data.TimeSeries.Series

variable {n : Nat} {Time E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem derivativeCompatible_iff (s : Series n Time (PosVel E E)) (f : ℝ → E)
    (sampleTimes : Fin n → ℝ) :
    s.DerivativeCompatible f sampleTimes ↔
      ∀ i, f (sampleTimes i) = (s.positions.get i).value ∧
        HasDerivAt f (s.velocities.get i).value (sampleTimes i) := Iff.rfl

end Silmaril.Data.TimeSeries.Series
