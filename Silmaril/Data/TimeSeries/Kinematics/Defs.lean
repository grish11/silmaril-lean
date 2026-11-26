module

public import Silmaril.Data.TimeSeries.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Position and velocity columns, with a derivative contract for real normed
vector spaces. In this specialization velocities are vectors in the model space. -/

@[expose] public section

namespace Silmaril.Data.TimeSeries

/-- Position and velocity may have different recorded types. -/
structure PosVel (Position Velocity : Type*) where
  pos : Position
  vel : Velocity

namespace Series

variable {n : Nat} {Time Position Velocity : Type*}

def positions (s : Series n Time (PosVel Position Velocity)) : Series n Time Position :=
  s.mapValue PosVel.pos

def velocities (s : Series n Time (PosVel Position Velocity)) : Series n Time Velocity :=
  s.mapValue PosVel.vel

end Series

variable {n : Nat} {Time E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The position and velocity agree with the curve and its derivative at the supplied time. -/
def PosVel.CompatibleAt (sample : PosVel E E) (f : ℝ → E) (t : ℝ) : Prop :=
  f t = sample.pos ∧ HasDerivAt f sample.vel t

/-- Check the columns at explicitly supplied latent times. Use an error model
and a schedule predicate when relating those times to the recorded timestamps. -/
def Series.DerivativeCompatible (s : Series n Time (PosVel E E)) (f : ℝ → E)
    (sampleTimes : Fin n → ℝ) : Prop :=
  ∀ i, (s.get i).value.CompatibleAt f (sampleTimes i)

end Silmaril.Data.TimeSeries
