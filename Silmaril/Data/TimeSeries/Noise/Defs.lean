module

public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Sampling with additive noise

The sampling interface uses finite indexed vectors. A noise measure describes the entire
vector of errors, so errors at different indices may be dependent. For a random function,
the caller supplies a measurable family, a law on its parameters and a noise kernel.
Probability inputs, with a Markov kernel in the random model, give probability laws.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Silmaril.Data.TimeSeries.Noise

/-- A finite schedule indexed by sample position. Times may repeat. -/
abbrev Schedule (n : Nat) := Fin n → ℝ

/-- The values or errors at the positions of a schedule. -/
abbrev Samples (n : Nat) (V : Type*) := Fin n → V

variable {n : Nat} {V : Type*}

/-- Evaluate a fixed function at the scheduled times. -/
def sample (f : ℝ → V) (times : Schedule n) : Samples n V := fun i => f (times i)

/-- Subtract the clean samples from the observations coordinatewise. -/
def residual [Sub V] (clean observed : Samples n V) : Samples n V := observed - clean

/-- A parameterized family of functions with measurable evaluation in the parameter at each
fixed time. This suffices for any fixed finite schedule. -/
structure MeasurableFamily (F V : Type*) [MeasurableSpace F] [MeasurableSpace V] where
  eval : F → ℝ → V
  measurable_eval : ∀ t, Measurable (fun a => eval a t)

variable [MeasurableSpace V]

/-- The pushforward of the supplied joint noise measure through translation by the clean
samples. Since `f` and `times` are fixed, measurability of `f` is unnecessary. -/
noncomputable def fixedObservationLaw [Add V] [MeasurableAdd₂ V] (f : ℝ → V) (times : Schedule n)
    (noise : Measure (Samples n V)) : Measure (Samples n V) :=
  noise.map (fun ε => sample f times + ε)

variable {F : Type*} [MeasurableSpace F]

theorem MeasurableFamily.measurable_sample (family : MeasurableFamily F V) (times : Schedule n) :
    Measurable (fun a => sample (family.eval a) times) :=
  Measurable.of_eval fun i => family.measurable_eval (times i)

/-- The joint law of the family parameter and its conditional noise vector. -/
noncomputable def jointNoiseLaw (prior : Measure F) (noise : Kernel F (Samples n V)) :
    Measure (F × Samples n V) :=
  prior ⊗ₘ noise

/-- The unconditional noise law, obtained by mixing the kernel against the prior. -/
noncomputable def noiseLaw (prior : Measure F) (noise : Kernel F (Samples n V)) :
    Measure (Samples n V) :=
  noise ∘ₘ prior

/-- Evaluate the function selected by the parameter and add its noise vector. -/
def observe [Add V] (family : MeasurableFamily F V) (times : Schedule n)
    (draw : F × Samples n V) : Samples n V :=
  sample (family.eval draw.1) times + draw.2

theorem measurable_observe [Add V] [MeasurableAdd₂ V]
    (family : MeasurableFamily F V) (times : Schedule n) : Measurable (observe family times) :=
  ((family.measurable_sample times).comp measurable_fst).add measurable_snd

/-- Push the joint law forward to the observation vector, retaining the dependence of the
noise on the chosen function parameter. -/
noncomputable def randomObservationLaw [Add V] [MeasurableAdd₂ V] (family : MeasurableFamily F V)
    (times : Schedule n) (prior : Measure F) (noise : Kernel F (Samples n V)) :
    Measure (Samples n V) :=
  (jointNoiseLaw prior noise).map (observe family times)

end Silmaril.Data.TimeSeries.Noise
