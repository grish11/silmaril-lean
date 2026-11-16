module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Reduction.Thms
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Rules.Thms
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Substitution

@[expose] public section

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.Reduction.Examples

/-- A typed endpoint with a proper directed beta contraction. -/
def endpoint : Term 0 := .app natIdentity .zero

theorem endpoint_step : ReductionStep endpoint .zero := .root (.beta .nat (.var 0) .zero)

def endpoint_derivation : Derivation .nil endpoint .nat :=
  .app natIdentity_derivation (.zero .nil)

/-- The repeated endpoint appears three times in the original J redex. -/
def before : Term 0 := .j .nat endpoint .nat .zero endpoint (.refl endpoint)

/-- Reducing just its right endpoint temporarily desynchronizes the copies. -/
def between : Term 0 := .j .nat endpoint .nat .zero .zero (.refl endpoint)

theorem before_root : RootReduction before .zero := .j_refl .nat endpoint .nat .zero

theorem before_step_between : ReductionStep before between := .j_right endpoint_step

theorem between_not_root : ¬ RootReduction between .zero := by
  intro h
  cases h

/-- Both branches of the actual J fork join by synchronizing the remaining copies. -/
theorem between_reduces_zero : Reduces between .zero :=
  Reduces.j_synchronize endpoint_step.toReduces (.refl .zero) endpoint_step.toReduces

noncomputable def before_derivation : Derivation .nil before .nat := by
  have hNat : Derivation .nil .nat (.univ 0) := .nat .nil
  have hΓ : ContextDerivation (Context.nil.snoc .nat) := .snoc .nil hNat
  have hEndpoint : Derivation (Context.nil.snoc .nat) endpoint.weaken .nat := by
    have h := endpoint_derivation.weaken (B := .nat) .nil hNat
    exact h
  have hId : Derivation (Context.nil.snoc .nat)
      (.id .nat endpoint.weaken (.var 0)) (.univ 0) :=
    .id (.nat hΓ) hEndpoint (.var hΓ .here)
  have hMotive : ContextDerivation (motiveContext .nil .nat endpoint) := .snoc hΓ hId
  exact .j hNat endpoint_derivation (.nat hMotive) (.zero .nil)
    endpoint_derivation (.refl hNat endpoint_derivation)

theorem before_conversion_chain :
    Relation.ReflTransGen (Relation.SymmGen ReductionStep) before .zero :=
  convertible_iff_reductionChain.mp before_root.toConvertible

end Silmaril.Logic.TypeTheory.IntensionalMLTT.Reduction.Examples
