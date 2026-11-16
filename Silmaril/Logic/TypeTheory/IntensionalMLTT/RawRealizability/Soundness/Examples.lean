module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Soundness.Thms
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRecursorSubjectReduction.Examples

@[expose] public section

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Soundness.Examples

open RawRecursorSubjectReduction.Examples

/-- Actual closed code/member data from an unrestricted source conversion node. -/
theorem converted_nat_realizes :
    ∃ i X, Code i (ofTerm natAlias) X ∧ ofTerm natRecOne ∈ X := by
  have d : Derivation .nil natRecOne natAlias :=
    .conv natRecOne_derivation natAlias_derivation (.symm (.beta .unit .nat .star))
  exact closed_realizes d

/-- A source recursor ending in cumulativity has actual universe-code membership. -/
theorem cumulative_nat_realizes :
    ∃ i X, Code i (ofTerm (.univ 2)) X ∧
      ofTerm (.natrec (.univ 0) .nat typeStep .zero) ∈ X :=
  closed_realizes cumulativeSource

/-- Original exact based J remains sound under a converted requested carrier. -/
theorem converted_j_realizes : Valid .nil jZero natAlias :=
  converted_j_refl.1.realizes

/-- A motive genuinely depends on both the endpoint and its path variable. -/
def pathMotive : Term 2 := .id (.id .nat .zero (.var 1)) (.var 0) (.var 0)

def pathMotive_derivation :
    Derivation (motiveContext .nil .nat .zero) pathMotive (.univ 0) := by
  have hΓ : ContextDerivation (Context.nil.snoc .nat) := .snoc .nil (.nat .nil)
  have hPath : Derivation (Context.nil.snoc .nat) (.id .nat .zero (.var 0)) (.univ 0) :=
    .id (.nat hΓ) (.zero hΓ) (.var hΓ .here)
  have hΔ : ContextDerivation (motiveContext .nil .nat .zero) := .snoc hΓ hPath
  have hEndpoint : Derivation (motiveContext .nil .nat .zero) (.var 1) .nat :=
    .var hΔ (.there .here)
  have hCarrier : Derivation (motiveContext .nil .nat .zero)
      (.id .nat .zero (.var 1)) (.univ 0) :=
    .id (.nat hΔ) (.zero hΔ) hEndpoint
  have hp : Derivation (motiveContext .nil .nat .zero) (.var 0)
      (.id .nat .zero (.var 1)) := .var hΔ .here
  exact .id hCarrier hp hp

def pathJ : Term 0 :=
  .j .nat .zero pathMotive (.refl (.refl .zero)) .zero (.refl .zero)

def pathJ_derivation :
    Derivation .nil pathJ (pathMotive.instantiate₂ .zero (.refl .zero)) := by
  have hNat : Derivation .nil .nat (.univ 0) := .nat .nil
  have hZero : Derivation .nil .zero .nat := .zero .nil
  have hId : Derivation .nil (.id .nat .zero .zero) (.univ 0) := .id hNat hZero hZero
  have hRefl : Derivation .nil (.refl .zero) (.id .nat .zero .zero) := .refl hNat hZero
  have hBase : Derivation .nil (.refl (.refl .zero))
      (pathMotive.instantiate₂ .zero (.refl .zero)) := .refl hId hRefl
  exact .j hNat hZero pathMotive_derivation hBase hZero hRefl

/-- Full dependent J produces actual code/member data; the motive is not constant. -/
theorem path_j_realizes : ∃ i X,
    Code i (ofTerm (pathMotive.instantiate₂ .zero (.refl .zero))) X ∧ ofTerm pathJ ∈ X :=
  closed_realizes pathJ_derivation

/-- The original empty context is actually realized, so closed consistency is nonvacuous. -/
theorem empty_context_realized : RealizesContext .nil (variableEnv 0) := trivial

theorem no_original_empty : ¬ ∃ t : Term 0, Typing .nil t .empty := empty_consistency

end Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Soundness.Examples
