module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Coherence.Thms
public import Silmaril.Proofs.Logic.TypeTheory.CIC.TermSubstitutionReflection

@[expose] public section

/-! # Exact evaluation reflection through actual term substitution

Replacement expressions evaluate in the surviving suffix. CIC's actual
substitution lifts them under the explicit prefix, so no freshness or
closedness premise is added. Binder and case-field prefixes are retained.
-/

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

export Silmaril.Proofs.Logic.TypeTheory.CIC.TermSubstitutionReflectionLaws
  (evaluates_subst_reflect evaluates_subst_iff evaluates_subst_one_reflect evaluates_let_of_subst
    substitution_reflection_value_mismatch zeta_reconstruction_needs_value)

end Silmaril.Logic.TypeTheory.CIC.SetSemantics
