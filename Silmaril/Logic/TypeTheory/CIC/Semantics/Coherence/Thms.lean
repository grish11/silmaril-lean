module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Thms
public import Silmaril.Proofs.Logic.TypeTheory.CIC.SemanticCoherence

@[expose] public section

/-! # Coherence for the concrete CIC evaluation kernel

Evaluation is deterministic. Actual de Bruijn lifting and simultaneous
substitution preserve exact values, yielding dependent application and
same-value beta/zeta endpoints. Beta requires the argument to belong to the
lambda's semantic domain. These laws cover the defined evaluation kernel;
full CIC conversion, general inductive/case/projection soundness and
fix/cofix semantics remain open.
-/

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

export Silmaril.Proofs.Logic.TypeTheory.CIC.SemanticCoherenceLaws
  (evaluates_deterministic missing_constant_rejected evaluates_lift evaluates_subst evaluates_subst_one
   application_substitution_rule beta_step_values zeta_step_values)

end Silmaril.Logic.TypeTheory.CIC.SetSemantics
