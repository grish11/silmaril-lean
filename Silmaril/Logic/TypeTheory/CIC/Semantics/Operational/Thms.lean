module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Operational.Defs
public import Silmaril.Proofs.Logic.TypeTheory.CIC.OperationalEvaluation

@[expose] public section

/-! # Deterministic staged unary-fix and tagged-iota evaluation

Actual constructor-directed unary fix/beta and no-definition tagged iota
rules extend existing kernel values. The extension is deterministic and agrees
with every old kernel evaluation. Each staged derivation constructs an actual
finite source reduction to a same-valued kernel expression. No arbitrary
reduction closure, fixed trace assignment or general typing soundness is assumed.
The original kernel and its transport theorems remain unchanged. Universe
transport and local insertion are supplied by separate Operational.Instantiation
and Operational.Local headers; local substitution uses kernel-evaluated
replacements. Operational.Carrier supplies concrete liftSet transport.
Operational.Bounded supplies original-source finite support and actual tower
restriction, extension and raising laws.
-/

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

export Silmaril.Proofs.Logic.TypeTheory.CIC.OperationalEvaluationLaws
  (constructor_spine_injective iota_reduct_eq evaluates_fix_impossible evaluates_fix_application_impossible fixBeta_steps evaluates_expandLets_noDefinitions
   evaluates_iota_reduct operationalEvaluates_fix_impossible operationalEvaluates_kernel_compatible
   operationalEvaluates_deterministic operational_iota_step operationalEvaluates_source_bridge)

end Silmaril.Logic.TypeTheory.CIC.SetSemantics
