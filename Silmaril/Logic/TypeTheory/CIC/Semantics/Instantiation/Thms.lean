module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Instantiation.Defs
public import Silmaril.Logic.TypeTheory.CIC.Semantics.Local.Thms
public import Silmaril.Proofs.Logic.TypeTheory.CIC.UniverseEvaluation

@[expose] public section

/-! # Concrete evaluation coherence for universe substitution and instantiation

Actual CIC universe substitution preserves values under composition of the
numerical valuation and explicit reindexing of global assignments. The same
values realize substituted local types/bodies and inhabited term/type pairs.
Declaration-instance specialization uses the actual `Expr.instantiate` and
`Context.instantiate` operations. These are raw substitution laws; valid
instance length, scope and constraints remain separate typing obligations.
-/

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

export Silmaril.Proofs.Logic.TypeTheory.CIC.UniverseEvaluationLaws
  (sortValue_substUniverses evaluates_substUniverses hasValueAt_substUniverses interpretsLocal_substUniverses
   evaluates_instantiate hasValueAt_instantiate interpretsLocal_instantiate instantiated_parameter_sort)

end Silmaril.Logic.TypeTheory.CIC.SetSemantics
