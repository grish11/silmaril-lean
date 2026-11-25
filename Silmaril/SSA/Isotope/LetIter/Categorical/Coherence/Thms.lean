module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Coherence.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Coherence

/-! # Derivation dependence in an exact LetIter model -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

/-- The refined Freyd boundary and pure primitive condition allow a model in which
two derivations of one exact typing judgment have distinct denotations. -/
theorem refinedEquationSound_fails : ¬ RefinedEquationSound :=
  TypingCounterexample.refinedEquationSound_fails_proof

end Silmaril.Isotope.LetIter.Semantics.Categorical
