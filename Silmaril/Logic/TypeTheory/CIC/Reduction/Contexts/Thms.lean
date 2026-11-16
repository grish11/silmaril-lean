module

public import Silmaril.Logic.TypeTheory.CIC.Reduction.Thms
public import Silmaril.Proofs.Logic.TypeTheory.CIC.ContextReduction

@[expose] public section

/-! # Concrete reduction caches without local definitions

Assumption-only caches have length-many assumptions and a pure rel-variable
extended substitution. Declaration-instance substitution preserves this
property; equal-length caches therefore give the same actual let expansion.
-/

namespace Silmaril.Logic.TypeTheory.CIC.Context

export Silmaril.Proofs.Logic.TypeTheory.CIC.ContextReductionLaws
  (assumptionCount_eq_length instantiateCase_noDefinitions extendedSubst_eq_of_noDefinitions
   extendedSubst_substUniverses expandLets_eq_of_noDefinitions)

end Silmaril.Logic.TypeTheory.CIC.Context
