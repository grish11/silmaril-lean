module

public import Silmaril.Logic.TypeTheory.CIC.Declarations.Lookup.Defs
public import Silmaril.Proofs.Logic.TypeTheory.CIC.CheckedLookup

@[expose] public section

/-! # Inversion of actual lookup in a checked source environment

The public witnesses retain the exact preceding environment, its universe
checks, actual constructor-sort lists, source positivity and projection cache.
Projection typing still checks the raw reference's parameter count explicitly.
These are general checked-source prerequisites, without semantic assignments
or a claimed CIC soundness theorem.
-/

namespace Silmaril.Logic.TypeTheory.CIC.CoreCheckedEnvironment

export Silmaril.Proofs.Logic.TypeTheory.CIC.CheckedLookupLaws
  (declaration_checked inductive_checked constructor_checked projection_checked projection_field_typed)

end Silmaril.Logic.TypeTheory.CIC.CoreCheckedEnvironment
