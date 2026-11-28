module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Example.Defs

/-! # A cyclic source with a different request placement on each tag -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet.CaseExpansion

open CategoryTheory CategoryTheory.Limits
open EntryLetObstruction
open OperandExample (D X taggedSource)
open Paper.TypeCategory (ofRegion sumCofan sumIso)

/-- Each state executes a request and recurs with its own tag. The
request has moved out of the two-transfer CFG only in the first arm. -/
noncomputable def source : D ⟶ X ⨿ D :=
  (sumIso U U).hom ≫ coprod.desc
    ((sumCofan U U).inl ≫ taggedSource (ofRegion movedRequest_typed))
    ((sumCofan U U).inr ≫ taggedSource (ofRegion flatRequest_typed))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet.CaseExpansion
