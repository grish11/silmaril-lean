module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Obstruction.Thms

/-! # Once-bound η derives the separated two-transfer entry let -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta

open EntryLetObstruction

/-- The exact two-transfer fixture is derivable with the once-bound η seed. -/
theorem flatRequest_eq_moved : Eqv [U] flatRequest movedRequest [U] :=
  entryLet (n := 2) (fun _ => U) (.op (.var rfl)) (.br rfl (.var rfl))
    (Fin.cases (.br rfl (.var rfl)) (fun _ => .br rfl (.var rfl)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta
