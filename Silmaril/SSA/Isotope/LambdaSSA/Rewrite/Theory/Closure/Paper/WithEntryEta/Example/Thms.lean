module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryEta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Obstruction.Thms

/-! # Replay of the two-transfer example by literal CFG η -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryEta

open EntryLetObstruction

/-- The exact two-transfer fixture follows from two applications of η. -/
theorem flatRequest_eq_moved : Eqv [U] flatRequest movedRequest [U] :=
  entryLet 2 (fun _ => U) (.op (.var rfl)) (.br rfl (.var rfl))
    (Fin.cases (.br rfl (.var rfl)) (fun _ => .br rfl (.var rfl)))

/-- The separation in standard Paper and derivability in the η slice
hold for the same typed regions. -/
theorem flatRequest_strict_extension :
    (¬ Paper.Eqv [U] flatRequest movedRequest [U]) ∧ Eqv [U] flatRequest movedRequest [U] :=
  ⟨flatRequest_ne_moved, flatRequest_eq_moved⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryEta
