module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Obstruction.Thms

/-! # The two-transfer entry-let equation in the opt-in quotient -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet

open EntryLetObstruction

/-- The typed witness that separates standard Paper is an instance of
the new entry-let schema. -/
theorem flatRequest_eq_moved : Eqv [U] flatRequest movedRequest [U] :=
  entryLet 2 (fun _ => U) (.op (.var rfl)) (.br rfl (.var rfl))
    (Fin.cases (.br rfl (.var rfl)) (fun _ => .br rfl (.var rfl)))

/-- The opt-in singleton quotient identifies the exact separated pair. -/
theorem flatRequest_arrow_eq_moved :
    Extension.Singleton.ofRegion Step flatRequest_typed = Extension.Singleton.ofRegion Step movedRequest_typed :=
  (Extension.Singleton.ofRegion_eq_iff Step _ _).2 flatRequest_eq_moved

/-- The same representatives record the strict extension of the standard
singleton quotient. -/
theorem flatRequest_strict_extension :
    Paper.TypeCategory.ofRegion flatRequest_typed ≠ Paper.TypeCategory.ofRegion movedRequest_typed ∧
    Extension.Singleton.ofRegion Step flatRequest_typed = Extension.Singleton.ofRegion Step movedRequest_typed :=
  ⟨flatRequest_arrow_ne_moved, flatRequest_arrow_eq_moved⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet
