module

public import Silmaril.Logic.Temporal.TLA.Elaborator.Defs

public section

namespace Silmaril.Logic.Temporal.TLA.Elaborator

/-- Selecting a checked state predicate as a step uses exactly its source lift. -/
theorem CheckedModule.stepPredicate_of_statePredicate {signature : Signature}
    (checked : CheckedModule signature) (name : Surface.Ident) (p : Kernel.StatePredicate signature.scope)
    (h : checked.statePredicate name = .ok p) : checked.stepPredicate name = .ok p.current := by
  simp only [CheckedModule.statePredicate, CheckedModule.stepPredicate] at h ⊢
  generalize checked.predicate name = result at h ⊢
  rcases result with _ | (_ | _) <;> cases h <;> rfl

end Silmaril.Logic.Temporal.TLA.Elaborator
