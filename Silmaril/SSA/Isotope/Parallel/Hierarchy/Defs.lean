module

public import Silmaril.SSA.Isotope.LetPar.Interpretation.Defs

@[expose] public section

namespace Silmaril.Isotope.Parallel.Hierarchy

universe u v

/-- Restrict a parallel iteration model to its case and empty operations. -/
def restrictControl {τ : Type u} [TypeFormers τ] {D : τ → Type v} {m : Type v → Type v}
    (C : Control .iter D m) : Control .case D m where
  sum h := C.sum (Tier.caseIter.hasCase h)
  zero h := C.zero (Tier.caseIter.hasCase h)
  loop h := nomatch h

end Silmaril.Isotope.Parallel.Hierarchy
