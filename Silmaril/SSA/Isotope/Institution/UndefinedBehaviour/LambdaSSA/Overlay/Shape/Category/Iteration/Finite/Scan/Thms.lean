module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Search

/-! # The productive orbit of an exhausted finite scan -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration

variable {points results states : Nat}

/-- If the full scan finds no terminal, every step of a continued orbit
is an actual transfer. The finite-carrier proof finds a repeated point. -/
theorem scan_exhausted_path (rows : Fin points → Row points results states) (p : Fin points)
    (noneFound : search rows points p = none) :
    ∃ orbit : Nat → Fin points, orbit 0 = p ∧ ∀ k, rows (orbit k) = .repeat (orbit (k + 1)) :=
  ⟨Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.orbit rows p, Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.orbit_zero rows p,
    Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.repeats_of_exhausted rows p noneFound⟩

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
