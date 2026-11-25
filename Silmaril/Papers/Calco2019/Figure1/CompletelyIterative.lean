module

public import Silmaril.Semantics.Calco2019.CompletelyIterative.Thms

/-! # CALCO 2019, Figure 1, completely iterative monads -/

public section

universe u v

namespace Silmaril.Papers.Calco2019

open CategoryTheory Silmaril.Calco2019

/-- A completely iterative idealized monad has unique solutions for the
weak guard induced by its module. -/
theorem completelyIterative_to_guardedIterative {C : Type u} [Category.{v} C]
    (P : Coproducts C) {T : CategoryTheory.Monad C} (I : IdealizedMonad T)
    (h : I.CompletelyIterative P) : IsGuardedIterative P (I.weakGuard P) :=
  I.weakGuard_iterative P h

end Silmaril.Papers.Calco2019
