module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Defs

/-! # Factorization through a shared feedback state -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits

/-- Ordinary iteration can rotate a transition that returns only a state. -/
@[expose] def IterationRolling (C : Type u) [Category.{v} C]
    [HasFiniteCoproducts C] [Iteration C] : Prop :=
  ∀ {X Y Z : C} (h : X ⟶ Z) (step : Z ⟶ Y ⨿ X),
    iterate (h ≫ step) = h ≫ iterate (step ≫ coprod.map (𝟙 Y) h)

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
