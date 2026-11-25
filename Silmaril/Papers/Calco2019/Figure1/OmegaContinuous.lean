module

public import Silmaril.Semantics.Calco2019.OmegaContinuous.Thms

/-! # CALCO 2019, Figure 1, ω-continuous monads

The lower left edge uses least fixpoints, as in Theorem 5.8 of *Unguarded
Recursion on Coinductive Resumptions*. The target here is CALCO Definition 19.
-/

public section

universe u v

namespace Silmaril.Papers.Calco2019

open CategoryTheory Silmaril.Calco2019
open OmegaCompletePartialOrder

/-- An ω-continuous monad becomes Elgot by selecting the total guard and using
least fixpoints to satisfy the guarded Elgot laws. -/
theorem omegaContinuous_to_elgot {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {P : Coproducts C} {T : Monad C} [T.Strong]
    [∀ X Y : Kleisli T, OmegaCompletePartialOrder (X ⟶ Y)]
    [∀ X Y : Kleisli T, OrderBot (X ⟶ Y)] (E : OmegaContinuousMonad P T) :
    E.toElgot.IsElgot :=
  fun _ => trivial

end Silmaril.Papers.Calco2019
