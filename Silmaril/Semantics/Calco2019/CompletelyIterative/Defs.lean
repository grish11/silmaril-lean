module

public import Silmaril.Semantics.Calco2019.Defs

/-! # Completely iterative monads and the weak guard

Goncharov, Schröder, Rauch and Piróg, *Guarded and Unguarded Iteration for
Generalized Processes*, Definitions 3.13 and 3.15–3.16, arXiv:1712.09574.
-/

@[expose] public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory

/-- A monad module is a functor out of the Kleisli category. Naturality of its
comparison to the right Kleisli adjoint is the module-to-monad law. -/
structure IdealizedMonad {C : Type u} [Category.{v} C] (T : CategoryTheory.Monad C) where
  ideal : Kleisli T ⥤ C
  inclusion : ideal ⟶ Kleisli.Adjunction.fromKleisli T

namespace IdealizedMonad

variable {C : Type u} [Category.{v} C] {T : CategoryTheory.Monad C} (I : IdealizedMonad T)
  (P : Coproducts C)

local notation "K" => P.kleisli T

/-- The ideal comparison as a Kleisli morphism. -/
abbrev includeIdeal (A : Kleisli T) : Kleisli.mk T (I.ideal.obj A) ⟶ A :=
  kleisliArrow (I.inclusion.app A)

/-- The allowed immediate returns and ideal computations for a guarded body. -/
noncomputable def guardBody (Y Z : Kleisli T) :
    (K).sum Y (Kleisli.mk T (I.ideal.obj ((K).sum Y Z))) ⟶ (K).sum Y Z :=
  (K).desc (K).inl (I.includeIdeal ((K).sum Y Z))

/-- Strong guardedness in the definition of complete iterativity uses a base-category
factor into the coproduct of results and ideal computations. -/
def StronglyGuarded {X Y Z : Kleisli T} (f : X ⟶ (K).sum Y Z) : Prop :=
  ∃ j : X.of ⟶ P.sum Y.of (I.ideal.obj ((K).sum Y Z)),
    f = (Kleisli.Adjunction.toKleisli T).map j ≫ I.guardBody P Y Z

/-- Weak guardedness allows a Kleisli factor into the same coproduct. -/
def WeaklyGuarded {X Y Z : Kleisli T} (f : X ⟶ (K).sum Y Z) : Prop :=
  ∃ j : X ⟶ (K).sum Y (Kleisli.mk T (I.ideal.obj ((K).sum Y Z))),
    f = j ≫ I.guardBody P Y Z

/-- Complete iterativity is a property of an idealized monad. -/
def CompletelyIterative : Prop :=
  ∀ {X Y : Kleisli T} (f : X ⟶ (K).sum Y X),
    I.StronglyGuarded P (Y := Y) (Z := X) f → ∃! g, Guardedness.IsFixpoint (P := K) f g

end IdealizedMonad
end Silmaril.Calco2019
