module

public import Silmaril.Semantics.Calco2019.Parametrized
public import Silmaril.Semantics.Calco2019.Thms
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Vacuous guardedness and the initial guarded Elgot monad -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (P : Coproducts C)

/-- The coproduct-preserving pure functor also sends an initial object to an
initial object of the Kleisli category, as used in §2. -/
noncomputable def kleisliInitial (T : CategoryTheory.Monad C) {I : C} (i : IsInitial I) :
    IsInitial (Kleisli.mk T I) := by
  let J := Kleisli.Adjunction.toKleisli T
  letI : J.IsLeftAdjoint := ⟨_, ⟨Kleisli.Adjunction.adj T⟩⟩
  exact i.isInitialObj J

/-- Any monad carries the vacuous guarded Elgot structure of Example 20(1). -/
noncomputable def vacuousMonad (T : CategoryTheory.Monad C) : GuardedElgotMonad P :=
  GuardedElgotMonad.ofIterative (Guardedness.vacuous_iterative (P := P.kleisli T))

/-- The identity monad with its vacuous guard. -/
noncomputable abbrev guardedIdentity : GuardedElgotMonad P :=
  vacuousMonad P (CategoryTheory.Monad.id C)

/-- The unit is the underlying monad morphism from the identity monad. -/
def identityMonadMap (T : CategoryTheory.Monad C) : CategoryTheory.Monad.id C ⟶ T where
  toNatTrans := T.η
  app_η X := Category.id_comp _
  app_μ X := by
    change 𝟙 X ≫ T.η.app X = (T.η.app X ≫ T.η.app (T.obj X)) ≫ T.μ.app X
    simp

end Silmaril.Calco2019
