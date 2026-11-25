module

public import Silmaril.Semantics.Calco2019.Maybe.Thms
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Finite exits and infinite recurrence in a deterministic loop -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Maybe

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {P : Coproducts C} {X Y : C}

/-- The coproduct branches of a pure deterministic body. Branch zero returns;
branch (n+1) advances to branch (n); the residual branch is invariant. -/
structure LoopDecomposition (f : X ⟶ P.sum Y X) where
  finite : ℕ → C
  residual : C
  finiteIn (n : ℕ) : finite n ⟶ X
  residualIn : residual ⟶ X
  result : finite 0 ⟶ Y
  advance (n : ℕ) : finite (n + 1) ⟶ finite n
  residualStep : residual ⟶ residual
  zero_eq : finiteIn 0 ≫ f = result ≫ P.inl
  succ_eq (n : ℕ) : finiteIn (n + 1) ≫ f = advance n ≫ finiteIn n ≫ P.inr
  residual_eq : residualIn ≫ f = residualStep ≫ residualIn ≫ P.inr
  isColimit : IsColimit (Cofan.mk (f := fun i : Option ℕ => i.elim residual finite) X
    (fun i : Option ℕ => match i with | some n => finiteIn n | none => residualIn))

variable (T : GuardedElgotMonad P) (total : T.IsElgot)

/-- Iteration of a deterministic loop after embedding its body into the Kleisli category. -/
noncomputable def iteratePure (f : X ⟶ P.sum Y X) : X ⟶ T.monad.obj Y :=
  let pureBody := (Kleisli.Adjunction.toKleisli T.monad).map f
  (T.iteration.iterate pureBody (total pureBody)).of

end Silmaril.Calco2019.Maybe
