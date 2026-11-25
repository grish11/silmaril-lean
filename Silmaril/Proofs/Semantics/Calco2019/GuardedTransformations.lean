module

public import Silmaril.Semantics.Calco2019.Vacuous
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasInitial C] {P : Coproducts C}
  {H H' : C ⥤ C} {T S : GuardedElgotMonad P}

theorem guardedNatTrans_pre {σ : H ⟶ (T.monad : C ⥤ C)}
    (hσ : T.guard.GuardedNatTrans P σ) (α : H' ⟶ H) :
    T.guard.GuardedNatTrans P (α ≫ σ) := by
  intro X
  let f : H.obj X ⟶ T.monad.obj (P.sum (⊥_ C) X) :=
    σ.app X ≫ T.monad.map (P.inr (X := ⊥_ C))
  have h := Guardedness.precomp (hσ X) ((Kleisli.Adjunction.toKleisli T.monad).map (α.app X))
  have e : (α ≫ σ).app X ≫ T.monad.map (P.inr (X := ⊥_ C) (Y := X)) = α.app X ≫ f :=
    Category.assoc _ _ _
  have e' := pure_comp_of T.monad (α.app X) (kleisliArrow f)
  exact Eq.mpr (congrArg (fun t => T.guard.guarded (Y := Kleisli.mk T.monad (⊥_ C))
    (Z := Kleisli.mk T.monad X) (kleisliArrow t)) (e.trans e'.symm)) h

theorem guardedNatTrans_post {σ : H ⟶ (T.monad : C ⥤ C)}
    (hσ : T.guard.GuardedNatTrans P σ) (φ : GuardedElgotMonadHom P T S) :
    S.guard.GuardedNatTrans P (σ ≫ φ.hom.toNatTrans) := by
  intro X
  let i : X ⟶ P.sum (⊥_ C) X := P.inr
  let f := σ.app X ≫ T.monad.map i
  have e : (σ ≫ φ.hom.toNatTrans).app X ≫ S.monad.map i = f ≫ φ.hom.app (P.sum (⊥_ C) X) := by
    change (σ.app X ≫ φ.hom.app X) ≫ S.monad.map i = (σ.app X ≫ T.monad.map i) ≫ _
    rw [Category.assoc, Category.assoc, ← φ.hom.toNatTrans.naturality i]
  exact Eq.mpr (congrArg (fun t => S.guard.guarded (Y := Kleisli.mk S.monad (⊥_ C))
    (Z := Kleisli.mk S.monad X) (kleisliArrow t)) e) (φ.guarded f (hσ X))

end Silmaril.Calco2019.Proofs
