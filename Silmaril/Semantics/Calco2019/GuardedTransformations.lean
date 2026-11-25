module

public import Silmaril.Semantics.Calco2019.VacuousThms
import Silmaril.Proofs.Semantics.Calco2019.GuardedTransformations

/-! # Guarded natural transformations in the free-extension problem -/

public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasInitial C] {P : Coproducts C}

theorem MonadGuardedness.guardedNatTrans_pre
    {T : GuardedElgotMonad P} {H H' : C ⥤ C} {σ : H ⟶ (T.monad : C ⥤ C)}
    (hσ : T.guard.GuardedNatTrans P σ) (α : H' ⟶ H) :
    T.guard.GuardedNatTrans P (α ≫ σ) :=
  Proofs.guardedNatTrans_pre hσ α

theorem MonadGuardedness.guardedNatTrans_post
    {T S : GuardedElgotMonad P} {H : C ⥤ C} {σ : H ⟶ (T.monad : C ⥤ C)}
    (hσ : T.guard.GuardedNatTrans P σ) (m : GuardedElgotMonadHom P T S) :
    S.guard.GuardedNatTrans P (σ ≫ m.hom.toNatTrans) :=
  Proofs.guardedNatTrans_post hσ m

/-- The morphisms from an endofunctor to a guarded Elgot monad in the bimodule
used by Theorem 28. -/
@[expose]
def GuardedTransformation (H : C ⥤ C) (T : GuardedElgotMonad P) :=
  {σ : H ⟶ (T.monad : C ⥤ C) // T.guard.GuardedNatTrans P σ}

/-- The bimodule of guarded natural transformations used in Theorem 28. -/
@[expose]
def guardedBimodule (P : Coproducts C) : Bimodule (C ⥤ C) (GuardedElgotMonad P) :=
  Profunctor.ofCore
    { obj T H := GuardedTransformation H T
      map m α := ↾fun σ => ⟨α ≫ σ.val ≫ m.hom.toNatTrans,
        MonadGuardedness.guardedNatTrans_pre
          (MonadGuardedness.guardedNatTrans_post σ.property m) α⟩
      map_id T H := by
        apply ConcreteCategory.coe_ext
        funext σ
        apply Subtype.ext
        change (𝟙 H) ≫ σ.val ≫ (GuardedElgotMonadHom.id T).hom.toNatTrans = σ.val
        simp [GuardedElgotMonadHom.id]
      map_comp m n α β := by
        apply ConcreteCategory.coe_ext
        funext σ
        apply Subtype.ext
        change (α ≫ β) ≫ σ.val ≫ (GuardedElgotMonadHom.comp m n).hom.toNatTrans =
          α ≫ (β ≫ σ.val ≫ m.hom.toNatTrans) ≫ n.hom.toNatTrans
        simp [GuardedElgotMonadHom.comp, Category.assoc] }

theorem guardedBimodule_post {H : C ⥤ C} {T S : GuardedElgotMonad P}
    (σ : (guardedBimodule P).Hom H T) (m : T ⟶ S) :
    ((guardedBimodule P).post σ m).val = σ.val ≫ m.hom.toNatTrans :=
  Category.id_comp _

/-- The coproduct step for Corollary 29, once the two free extensions have
been constructed. -/
theorem coproduct_of_free_extensions {H : C ⥤ C} {T : GuardedElgotMonad P}
    (F₀ : (guardedBimodule P).FreeExtension H (guardedIdentity P))
    (F : (guardedBimodule P).FreeExtension H T) :
    ∃! l : F₀.pt ⟶ F.pt, (guardedBimodule P).post F₀.generator l = F.generator ∧
      Nonempty (IsColimit (BinaryCofan.mk l F.inclusion)) := by
  let i := guardedIdentity_initial P
  have e : F₀.inclusion = i.to F₀.pt := i.hom_ext _ _
  exact freeExtension_coprodLeg ((isFreeExtension_initial_iff i F₀.generator).mp
    (e ▸ F₀.isFreeExtension)) F.isFreeExtension

end Silmaril.Calco2019
