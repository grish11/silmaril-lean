module

public import Silmaril.Semantics.Calco2019.OmegaContinuous.Defs
import Silmaril.Semantics.Domain.ScottInduction
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard

public section

universe u v

namespace Silmaril.Calco2019.Proofs.OmegaContinuous

open CategoryTheory Category CartesianMonoidalCategory
open scoped MonoidalCategory
open OmegaCompletePartialOrder Silmaril.Semantics.Domain

private theorem fusion {D E : Type*} [OmegaCompletePartialOrder D] [OrderBot D]
    [OmegaCompletePartialOrder E] [OrderBot E] {F : D →𝒄 D} {G : E →𝒄 E} {p : D → E}
    (hp : ωScottContinuous p) (hbot : p ⊥ = ⊥) (comm : ∀ x, p (F x) = G (p x)) :
    p (fix F) = fix G := by
  have chain : ∀ n : ℕ, p (kleeneChain (F : D →o D) n) = kleeneChain (G : E →o E) n := by
    intro n
    induction n with
    | zero => exact hbot
    | succ n ih =>
        rw [kleeneChain_succ, kleeneChain_succ]
        exact (comm _).trans (congrArg G ih)
  unfold fix
  rw [hp.map_ωSup]
  congr 1
  ext n
  exact chain n

section Category

variable {K : Type u} [Category.{v} K] {Q : Coproducts K}
    [∀ X Y : K, OmegaCompletePartialOrder (X ⟶ Y)] [∀ X Y : K, OrderBot (X ⟶ Y)]
    (E : OmegaEnrichment Q)

include E in
private theorem continuous_postcompose {X Y Z : K} (g : Y ⟶ Z) :
    ωScottContinuous fun f : X ⟶ Y => f ≫ g :=
  E.comp_continuous.comp (Prod.ωScottContinuous.prodMk ωScottContinuous.id ωScottContinuous.const)

include E in
private theorem continuous_precompose {X Y Z : K} (f : X ⟶ Y) :
    ωScottContinuous fun g : Y ⟶ Z => f ≫ g :=
  E.comp_continuous.comp (Prod.ωScottContinuous.prodMk ωScottContinuous.const ωScottContinuous.id)

include E in
private theorem continuous_copair {X Y Z : K} (a : X ⟶ Z) :
    ωScottContinuous fun b : Y ⟶ Z => Q.desc a b :=
  E.desc_continuous.comp (Prod.ωScottContinuous.prodMk ωScottContinuous.const ωScottContinuous.id)

local notation "iter" => fun f => E.fixpoints.iterate f trivial

private theorem naturality {X Y Z : K} (f : X ⟶ Q.sum Y X) (g : Y ⟶ Z) :
    iter (f ≫ Q.map g (𝟙 X)) = iter f ≫ g := by
  refine (fusion (F := E.unfolding f) (G := E.unfolding _) (continuous_postcompose E g)
    (E.bot_comp g) fun k => ?_).symm
  change (f ≫ Q.desc (𝟙 Y) k) ≫ g = (f ≫ Q.map g (𝟙 X)) ≫ Q.desc (𝟙 Z) (k ≫ g)
  simp

private theorem codiagonal {X Y : K} (f : X ⟶ Q.sum (Q.sum Y X) X) :
    iter (f ≫ Q.merge) = iter (iter f) := by
  have unfold_inner (k : X ⟶ Q.sum Y X) (r : X ⟶ Y) :
      (f ≫ Q.desc (𝟙 (Q.sum Y X)) k) ≫ Q.desc (𝟙 Y) r =
        f ≫ Q.desc (Q.desc (𝟙 Y) r) (k ≫ Q.desc (𝟙 Y) r) := by simp
  have unfold_merged (r : X ⟶ Y) :
      (f ≫ Q.merge) ≫ Q.desc (𝟙 Y) r = f ≫ Q.desc (Q.desc (𝟙 Y) r) r := by
    simp [Coproducts.merge]
  apply le_antisymm
  · apply fix_le (f := E.unfolding (f ≫ Q.merge))
    let r := iter (iter f)
    have inner := E.fixpoints.fixpoint f trivial
    have outer := E.fixpoints.fixpoint (iter f) trivial
    change f ≫ Q.desc (𝟙 (Q.sum Y X)) (iter f) = iter f at inner
    change iter f ≫ Q.desc (𝟙 Y) r = r at outer
    have eq := unfold_inner (iter f) r
    rw [inner, outer] at eq
    change (f ≫ Q.merge) ≫ Q.desc (𝟙 Y) r ≤ r
    rw [unfold_merged]
    exact eq.symm.le
  · apply fix_le (f := E.unfolding (iter f))
    let r := iter (f ≫ Q.merge)
    have hr : f ≫ Q.desc (Q.desc (𝟙 Y) r) r = r :=
      (unfold_merged r).symm.trans (E.fixpoints.fixpoint (f ≫ Q.merge) trivial)
    change iter f ≫ Q.desc (𝟙 Y) r ≤ r
    refine fix_induction (f := E.unfolding f) (P := fun k => k ≫ Q.desc (𝟙 Y) r ≤ r)
      (by rw [E.bot_comp]; exact bot_le)
      (ChainClosed.le_of_continuous (continuous_postcompose E _) ωScottContinuous.const) fun k hk => ?_
    change (f ≫ Q.desc (𝟙 (Q.sum Y X)) k) ≫ Q.desc (𝟙 Y) r ≤ r
    rw [unfold_inner]
    calc
      _ ≤ f ≫ Q.desc (Q.desc (𝟙 Y) r) r :=
        (continuous_precompose E f).monotone ((continuous_copair E _).monotone hk)
      _ = r := hr

theorem naturalCodiagonal : E.fixpoints.NaturalCodiagonal where
  naturality f g _ _ := naturality E f g
  codiagonal f _ _ _ _ := codiagonal E f

theorem uniformAt {X Z : K} (h : Z ⟶ X) (strict : ∀ Y, h ≫ (⊥ : X ⟶ Y) = ⊥) :
    E.fixpoints.UniformAt h := by
  intro Y f g _ _ comm
  refine fusion (F := E.unfolding f) (G := E.unfolding g) (continuous_precompose E h) (strict Y) fun k => ?_
  change h ≫ f ≫ Q.desc (𝟙 Y) k = g ≫ Q.desc (𝟙 Y) (h ≫ k)
  rw [← assoc, comm]
  simp

include E in
private theorem iso_inv_comp_bot {X Y Z : K} (e : X ≅ Y) :
    e.inv ≫ (⊥ : X ⟶ Z) = ⊥ := by
  refine le_antisymm ?_ bot_le
  have h : (⊥ : X ⟶ Z) ≤ e.hom ≫ (⊥ : Y ⟶ Z) := bot_le
  simpa using (continuous_precompose E e.inv).monotone h

end Category

section Kleisli

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {P : Coproducts C}
    {T : Monad C} [T.Strong] [∀ X Y : Kleisli T, OmegaCompletePartialOrder (X ⟶ Y)]
    [∀ X Y : Kleisli T, OrderBot (X ⟶ Y)]

local notation "J" => Kleisli.Adjunction.toKleisli T

/-- Strength and strict postcomposition identify bottom with the constant
divergence obtained from the tensor unit. -/
private theorem terminal_comp_bot (E : OmegaContinuousMonad P T) (A : C) (Y : Kleisli T) :
    (J).map (toUnit A) ≫ (⊥ : Kleisli.mk T (𝟙_ C) ⟶ Y) = ⊥ := by
  let b : Kleisli.mk T (𝟙_ C) ⟶ Y := ⊥
  have strength_proj :
      strengthWhisker A b ≫ (J).map (snd A Y.of) = (J).map (snd A (𝟙_ C)) ≫ b := by
    apply Kleisli.hom_ext
    rw [comp_pure_of, pure_comp_of]
    change ((A ◁ b.of) ≫ Monad.Strong.strength A Y.of) ≫ T.map (snd A Y.of) =
      snd A (𝟙_ C) ≫ b.of
    rw [← whiskerRight_toUnit_comp_leftUnitor_hom A Y.of, T.map_comp, assoc, ← Monad.Strong.naturality_left_assoc,
      MonoidalCategory.whisker_exchange_assoc, Monad.Strong.left_unitality,
      MonoidalCategory.leftUnitor_naturality, whiskerRight_toUnit_comp_leftUnitor_hom_assoc]
  have bot_proj : (J).map (snd A (𝟙_ C)) ≫ b = ⊥ :=
    strength_proj.symm.trans ((E.strength_bot A) ▸ E.bot_comp ((J).map (snd A Y.of)))
  have h := congrArg (fun k => (J).map (ρ_ A).inv ≫ k) bot_proj
  rw [← assoc, ← (J).map_comp, rightUnitor_inv_snd] at h
  exact h.trans (iso_inv_comp_bot E.toOmegaEnrichment ((J).mapIso (ρ_ A)))

theorem pure_comp_bot (E : OmegaContinuousMonad P T) {X Z : C} (h : X ⟶ Z) (Y : Kleisli T) :
    (J).map h ≫ (⊥ : Kleisli.mk T Z ⟶ Y) = ⊥ := by
  rw [← terminal_comp_bot E Z Y, ← assoc, ← (J).map_comp, comp_toUnit, terminal_comp_bot E]

end Kleisli

end Silmaril.Calco2019.Proofs.OmegaContinuous
