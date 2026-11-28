module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

/-! # Phase uniformity is sound by pure uniformity of the model -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (PhaseUniform)
open Paper.TypeCategory
open Paper.Extension.Singleton (SeedDenotes)
open Semantics.Categorical
open Semantics.Categorical.SingletonDispatcher (payload_labelInject)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v u₁ u₂ v₁ v₂
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V)
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
    Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)

set_option hygiene false in
local notation "F" => Paper.TypeCategory.denoteFunctor (Φ := Φ) J M shared

set_option backward.isDefEq.respectTransparency false

omit [FreydCategory.CentralUnit J] in
theorem comparison_desc {X Y Z : V} (u : X ⟶ Z) (v : Y ⟶ Z) :
    inv (coprodComparison J X Y) ≫ coprod.desc (J.map u) (J.map v) = J.map (coprod.desc u v) := by
  rw [IsIso.inv_comp_eq]
  apply coprod.hom_ext
  · rw [coprod.inl_desc, inl_coprodComparison_assoc, ← J.map_comp, coprod.inl_desc]
  · rw [coprod.inr_desc, inr_coprodComparison_assoc, ← J.map_comp, coprod.inr_desc]

/-- The denotation of the phase fold is the image of a pure map. -/
theorem map_phaseFold (A : τ) :
    ∀ k, ∃ m : M.obj (phaseType A k) ⟶ M.obj A, (F).map (phaseFold (Φ := Φ) A k) = J.map m
  | 0 => ⟨𝟙 _, ((F).map_id _).trans (J.map_id _).symm⟩
  | k + 1 => by
    obtain ⟨m, hm⟩ := map_phaseFold A k
    refine ⟨(M.coprodIso A (phaseType A k)).hom ≫ coprod.desc (𝟙 _) m, ?_⟩
    have desc := denoteFunctor_map_desc (Φ := Φ) J M shared (𝟙 (ofType A)) (phaseFold A k)
    have unfolded : phaseFold (Φ := Φ) A (k + 1) =
        (sumIso A (phaseType A k)).hom ≫ coprod.desc (𝟙 _) (phaseFold A k) := rfl
    have cancel : (F).map (sumIso (Φ := Φ) A (phaseType A k)).hom ≫
        (denoteCoprodIso J M shared A (phaseType A k)).hom =
        (denoteExactSumIso J M A (phaseType A k)).hom := by
      have inverse : (F).map (sumIso (Φ := Φ) A (phaseType A k)).hom ≫
          (F).map (sumIso (Φ := Φ) A (phaseType A k)).inv = 𝟙 _ :=
        ((F).map_comp _ _).symm.trans
          ((congrArg (F).map (sumIso (Φ := Φ) A (phaseType A k)).hom_inv_id).trans ((F).map_id _))
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (denoteExactSumIso J M A (phaseType A k)).hom) inverse).trans
          (Category.id_comp _))
    have step : (F).map (phaseFold (Φ := Φ) A (k + 1)) =
        (denoteExactSumIso J M A (phaseType A k)).hom ≫
          coprod.desc (𝟙 (J.obj (M.obj A))) (J.map m) := by
      rw [unfolded, Functor.map_comp, desc, hm, (F).map_id, reassoc_of% cancel]
      rfl
    rw [step]
    exact (Category.assoc _ _ _).trans
      ((congrArg (J.map (M.coprodIso A (phaseType A k)).hom ≫ ·)
        ((congrArg (fun i => inv (coprodComparison J (M.obj A) (M.obj (phaseType A k))) ≫
          coprod.desc i (J.map m)) (J.map_id (M.obj A)).symm).trans
            (comparison_desc J (𝟙 _) m))).trans (J.map_comp _ _).symm)

include shared in
/-- The seed is sound: the square maps to a square along a pure map, and
pure uniformity of the model identifies the two loops. -/
theorem phase_denotes : SeedDenotes (Seed := PhaseUniform (τ := τ) (Φ := Φ)) J M := by
  intro Γ r s L seed hr hs
  cases seed with
  | @fold k A B f g square r s hr' hs' left right =>
    obtain ⟨m, hm⟩ := map_phaseFold (Φ := Φ) J M shared A k
    let c₁ := denoteCoprodIso (Φ := Φ) J M shared B (phaseType A k)
    let c₂ := denoteCoprodIso (Φ := Φ) J M shared B A
    have mapSum : (F).map (coprod.map (𝟙 (ofType B)) (phaseFold (Φ := Φ) A k)) ≫ c₂.hom =
        c₁.hom ≫ coprod.map (𝟙 _) (J.map m) := by
      have shape : coprod.map (𝟙 (ofType B)) (phaseFold (Φ := Φ) A k) =
          coprod.desc coprod.inl (phaseFold A k ≫ coprod.inr) := by
        apply coprod.hom_ext <;> simp
      rw [shape, denoteFunctor_map_desc (Φ := Φ) J M shared, Category.assoc]
      congr 1
      apply coprod.hom_ext
      · rw [coprod.inl_desc_assoc, coprod.inl_map, Category.id_comp]
        exact denoteFunctor_map_inl (Φ := Φ) J M shared B A
      · rw [coprod.inr_desc_assoc, coprod.inr_map, Functor.map_comp, Category.assoc, hm]
        exact congrArg (J.map m ≫ ·) (denoteFunctor_map_inr (Φ := Φ) J M shared B A)
    have sq : ((F).map f ≫ c₁.hom) ≫ coprod.map (𝟙 _) (J.map m) = J.map m ≫ ((F).map g ≫ c₂.hom) := by
      have mapped := congrArg (F).map square
      rw [Functor.map_comp, Functor.map_comp, hm] at mapped
      rw [Category.assoc, ← mapSum, ← Category.assoc, mapped, Category.assoc]
    have loops := ElgotFreydCategory.pure_uniformity J _ _ m sq
    have arrows : (F).map (ofRegion hr') = (F).map (ofRegion hs') := by
      rw [left, right, Functor.map_comp, hm, denoteFunctor_map_iterate, denoteFunctor_map_iterate]
      exact loops
    have eq : denoteSingletonRegion J M hr = denoteSingletonRegion J M hs :=
      (denoteArrow_ofRegion J M shared hr').symm.trans (arrows.trans (denoteArrow_ofRegion J M shared hs'))
    have source : J.map (λ_ (M.obj (phaseType A k))).hom ≫ J.map (λ_ (M.obj (phaseType A k))).inv = 𝟙 _ := by
      rw [← J.map_comp, Iso.hom_inv_id, J.map_id]
    have payload : J.map (singletonLabelPayload M B) ≫ J.map (labelInject M 0 (L := [B]) rfl) = 𝟙 _ := by
      rw [← J.map_comp, payload_labelInject, J.map_id]
    have closed := congrArg (fun f => J.map (λ_ (M.obj (phaseType A k))).hom ≫ f ≫
      J.map (labelInject M 0 (L := [B]) rfl)) eq
    simp only [denoteSingletonRegion, Category.assoc, reassoc_of% source, payload, Category.comp_id] at closed
    exact ⟨_, denoteRegion_spec J M hr, closed.symm ▸ denoteRegion_spec J M hs⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity
