module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

/-! # Change of the pure environment in categorical LetIter combinators -/

public section

universe v₁ v₂ u₁ u₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext contextualLoop duplicate extend retainLeft splitMapCoprod)

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
local notation "fst" => CartesianMonoidalCategory.fst
local notation "snd" => CartesianMonoidalCategory.snd
local notation "lift" => CartesianMonoidalCategory.lift

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

section Distributive

variable (J : V ⥤ C) [DistributiveFreydCategory J]

private theorem retainLeft_comp {E A B D : V} (f : J.obj A ⟶ J.obj B) (g : J.obj B ⟶ J.obj D) :
    retainLeft J (R := E) (f ≫ g) = retainLeft J f ≫ retainLeft J g := by
  simp [retainLeft, leftTensor, PremonoidalCategory.whiskerLeft_comp]

private theorem retainLeft_map (E : V) {A B : V} (f : A ⟶ B) :
    retainLeft J (R := E) (J.map f) = J.map (E ◁ f) := by
  simp only [retainLeft, leftTensor, PremonoidalCategory.id_whiskerRight,
    Category.id_comp, Functor.StrongPremonoidal.tensor_naturality_right]
  simp

private theorem extend_eq_retainLeft {E A : V} (f : J.obj E ⟶ J.obj A) :
    extend J f = J.map (duplicate E) ≫ retainLeft J f := rfl

@[reassoc] private theorem distributeMap_inl (E A B : V) :
    J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫
      J.map (DistributiveTensor.leftIso E A B).inv ≫ splitMapCoprod J (E ⊗ A) (E ⊗ B) =
        coprod.inl := by
  have h : (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ (DistributiveTensor.leftIso E A B).inv =
      coprod.inl := by
    apply (cancel_mono (DistributiveTensor.leftIso E A B).hom).1
    simp [DistributiveTensor.leftIso]
  rw [← Category.assoc, ← J.map_comp, h]
  exact map_inl_inv_coprodComparison J

@[reassoc] private theorem distributeMap_inr (E A B : V) :
    J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫
      J.map (DistributiveTensor.leftIso E A B).inv ≫ splitMapCoprod J (E ⊗ A) (E ⊗ B) =
        coprod.inr := by
  have h : (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ (DistributiveTensor.leftIso E A B).inv =
      coprod.inr := by
    apply (cancel_mono (DistributiveTensor.leftIso E A B).hom).1
    simp [DistributiveTensor.leftIso]
  rw [← Category.assoc, ← J.map_comp, h]
  exact map_inr_inv_coprodComparison J

@[reassoc] private theorem extend_pre_map {D E A : V} (k : D ⟶ E)
    (f : J.obj E ⟶ J.obj A) :
    extend J (J.map k ≫ f) ≫ J.map (k ▷ A) = J.map k ≫ extend J f := by
  simp only [extend_eq_retainLeft, retainLeft_comp, retainLeft_map, Category.assoc,
    ← retainLeft_pre_map]
  simp only [← J.map_comp_assoc]
  congr 2
  rw [← MonoidalCategory.tensorHom_def']
  apply CartesianMonoidalCategory.hom_ext <;> simp [duplicate]

@[reassoc] theorem bind_pre_map_proof {D E A B : V} (k : D ⟶ E)
    (f : J.obj E ⟶ J.obj A) (g : J.obj (E ⊗ A) ⟶ J.obj B) :
    bindArrow J (J.map k ≫ f) (J.map (k ▷ A) ≫ g) = J.map k ≫ bindArrow J f g := by
  simpa only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    Category.assoc] using extend_pre_map_assoc J k f g

theorem pair_pre_map_proof {D E A B : V} (k : D ⟶ E)
    (f : J.obj E ⟶ J.obj A) (g : J.obj E ⟶ J.obj B) :
    Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair J
      (J.map k ≫ f) (J.map k ≫ g) =
    J.map k ≫ Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair J f g := by
  let p (X : V) := lift (fst (X ⊗ A) B ≫ snd X A) (snd (X ⊗ A) B)
  have projection : fst D A ≫ k = (k ▷ A) ≫ fst E A := by simp
  have output : ((k ▷ A) ▷ B) ≫ p E = p D := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [p]
  change bindArrow J (J.map k ≫ f)
    (bindArrow J (J.map (fst D A) ≫ J.map k ≫ g) (J.map (p D))) =
    J.map k ≫ bindArrow J f (bindArrow J (J.map (fst E A) ≫ g) (J.map (p E)))
  rw [← J.map_comp_assoc, projection, J.map_comp_assoc, ← output, J.map_comp,
    bind_pre_map_proof, bind_pre_map_proof]

private noncomputable def distributeEnv (E A B : V) :
    J.obj (E ⊗ (A ⨿ B)) ⟶ J.obj (E ⊗ A) ⨿ J.obj (E ⊗ B) :=
  J.map (DistributiveTensor.leftIso E A B).inv ≫ splitMapCoprod J (E ⊗ A) (E ⊗ B)

@[reassoc] private theorem distributeEnv_pre {D E A B : V} (k : D ⟶ E) :
    distributeEnv J D A B ≫
      coprod.map (J.map (k ▷ A)) (J.map (k ▷ B)) =
    J.map (k ▷ (A ⨿ B)) ≫ distributeEnv J E A B := by
  let d := distributeEnv J D A B
  have : IsIso d := by dsimp only [d, distributeEnv, splitMapCoprod]; infer_instance
  have hl : J.map (D ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ d = coprod.inl :=
    distributeMap_inl J D A B
  have hr : J.map (D ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ d = coprod.inr :=
    distributeMap_inr J D A B
  have hl' : coprod.inl ≫ inv d = J.map (D ◁ (coprod.inl : A ⟶ A ⨿ B)) := by
    rw [← hl, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hr' : coprod.inr ≫ inv d = J.map (D ◁ (coprod.inr : B ⟶ A ⨿ B)) := by
    rw [← hr, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  apply (cancel_epi (inv d)).mp
  apply coprod.hom_ext
  · rw [← Category.assoc, hl', reassoc_of% hl, coprod.inl_map, reassoc_of% hl']
    rw [← J.map_comp_assoc, MonoidalCategory.whisker_exchange, J.map_comp]
    simpa only [Category.assoc] using congrArg (J.map (k ▷ A) ≫ ·)
      (show J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ distributeEnv J E A B =
        coprod.inl from distributeMap_inl J E A B).symm
  · rw [← Category.assoc, hr', reassoc_of% hr, coprod.inr_map, reassoc_of% hr']
    rw [← J.map_comp_assoc, MonoidalCategory.whisker_exchange, J.map_comp]
    simpa only [Category.assoc] using congrArg (J.map (k ▷ B) ≫ ·)
      (show J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ distributeEnv J E A B =
        coprod.inr from distributeMap_inr J E A B).symm

theorem case_pre_map_proof {D E A B X : V} (k : D ⟶ E)
    (f : J.obj E ⟶ J.obj (A ⨿ B))
    (left : J.obj (E ⊗ A) ⟶ J.obj X) (right : J.obj (E ⊗ B) ⟶ J.obj X) :
    caseWithContext J (J.map k ≫ f) (J.map (k ▷ A) ≫ left) (J.map (k ▷ B) ≫ right) =
      J.map k ≫ caseWithContext J f left right := by
  have unfoldCase {Y : V} (f : J.obj Y ⟶ J.obj (A ⨿ B))
      (l : J.obj (Y ⊗ A) ⟶ J.obj X) (r : J.obj (Y ⊗ B) ⟶ J.obj X) :
      caseWithContext J f l r = extend J f ≫ distributeEnv J Y A B ≫ coprod.desc l r := by
    simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
      distributeEnv, Category.assoc]
  rw [unfoldCase, unfoldCase]
  rw [← coprod.map_desc, distributeEnv_pre_assoc, extend_pre_map_assoc]

end Distributive

section Iteration

variable [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]

theorem contextualLoop_pre_map_proof {D E A B : V} (k : D ⟶ E)
    (f : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) :
    contextualLoop J (J.map (k ▷ A) ≫ f) = J.map (k ▷ A) ≫ contextualLoop J f := by
  let copy (X : V) := lift (fst X A) (𝟙 (X ⊗ A))
  let step (X : V) (g : J.obj (X ⊗ A) ⟶ J.obj (B ⨿ A)) :=
    J.map (copy X) ≫ retainLeft J g ≫ distributeEnv J X B A
  let g := J.map (k ▷ A) ≫ f
  have copy_natural : copy D ≫ (D ◁ (k ▷ A)) ≫ k ▷ (E ⊗ A) = (k ▷ A) ≫ copy E := by
    rw [← MonoidalCategory.tensorHom_def']
    apply CartesianMonoidalCategory.hom_ext <;> simp [copy]
  have square : step D g ≫ coprod.map (J.map (k ▷ B)) (J.map (k ▷ A)) =
      J.map (k ▷ A) ≫ step E f := by
    simp only [step, Category.assoc, distributeEnv_pre, g, retainLeft_comp, retainLeft_map]
    rw [← retainLeft_pre_map_assoc, ← J.map_comp_assoc, ← J.map_comp_assoc, Category.assoc (copy D), copy_natural, J.map_comp_assoc]
  have outputs :
      iterate (step D g) ≫ J.map (k ▷ B) = J.map (k ▷ A) ≫ iterate (step E f) := by
    rw [ElgotCategory.naturality]
    apply ElgotFreydCategory.uniformity (J := J)
    rw [Category.assoc]
    have route : Limits.coprod.map (J.map (k ▷ B)) (𝟙 _) ≫
        Limits.coprod.map (𝟙 _) (J.map (k ▷ A)) =
        Limits.coprod.map (J.map (k ▷ B)) (J.map (k ▷ A)) := by
      apply Limits.coprod.hom_ext <;> simp
    rw [route]
    exact square
  change iterate (step D g) ≫ J.map (snd D B) = J.map (k ▷ A) ≫
    iterate (step E f) ≫ J.map (snd E B)
  have proj : (k ▷ B) ≫ snd E B = snd D B := by simp
  rw [← Category.assoc, ← outputs, Category.assoc, ← J.map_comp, proj]

end Iteration

end Silmaril.Isotope.LetIter.Semantics.Categorical
