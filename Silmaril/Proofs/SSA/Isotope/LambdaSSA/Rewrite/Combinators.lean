module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms

/-! # Categorical dispatch and contextual unfolding -/

public section

universe v₁ v₂ u₁ u₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext contextualLoop duplicate extend retainLeft splitMapCoprod)

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

section Distributive

variable (J : Functor V C) [DistributiveFreydCategory J]

theorem retainLeft_comp {E A B D : V} (f : J.obj A ⟶ J.obj B) (g : J.obj B ⟶ J.obj D) :
    retainLeft J (R := E) (f ≫ g) = retainLeft J f ≫ retainLeft J g := by
  simp [retainLeft, leftTensor, PremonoidalCategory.whiskerLeft_comp]

theorem retainLeft_map (E : V) {A B : V} (f : A ⟶ B) :
    retainLeft J (R := E) (J.map f) = J.map (E ◁ f) := by
  simp only [retainLeft, leftTensor, PremonoidalCategory.id_whiskerRight,
    Category.id_comp, Functor.StrongPremonoidal.tensor_naturality_right]
  simp

theorem extend_eq_retainLeft {E A : V} (f : J.obj E ⟶ J.obj A) :
    extend J f = J.map (duplicate E) ≫ retainLeft J f := rfl

theorem extend_post_map {E A B : V} (f : J.obj E ⟶ J.obj A) (g : A ⟶ B) :
    extend J (f ≫ J.map g) = extend J f ≫ J.map (E ◁ g) := by
  rw [extend_eq_retainLeft, retainLeft_comp, retainLeft_map, ← Category.assoc,
    ← extend_eq_retainLeft]

theorem extend_map {E A : V} (f : E ⟶ A) :
    extend J (J.map f) = J.map (CartesianMonoidalCategory.lift (𝟙 E) f) := by
  rw [extend_eq_retainLeft, retainLeft_map, ← J.map_comp]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp [duplicate]

theorem pair_map {E A B : V} (f : E ⟶ A) (g : E ⟶ B) :
    Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair J (J.map f) (J.map g) =
      J.map (CartesianMonoidalCategory.lift f g) := by
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair,
    Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.retainedContext,
    extend_map, ← J.map_comp]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

@[reassoc] theorem distributeMap_inl (E A B : V) :
    J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫
      J.map (DistributiveTensor.leftIso E A B).inv ≫ splitMapCoprod J (E ⊗ A) (E ⊗ B) =
        coprod.inl := by
  have h : (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ (DistributiveTensor.leftIso E A B).inv =
      coprod.inl := by
    apply (cancel_mono (DistributiveTensor.leftIso E A B).hom).1
    simp [DistributiveTensor.leftIso]
  rw [← Category.assoc, ← J.map_comp, h]
  exact map_inl_inv_coprodComparison J

@[reassoc] theorem distributeMap_inr (E A B : V) :
    J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫
      J.map (DistributiveTensor.leftIso E A B).inv ≫ splitMapCoprod J (E ⊗ A) (E ⊗ B) =
        coprod.inr := by
  have h : (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ (DistributiveTensor.leftIso E A B).inv =
      coprod.inr := by
    apply (cancel_mono (DistributiveTensor.leftIso E A B).hom).1
    simp [DistributiveTensor.leftIso]
  rw [← Category.assoc, ← J.map_comp, h]
  exact map_inr_inv_coprodComparison J

theorem case_inl {E A B D : V} (f : J.obj E ⟶ J.obj A)
    (l : J.obj (E ⊗ A) ⟶ J.obj D) (r : J.obj (E ⊗ B) ⟶ J.obj D) :
    caseWithContext J (f ≫ J.map (coprod.inl : A ⟶ A ⨿ B)) l r = bindArrow J f l := by
  dsimp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind]
  simp only [extend_post_map, Category.assoc, distributeMap_inl_assoc, coprod.inl_desc]

theorem case_inr {E A B D : V} (f : J.obj E ⟶ J.obj B)
    (l : J.obj (E ⊗ A) ⟶ J.obj D) (r : J.obj (E ⊗ B) ⟶ J.obj D) :
    caseWithContext J (f ≫ J.map (coprod.inr : B ⟶ A ⨿ B)) l r = bindArrow J f r := by
  dsimp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind]
  simp only [extend_post_map, Category.assoc, distributeMap_inr_assoc, coprod.inr_desc]

end Distributive

section Iteration

variable [Iteration C] [ElgotCategory C] (J : Functor V C) [StrongElgotFreydCategory J]

/-- Iteration begins at the chosen state while the same environment is available to the body. -/
theorem contextualLoop_enter {E A B D : V} (a : E ⟶ A) (i : A ⟶ D)
    (body : J.obj (E ⊗ D) ⟶ J.obj (B ⨿ D)) :
    bindArrow J (J.map a) (J.map (E ◁ i) ≫ contextualLoop J body) =
      caseWithContext J (bindArrow J (J.map a) (J.map (E ◁ i) ≫ body))
        (J.map (CartesianMonoidalCategory.snd E B)) (contextualLoop J body) := by
  let p : E ⟶ E ⊗ D := CartesianMonoidalCategory.lift (𝟙 E) (a ≫ i)
  let fst : E ⊗ D ⟶ E := CartesianMonoidalCategory.fst E D
  have hp : CartesianMonoidalCategory.lift (𝟙 E) a ≫ (E ◁ i) = p := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [p]
  have hcopy : p ≫ CartesianMonoidalCategory.lift fst (𝟙 (E ⊗ D)) =
      duplicate E ≫ (E ◁ p) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [p, fst, duplicate]
  let route := J.map (DistributiveTensor.leftIso E B D).inv ≫
    splitMapCoprod J (E ⊗ B) (E ⊗ D)
  let step := J.map (CartesianMonoidalCategory.lift fst (𝟙 (E ⊗ D))) ≫
    retainLeft J body ≫ route
  let out := J.map (CartesianMonoidalCategory.snd E B)
  have hextend : extend J (J.map p ≫ body) ≫ route = J.map p ≫ step := by
    rw [extend_eq_retainLeft, retainLeft_comp, retainLeft_map]
    simp only [Category.assoc, step]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hcopy]
  have hloop : contextualLoop J body = iterate step ≫ out := rfl
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map, ← Functor.map_comp_assoc, hp]
  have dispatch : caseWithContext J (J.map p ≫ body) out (contextualLoop J body) =
      (extend J (J.map p ≫ body) ≫ route) ≫ coprod.desc out (contextualLoop J body) := by
    simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
      route, Category.assoc]
  have unfoldStep : iterate step ≫ out = step ≫ coprod.desc out (iterate step ≫ out) :=
    calc
      _ = step ≫ coprod.desc (𝟙 _) (iterate step) ≫ out :=
        ElgotCategory.fixpoint_assoc step out
      _ = _ := by rw [coprod.desc_comp, Category.id_comp]
  rw [dispatch, hextend, hloop, Category.assoc]
  exact congrArg (J.map p ≫ ·) unfoldStep

end Iteration

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
