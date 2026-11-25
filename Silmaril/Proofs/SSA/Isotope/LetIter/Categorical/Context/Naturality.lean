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

private theorem case_eq_distribute {E A B X : V} (f : J.obj E ⟶ J.obj (A ⨿ B))
    (l : J.obj (E ⊗ A) ⟶ J.obj X) (r : J.obj (E ⊗ B) ⟶ J.obj X) :
    caseWithContext J f l r = extend J f ≫ distributeEnv J E A B ≫ coprod.desc l r := by
  simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    distributeEnv, Category.assoc]

theorem case_pre_map_proof {D E A B X : V} (k : D ⟶ E)
    (f : J.obj E ⟶ J.obj (A ⨿ B))
    (left : J.obj (E ⊗ A) ⟶ J.obj X) (right : J.obj (E ⊗ B) ⟶ J.obj X) :
    caseWithContext J (J.map k ≫ f) (J.map (k ▷ A) ≫ left) (J.map (k ▷ B) ≫ right) =
      J.map k ≫ caseWithContext J f left right := by
  rw [case_eq_distribute, case_eq_distribute]
  rw [← coprod.map_desc, distributeEnv_pre_assoc, extend_pre_map_assoc]

theorem case_bind_value_proof {E P A B X : V} (f : J.obj E ⟶ J.obj P)
    (p : P ⟶ A ⨿ B) (l : J.obj (E ⊗ A) ⟶ J.obj X) (r : J.obj (E ⊗ B) ⟶ J.obj X) :
    caseWithContext J (f ≫ J.map p) l r =
      bindArrow J f (caseWithContext J (J.map (snd E P ≫ p))
        (J.map (fst E P ▷ A) ≫ l) (J.map (fst E P ▷ B) ≫ r)) := by
  simp only [case_eq_distribute, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind]
  rw [extend_postmap, Category.assoc, extend_map, ← coprod.map_desc, distributeEnv_pre_assoc,
    ← J.map_comp_assoc]
  have h : lift (𝟙 (E ⊗ P)) (snd E P ≫ p) ≫ (fst E P ▷ (A ⨿ B)) = E ◁ p := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [h]

local notation "tIso" => Functor.StrongPremonoidal.tensorIso (J := J)

private theorem retainLeft_whisker {R A B : V} (f : J.obj A ⟶ J.obj B) :
    retainLeft J (R := R) f = (tIso R A).inv ≫ J.obj R ◁ f ≫ (tIso R B).hom := by
  simp only [retainLeft, leftTensor, id_whiskerRight, Category.id_comp]

theorem retainLeft_copy_proof {E A B : V} (f : J.obj A ⟶ J.obj B)
    (central : IsCentral (J.map (duplicate E) ≫ (tIso E E).inv)) :
    J.map ((duplicate E ▷ A) ≫ (α_ E E A).hom) ≫
      retainLeft J (R := E) (retainLeft J (R := E) f) =
    retainLeft J (R := E) f ≫ J.map ((duplicate E ▷ B) ≫ (α_ E E B).hom) := by
  let d := J.map (duplicate E) ≫ (tIso E E).inv
  have transport (X : V) :
      (tIso E X).hom ≫ J.map ((duplicate E ▷ X) ≫ (α_ E E X).hom) =
        (d ▷ J.obj X) ≫ (α_ (J.obj E) (J.obj E) (J.obj X)).hom ≫
          J.obj E ◁ (tIso E X).hom ≫ (tIso E (E ⊗ X)).hom := by
    rw [J.map_comp, ← Category.assoc, ← Functor.StrongPremonoidal.tensor_naturality_left,
      Category.assoc]
    have h := Functor.StrongPremonoidal.associativity (J := J) E E X
    simp only [d, comp_whiskerRight, Category.assoc]
    rw [h]
    rw [← comp_whiskerRight_assoc (tIso E E).inv, Iso.inv_hom_id,
      id_whiskerRight, Category.id_comp]
  apply (cancel_epi (tIso E A).hom).mp
  simp only [Category.assoc, retainLeft_whisker, Iso.hom_inv_id_assoc]
  rw [reassoc_of% (transport A), transport B]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, whiskerLeft_comp]
  rw [← whiskerLeft_comp_assoc, Iso.hom_inv_id, whiskerLeft_id, Category.id_comp,
    ← associator_naturality_right_assoc]
  have slide := central.1 f
  change (d ▷ J.obj A) ≫ (J.obj E ⊗ J.obj E) ◁ f =
    J.obj E ◁ f ≫ d ▷ J.obj B at slide
  rw [reassoc_of% slide]

omit [SymmetricCategory V] [HasFiniteCoproducts V] [DistributiveTensor V] in
theorem copyValue_proof (E A : V) :
    (duplicate E ▷ A) ≫ (α_ E E A).hom = lift (fst E A) (𝟙 (E ⊗ A)) := by
  have h : duplicate E ▷ A = lift (lift (fst E A) (fst E A)) (snd E A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [duplicate]
  rw [h, CartesianMonoidalCategory.lift_lift_associator_hom]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

@[reassoc] theorem extend_capture_proof {E A : V} (f : J.obj E ⟶ J.obj A)
    (central : IsCentral (J.map (duplicate E) ≫ (tIso E E).inv)) :
    J.map (duplicate E) ≫ retainLeft J (R := E) (extend J f) =
      extend J f ≫ J.map (lift (fst E A) (𝟙 (E ⊗ A))) := by
  have same : duplicate E ≫ E ◁ duplicate E =
      duplicate E ≫ (duplicate E ▷ E) ≫ (α_ E E E).hom := by
    rw [copyValue_proof]
    apply CartesianMonoidalCategory.hom_ext <;> simp [duplicate]
  simp only [extend_eq_retainLeft, retainLeft_comp, retainLeft_map, Category.assoc]
  rw [← J.map_comp_assoc, same, J.map_comp_assoc]
  rw [retainLeft_copy_proof J f central, copyValue_proof]

theorem bind_assoc_capture_proof {E A B D : V}
    (central : IsCentral (J.map (duplicate E) ≫ (tIso E E).inv))
    (f : J.obj E ⟶ J.obj A) (g : J.obj (E ⊗ A) ⟶ J.obj B)
    (k : J.obj (E ⊗ B) ⟶ J.obj D) :
    bindArrow J (bindArrow J f g) k =
      bindArrow J f (bindArrow J g (J.map (fst E A ▷ B) ≫ k)) := by
  have prepare : duplicate (E ⊗ A) ≫ fst E A ▷ (E ⊗ A) =
      lift (fst E A) (𝟙 (E ⊗ A)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
        duplicate, CartesianMonoidalCategory.lift_fst_assoc, Category.id_comp,
        CartesianMonoidalCategory.lift_fst]
    · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
        duplicate, CartesianMonoidalCategory.lift_snd]
  change extend J (extend J f ≫ g) ≫ k = extend J f ≫ extend J g ≫ J.map (fst E A ▷ B) ≫ k
  have lhs : extend J (extend J f ≫ g) =
      J.map (duplicate E) ≫ retainLeft J (R := E) (extend J f) ≫ retainLeft J (R := E) g := by
    rw [extend_eq_retainLeft, retainLeft_comp]
  rw [lhs, Category.assoc, Category.assoc, extend_capture_proof_assoc J f central]
  simp only [extend_eq_retainLeft J g, Category.assoc]
  rw [← retainLeft_pre_map_assoc, ← J.map_comp_assoc, prepare]

theorem bind_assoc_reindex_proof {E A X B D : V}
    (central : IsCentral (J.map (duplicate E) ≫ (tIso E E).inv))
    (f : J.obj E ⟶ J.obj A) (p : E ⊗ A ⟶ X)
    (g : J.obj X ⟶ J.obj B) (q : X ⟶ E) (hq : p ≫ q = fst E A)
    (k : J.obj (E ⊗ B) ⟶ J.obj D) :
    bindArrow J (bindArrow J f (J.map p ≫ g)) k =
      bindArrow J f (J.map p ≫ bindArrow J g (J.map (q ▷ B) ≫ k)) := by
  rw [bind_assoc_capture_proof J central, ← bind_pre_map_proof, ← J.map_comp_assoc,
    ← MonoidalCategory.comp_whiskerRight, hq]

theorem bind_case_capture_proof {E A B X Y : V}
    (central : IsCentral (J.map (duplicate E) ≫ (tIso E E).inv))
    (scrutinee : J.obj E ⟶ J.obj (A ⨿ B))
    (left : J.obj (E ⊗ A) ⟶ J.obj X) (right : J.obj (E ⊗ B) ⟶ J.obj X)
    (k : J.obj (E ⊗ X) ⟶ J.obj Y) :
    bindArrow J (caseWithContext J scrutinee left right) k =
      caseWithContext J scrutinee
        (bindArrow J left (J.map (fst E A ▷ X) ≫ k))
        (bindArrow J right (J.map (fst E B ▷ X) ≫ k)) := by
  let route := distributeEnv J E A B
  have : IsIso route := by dsimp only [route, distributeEnv, splitMapCoprod]; infer_instance
  have case_def {D : V} (l : J.obj (E ⊗ A) ⟶ J.obj D) (r : J.obj (E ⊗ B) ⟶ J.obj D) :
      caseWithContext J scrutinee l r = bindArrow J scrutinee (route ≫ coprod.desc l r) :=
    case_eq_distribute J scrutinee l r
  have route_left : J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ route = coprod.inl :=
    distributeMap_inl J E A B
  have route_right : J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ route = coprod.inr :=
    distributeMap_inr J E A B
  rw [case_def, case_def, bind_assoc_capture_proof J central]
  congr 1
  apply (cancel_epi (inv route)).mp
  apply coprod.hom_ext
  · have unpack : coprod.inl ≫ inv route = J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) := by
      rw [← route_left, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have projection :
        ((E ◁ (coprod.inl : A ⟶ A ⨿ B)) ▷ X) ≫ (fst E (A ⨿ B) ▷ X) =
          fst E A ▷ X := by
      rw [← MonoidalCategory.comp_whiskerRight, CartesianMonoidalCategory.whiskerLeft_fst]
    rw [← Category.assoc, unpack, ← bind_pre_map_proof, reassoc_of% route_left, coprod.inl_desc,
      ← J.map_comp_assoc, projection]
    change _ = coprod.inl ≫ inv route ≫ route ≫ _
    rw [IsIso.inv_hom_id_assoc, coprod.inl_desc]
  · have unpack : coprod.inr ≫ inv route = J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) := by
      rw [← route_right, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have projection :
        ((E ◁ (coprod.inr : B ⟶ A ⨿ B)) ▷ X) ≫ (fst E (A ⨿ B) ▷ X) =
          fst E B ▷ X := by
      rw [← MonoidalCategory.comp_whiskerRight, CartesianMonoidalCategory.whiskerLeft_fst]
    rw [← Category.assoc, unpack, ← bind_pre_map_proof, reassoc_of% route_right, coprod.inr_desc,
      ← J.map_comp_assoc, projection]
    change _ = coprod.inr ≫ inv route ≫ route ≫ _
    rw [IsIso.inv_hom_id_assoc, coprod.inr_desc]

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

theorem contextualLoop_fixpoint_proof {R A B : V} (f : J.obj (R ⊗ A) ⟶ J.obj (B ⨿ A)) :
    contextualLoop J f = caseWithContext J f
      (J.map (snd (R ⊗ A) B)) (J.map (fst R A ▷ A) ≫ contextualLoop J f) := by
  let E := R ⊗ A
  let p : E ⟶ R := fst R A
  let step : J.obj E ⟶ J.obj (R ⊗ B) ⨿ J.obj E :=
    J.map (lift p (𝟙 E)) ≫ retainLeft J f ≫ distributeEnv J R B A
  let out : J.obj (R ⊗ B) ⟶ J.obj B := J.map (snd R B)
  have prepare : extend J f ≫ J.map (p ▷ (B ⨿ A)) =
      J.map (lift p (𝟙 E)) ≫ retainLeft J f := by
    simp only [extend_eq_retainLeft, Category.assoc, ← retainLeft_pre_map, ← J.map_comp_assoc]
    have h : duplicate E ≫ (p ▷ E) = lift p (𝟙 E) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [duplicate]
    rw [h]
  have project : J.map (snd E B) = J.map (p ▷ B) ≫ out := by
    rw [← J.map_comp]
    simp
  rw [case_eq_distribute, project]
  change iterate step ≫ out =
    extend J f ≫ distributeEnv J E B A ≫
      coprod.desc (J.map (p ▷ B) ≫ out) (J.map (p ▷ A) ≫ iterate step ≫ out)
  rw [← coprod.map_desc, distributeEnv_pre_assoc, ← Category.assoc (extend J f),
    prepare, Category.assoc, ← Category.assoc (retainLeft J f), ← Category.assoc (J.map (lift p (𝟙 E)))]
  change iterate step ≫ out = step ≫ coprod.desc out (iterate step ≫ out)
  conv_lhs => rw [ElgotCategory.fixpoint_assoc]
  rw [coprod.desc_comp, Category.id_comp]

end Iteration

end Silmaril.Isotope.LetIter.Semantics.Categorical
