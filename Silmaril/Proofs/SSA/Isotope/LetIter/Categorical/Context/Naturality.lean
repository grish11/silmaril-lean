module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Defs
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms

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

@[reassoc] private theorem distributeEnv_pre {D E A B : V} (k : D ⟶ E) :
    routeEnvironment J D A B ≫
      coprod.map (J.map (k ▷ A)) (J.map (k ▷ B)) =
    J.map (k ▷ (A ⨿ B)) ≫ routeEnvironment J E A B := by
  let d := routeEnvironment J D A B
  have : IsIso d := by dsimp only [d, routeEnvironment, splitMapCoprod]; infer_instance
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
      (show J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ routeEnvironment J E A B =
        coprod.inl from distributeMap_inl J E A B).symm
  · rw [← Category.assoc, hr', reassoc_of% hr, coprod.inr_map, reassoc_of% hr']
    rw [← J.map_comp_assoc, MonoidalCategory.whisker_exchange, J.map_comp]
    simpa only [Category.assoc] using congrArg (J.map (k ▷ B) ≫ ·)
      (show J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ routeEnvironment J E A B =
        coprod.inr from distributeMap_inr J E A B).symm

private theorem case_eq_distribute {E A B X : V} (f : J.obj E ⟶ J.obj (A ⨿ B))
    (l : J.obj (E ⊗ A) ⟶ J.obj X) (r : J.obj (E ⊗ B) ⟶ J.obj X) :
    caseWithContext J f l r = extend J f ≫ routeEnvironment J E A B ≫ coprod.desc l r := by
  simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    routeEnvironment, Category.assoc]

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
  let route := routeEnvironment J E A B
  have : IsIso route := by dsimp only [route, routeEnvironment, splitMapCoprod]; infer_instance
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

theorem retainEnvironment_comp_proof {E X Y Z : V} (p : X ⟶ E)
    (f : J.obj X ⟶ J.obj Y) (g : J.obj Y ⟶ J.obj Z) :
    retainEnvironment J p (f ≫ g) = retainEnvironment J p f ≫ retainLeft J g := by
  simp only [retainEnvironment, retainLeft_comp, Category.assoc]

theorem retainEnvironment_map {E X Y : V} (p : X ⟶ E) (f : X ⟶ Y) :
    retainEnvironment J p (J.map f) = J.map (lift p f) := by
  rw [retainEnvironment, retainLeft_map, ← J.map_comp]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

@[reassoc] theorem retainEnvironment_pre_proof {E X Y D : V} (q : D ⟶ X) (p : X ⟶ E)
    (f : J.obj X ⟶ J.obj Y) :
    J.map q ≫ retainEnvironment J p f = retainEnvironment J (q ≫ p) (J.map q ≫ f) := by
  rw [retainEnvironment_comp_proof, retainEnvironment_map, retainEnvironment, ← J.map_comp_assoc]
  congr 2
  simp

@[reassoc] theorem retainEnvironment_snd [FreydCategory.CentralUnit J]
    {E X Y : V} (p : X ⟶ E) (f : J.obj X ⟶ J.obj Y) :
    retainEnvironment J p f ≫ J.map (snd E Y) = f := by
  simp only [retainEnvironment, retainLeft, leftTensor, id_whiskerRight,
    Category.id_comp, Category.assoc, FreydCategory.whiskerLeft_snd]
  rw [← J.map_comp_assoc, CartesianMonoidalCategory.lift_snd, J.map_id, Category.id_comp]

@[reassoc] theorem retainEnvironment_twice {E X Y : V}
    (central : IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    (p : X ⟶ E) (f : J.obj X ⟶ J.obj Y) :
    retainEnvironment J p (retainEnvironment J p f) =
      retainEnvironment J p f ≫ J.map (lift (fst E Y) (𝟙 (E ⊗ Y))) := by
  have copy :
      lift p (𝟙 X) ≫ E ◁ lift p (𝟙 X) =
      lift p (𝟙 X) ≫ lift (fst E X) (𝟙 (E ⊗ X)) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  simp only [retainEnvironment, retainLeft_comp, retainLeft_map, Category.assoc]
  rw [← J.map_comp_assoc, copy, J.map_comp_assoc, ← copyValue_proof, retainLeft_copy_proof J f central, copyValue_proof]

private theorem capture_liftExit {E A B D : V}
    (k : J.obj (E ⊗ A) ⟶ J.obj D) :
    retainEnvironment J (fst E (A ⨿ B)) (liftExit J k) ≫ routeEnvironment J E D B =
      routeEnvironment J E A B ≫
        coprod.map (retainEnvironment J (fst E A) k) (𝟙 (J.obj (E ⊗ B))) := by
  let route := routeEnvironment J E A B
  have : IsIso route := by dsimp only [route, routeEnvironment, splitMapCoprod]; infer_instance
  have hl : J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ route = coprod.inl :=
    distributeMap_inl J E A B
  have hr : J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ route = coprod.inr :=
    distributeMap_inr J E A B
  have hli : coprod.inl ≫ inv route = J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) := by
    rw [← hl, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hri : coprod.inr ≫ inv route = J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) := by
    rw [← hr, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have outL :
      J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ liftExit J (B := B) k =
        k ≫ J.map (coprod.inl : D ⟶ D ⨿ B) := by
    rw [liftExit, reassoc_of% hl, coprod.inl_desc]
  have outR :
      J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ liftExit J (B := B) k =
        J.map (snd E B ≫ (coprod.inr : B ⟶ D ⨿ B)) := by
    rw [liftExit, reassoc_of% hr, coprod.inr_desc]
  apply (cancel_epi (inv route)).mp
  apply coprod.hom_ext
  · simp only [reassoc_of% hli]
    rw [retainEnvironment_pre_proof_assoc, CartesianMonoidalCategory.whiskerLeft_fst,
      outL, retainEnvironment_comp_proof, retainLeft_map]
    rw [reassoc_of% hl, coprod.inl_map]
    simp only [Category.assoc, routeEnvironment]
    exact congrArg (retainEnvironment J (fst E A) k ≫ ·) (distributeMap_inl J E D B)
  · simp only [reassoc_of% hri]
    rw [retainEnvironment_pre_proof_assoc, CartesianMonoidalCategory.whiskerLeft_fst,
      outR, retainEnvironment_map]
    have prodMap :
        lift (fst E B) (snd E B ≫ (coprod.inr : B ⟶ D ⨿ B)) = E ◁ coprod.inr := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [prodMap]
    rw [reassoc_of% hr, coprod.inr_map, Category.id_comp]
    exact distributeMap_inr J E D B

private theorem route_tensor_comparison (E A B : V) :
    routeEnvironment J E A B =
      (Functor.StrongPremonoidal.tensorIso (J := J) E (A ⨿ B)).inv ≫
        (J.obj E ◁ splitMapCoprod J A B) ≫
        DistributivePremonoidalCategory.leftInv (J.obj E) (J.obj A) (J.obj B) ≫
        coprod.map (Functor.StrongPremonoidal.tensorIso (J := J) E A).hom
          (Functor.StrongPremonoidal.tensorIso (J := J) E B).hom := by
  let t := Functor.StrongPremonoidal.tensorIso (J := J)
  let route := routeEnvironment J E A B
  let δ := DistributiveTensor.leftIso (J.obj E) (J.obj A) (J.obj B)
  have : IsIso route := by dsimp only [route, routeEnvironment, splitMapCoprod]; infer_instance
  have ht {P Q : V} (f : P ⟶ Q) :
      J.map (E ◁ f) ≫ (t E Q).inv = (t E P).inv ≫ J.obj E ◁ J.map f := by
    apply (cancel_mono (t E Q).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [Functor.StrongPremonoidal.tensor_naturality_right, Iso.inv_hom_id_assoc]
  have hl : J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ route = coprod.inl :=
    distributeMap_inl J E A B
  have hr : J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ route = coprod.inr :=
    distributeMap_inr J E A B
  have δl : (J.obj E ◁ (coprod.inl : J.obj A ⟶ J.obj A ⨿ J.obj B)) ≫ δ.inv = coprod.inl := by
    apply (cancel_mono δ.hom).mp
    simp [δ, DistributiveTensor.leftIso]
  have δr : (J.obj E ◁ (coprod.inr : J.obj B ⟶ J.obj A ⨿ J.obj B)) ≫ δ.inv = coprod.inr := by
    apply (cancel_mono δ.hom).mp
    simp [δ, DistributiveTensor.leftIso]
  apply (cancel_epi (inv route)).mp
  apply coprod.hom_ext
  · have hinv : coprod.inl ≫ inv route = J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) := by
      rw [← hl, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, hinv, hl, reassoc_of% hinv, reassoc_of% (ht (coprod.inl : A ⟶ A ⨿ B)),
      ← whiskerLeft_comp_assoc]
    have hc : J.map (coprod.inl : A ⟶ A ⨿ B) ≫ splitMapCoprod J A B = coprod.inl :=
      map_inl_inv_coprodComparison J
    rw [hc]
    change _ = (t E A).inv ≫ (J.obj E ◁ coprod.inl) ≫ δ.inv ≫ _
    rw [reassoc_of% δl, coprod.inl_map, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · have hinv : coprod.inr ≫ inv route = J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) := by
      rw [← hr, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, hinv, hr, reassoc_of% hinv, reassoc_of% (ht (coprod.inr : B ⟶ A ⨿ B)),
      ← whiskerLeft_comp_assoc]
    have hc : J.map (coprod.inr : B ⟶ A ⨿ B) ≫ splitMapCoprod J A B = coprod.inr :=
      map_inr_inv_coprodComparison J
    rw [hc]
    change _ = (t E B).inv ≫ (J.obj E ◁ coprod.inr) ≫ δ.inv ≫ _
    rw [reassoc_of% δr, coprod.inr_map, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem route_graph (E A B : V) :
    retainEnvironment J (fst E (A ⨿ B)) (J.map (DistributiveTensor.leftIso E A B).inv) ≫
        routeEnvironment J E (E ⊗ A) (E ⊗ B) =
      routeEnvironment J E A B ≫ Limits.coprod.map
        (J.map (lift (fst E A) (𝟙 (E ⊗ A)))) (J.map (lift (fst E B) (𝟙 (E ⊗ B)))) := by
  let δ := DistributiveTensor.leftIso E A B
  let route := routeEnvironment J E A B
  have : IsIso route := by dsimp only [route, routeEnvironment, splitMapCoprod]; infer_instance
  have hl : J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ route = coprod.inl :=
    distributeMap_inl J E A B
  have hr : J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ route = coprod.inr :=
    distributeMap_inr J E A B
  have δl : (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ δ.inv = coprod.inl := by
    apply (cancel_mono δ.hom).mp
    simp [δ, DistributiveTensor.leftIso]
  have δr : (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ δ.inv = coprod.inr := by
    apply (cancel_mono δ.hom).mp
    simp [δ, DistributiveTensor.leftIso]
  apply (cancel_epi (inv route)).mp
  apply coprod.hom_ext
  · have hinv : coprod.inl ≫ inv route = J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) := by
      rw [← hl, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, hinv, retainEnvironment_pre_proof_assoc, CartesianMonoidalCategory.whiskerLeft_fst,
      ← J.map_comp, δl, retainEnvironment_map]
    have graph : lift (fst E A) (coprod.inl : E ⊗ A ⟶ (E ⊗ A) ⨿ (E ⊗ B)) =
        lift (fst E A) (𝟙 _) ≫ (E ◁ coprod.inl) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [graph, J.map_comp_assoc, reassoc_of% hinv, reassoc_of% hl, coprod.inl_map]
    simpa only [routeEnvironment, Category.assoc] using
      congrArg (J.map (lift (fst E A) (𝟙 (E ⊗ A))) ≫ ·)
        (distributeMap_inl J E (E ⊗ A) (E ⊗ B))
  · have hinv : coprod.inr ≫ inv route = J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) := by
      rw [← hr, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, hinv, retainEnvironment_pre_proof_assoc, CartesianMonoidalCategory.whiskerLeft_fst,
      ← J.map_comp, δr, retainEnvironment_map]
    have graph : lift (fst E B) (coprod.inr : E ⊗ B ⟶ (E ⊗ A) ⨿ (E ⊗ B)) =
        lift (fst E B) (𝟙 _) ≫ (E ◁ coprod.inr) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [graph, J.map_comp_assoc, reassoc_of% hinv, reassoc_of% hr, coprod.inr_map]
    simpa only [routeEnvironment, Category.assoc] using
      congrArg (J.map (lift (fst E B) (𝟙 (E ⊗ B))) ≫ ·)
        (distributeMap_inr J E (E ⊗ A) (E ⊗ B))

theorem bind_retainEnvironment_proof {E X Y D : V} (p : X ⟶ E)
    (f : J.obj X ⟶ J.obj Y) (k : J.obj (E ⊗ Y) ⟶ J.obj D) :
    bindArrow J f (J.map (p ▷ Y) ≫ k) = retainEnvironment J p f ≫ k := by
  have h : duplicate X ≫ p ▷ X = lift p (𝟙 X) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
        duplicate, CartesianMonoidalCategory.lift_fst_assoc, Category.id_comp,
        CartesianMonoidalCategory.lift_fst]
    · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
        duplicate, CartesianMonoidalCategory.lift_snd]
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    extend_eq_retainLeft, retainEnvironment, Category.assoc]
  rw [← retainLeft_pre_map_assoc, ← J.map_comp_assoc, h]

theorem caseWithContext_liftExit_proof [FreydCategory.CentralUnit J] {E A B D Z : V}
    (central : IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    (f : J.obj E ⟶ J.obj (A ⨿ B)) (k : J.obj (E ⊗ A) ⟶ J.obj D)
    (out : J.obj D ⟶ J.obj Z) (loop : J.obj (E ⊗ B) ⟶ J.obj Z) :
    caseWithContext J (bindArrow J f (liftExit J k)) (J.map (snd E D) ≫ out) loop =
      caseWithContext J f (k ≫ out) loop := by
  change bindArrow J (bindArrow J f (liftExit J k))
    (J.map (DistributiveTensor.leftIso E D B).inv ≫ splitMapCoprod J (E ⊗ D) (E ⊗ B) ≫ _) =
    bindArrow J f
      (J.map (DistributiveTensor.leftIso E A B).inv ≫ splitMapCoprod J (E ⊗ A) (E ⊗ B) ≫ _)
  rw [bind_assoc_capture_proof J central, bind_retainEnvironment_proof]
  have h := capture_liftExit J (B := B) k
  change retainEnvironment J (fst E (A ⨿ B)) (liftExit J k) ≫
      routeEnvironment J E D B = _ at h
  have assoc := reassoc_of% h
  change bindArrow J f (retainEnvironment J (fst E (A ⨿ B)) (liftExit J k) ≫
    (J.map (DistributiveTensor.leftIso E D B).inv ≫ splitMapCoprod J (E ⊗ D) (E ⊗ B) ≫ _)) = _
  have route (E A B : V) : routeEnvironment J E A B =
      J.map (DistributiveTensor.leftIso E A B).inv ≫ splitMapCoprod J (E ⊗ A) (E ⊗ B) := rfl
  simp only [route, Category.assoc] at assoc
  rw [assoc, Limits.coprod.map_desc, Category.id_comp, retainEnvironment_snd_assoc]

theorem bind_purePayload_proof {E B D : V} (k : J.obj (E ⊗ B) ⟶ J.obj D) :
    bindArrow J (J.map (snd E B)) (J.map (fst E B ▷ B) ≫ k) = k := by
  have h : lift (fst E B) (snd E B) = 𝟙 (E ⊗ B) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [bind_retainEnvironment_proof, retainEnvironment_map, h, J.map_id, Category.id_comp]

private theorem case_exit_transform {R A B D : V}
    (f : J.obj (R ⊗ A) ⟶ J.obj (B ⨿ A)) (k : J.obj (R ⊗ B) ⟶ J.obj D) :
    caseWithContext J f
      (J.map (fst R A ▷ B) ≫ k ≫ J.map (coprod.inl : D ⟶ D ⨿ A))
      (J.map (snd (R ⊗ A) A ≫ coprod.inr)) =
    retainEnvironment J (fst R A) f ≫ liftExit J k := by
  have right : J.map (snd (R ⊗ A) A ≫ (coprod.inr : A ⟶ D ⨿ A)) =
      J.map (fst R A ▷ A) ≫ J.map (snd R A ≫ coprod.inr) := by
    rw [← J.map_comp, CartesianMonoidalCategory.whiskerRight_snd_assoc]
  rw [right, case_eq_distribute, ← coprod.map_desc, distributeEnv_pre_assoc]
  change bindArrow J f (J.map (fst R A ▷ (B ⨿ A)) ≫ liftExit J k) = _
  exact bind_retainEnvironment_proof J _ _ _

private theorem route_collapse (R A B : V) :
    J.map (R ◁ coprod.desc (𝟙 (B ⨿ A)) (coprod.inr : A ⟶ B ⨿ A)) ≫
      routeEnvironment J R B A =
    routeEnvironment J R (B ⨿ A) A ≫ coprod.desc (routeEnvironment J R B A) coprod.inr := by
  let route := routeEnvironment J R (B ⨿ A) A
  have : IsIso route := by dsimp only [route, routeEnvironment, splitMapCoprod]; infer_instance
  have hl : J.map (R ◁ (coprod.inl : B ⨿ A ⟶ (B ⨿ A) ⨿ A)) ≫ route = coprod.inl :=
    distributeMap_inl J R (B ⨿ A) A
  have hr : J.map (R ◁ (coprod.inr : A ⟶ (B ⨿ A) ⨿ A)) ≫ route = coprod.inr :=
    distributeMap_inr J R (B ⨿ A) A
  have hl' : coprod.inl ≫ inv route = J.map (R ◁ (coprod.inl : B ⨿ A ⟶ (B ⨿ A) ⨿ A)) := by
    rw [← hl, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hr' : coprod.inr ≫ inv route = J.map (R ◁ (coprod.inr : A ⟶ (B ⨿ A) ⨿ A)) := by
    rw [← hr, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  change _ = route ≫ _
  apply (cancel_epi (inv route)).mp
  simp only [IsIso.inv_hom_id_assoc]
  apply coprod.hom_ext
  · rw [← Category.assoc, hl', ← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
      coprod.inl_desc, MonoidalCategory.whiskerLeft_id, J.map_id, Category.id_comp, coprod.inl_desc]
  · have routeRight : J.map (R ◁ (coprod.inr : A ⟶ B ⨿ A)) ≫ routeEnvironment J R B A = coprod.inr :=
      distributeMap_inr J R B A
    rw [← Category.assoc, hr', ← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
      coprod.inr_desc, routeRight, coprod.inr_desc]

private theorem route_map_exit {R A B S : V} (e : A ⟶ B) :
    J.map (R ◁ coprod.map e (𝟙 S)) ≫ routeEnvironment J R B S =
      routeEnvironment J R A S ≫ coprod.map (J.map (R ◁ e)) (𝟙 (J.obj (R ⊗ S))) := by
  let route := routeEnvironment J R A S
  have : IsIso route := by dsimp only [route, routeEnvironment, splitMapCoprod]; infer_instance
  have left : J.map (R ◁ (coprod.inl : A ⟶ A ⨿ S)) ≫ route = coprod.inl :=
    distributeMap_inl J R A S
  have right : J.map (R ◁ (coprod.inr : S ⟶ A ⨿ S)) ≫ route = coprod.inr :=
    distributeMap_inr J R A S
  have left' : coprod.inl ≫ inv route = J.map (R ◁ (coprod.inl : A ⟶ A ⨿ S)) := by
    rw [← left, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have right' : coprod.inr ≫ inv route = J.map (R ◁ (coprod.inr : S ⟶ A ⨿ S)) := by
    rw [← right, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  change _ = route ≫ _
  apply (cancel_epi (inv route)).mp
  simp only [IsIso.inv_hom_id_assoc]
  apply coprod.hom_ext
  · have step : J.map (R ◁ (coprod.inl : B ⟶ B ⨿ S)) ≫ routeEnvironment J R B S = coprod.inl :=
      distributeMap_inl J R B S
    rw [← Category.assoc, left', ← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
      coprod.inl_map, MonoidalCategory.whiskerLeft_comp, J.map_comp_assoc, step, coprod.inl_map]
  · have step : J.map (R ◁ (coprod.inr : S ⟶ B ⨿ S)) ≫ routeEnvironment J R B S = coprod.inr :=
      distributeMap_inr J R B S
    rw [← Category.assoc, right', ← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
      coprod.inr_map, Category.id_comp, step, coprod.inr_map, Category.id_comp]

end Distributive

section Iteration

variable [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]

theorem contextualLoop_pre_map_proof {D E A B : V} (k : D ⟶ E)
    (f : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) :
    contextualLoop J (J.map (k ▷ A) ≫ f) = J.map (k ▷ A) ≫ contextualLoop J f := by
  let copy (X : V) := lift (fst X A) (𝟙 (X ⊗ A))
  let step (X : V) (g : J.obj (X ⊗ A) ⟶ J.obj (B ⨿ A)) :=
    J.map (copy X) ≫ retainLeft J g ≫ routeEnvironment J X B A
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
    J.map (lift p (𝟙 E)) ≫ retainLeft J f ≫ routeEnvironment J R B A
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
    extend J f ≫ routeEnvironment J E B A ≫
      coprod.desc (J.map (p ▷ B) ≫ out) (J.map (p ▷ A) ≫ iterate step ≫ out)
  rw [← coprod.map_desc, distributeEnv_pre_assoc, ← Category.assoc (extend J f),
    prepare, Category.assoc, ← Category.assoc (retainLeft J f), ← Category.assoc (J.map (lift p (𝟙 E)))]
  change iterate step ≫ out = step ≫ coprod.desc out (iterate step ≫ out)
  conv_lhs => rw [ElgotCategory.fixpoint_assoc]
  rw [coprod.desc_comp, Category.id_comp]

theorem contextualStep_liftExit {E A B D : V}
    (central : IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    (body : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) (k : J.obj (E ⊗ B) ⟶ J.obj D) :
    contextualStep J (retainEnvironment J (fst E A) body ≫ liftExit J k) =
      contextualStep J body ≫ Limits.coprod.map (retainEnvironment J (fst E B) k) (𝟙 _) := by
  simp only [contextualStep, retainEnvironment_comp_proof, retainEnvironment_twice J central,
    Category.assoc]
  simpa only [retainEnvironment, Category.assoc] using
    congrArg (retainEnvironment J (fst E A) body ≫ ·) (capture_liftExit J (B := A) k)

theorem contextualLoop_eq_step {E A B : V} (body : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) :
    contextualLoop J body = iterate (contextualStep J body) ≫ J.map (snd E B) := by
  simp only [contextualLoop, contextualStep, retainEnvironment, routeEnvironment, Category.assoc]

theorem contextualLoop_liftExit_proof [FreydCategory.CentralUnit J] {E A B D : V}
    (central : IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    (body : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) (k : J.obj (E ⊗ B) ⟶ J.obj D) :
    contextualLoop J (retainEnvironment J (fst E A) body ≫ liftExit J k) =
      iterate (contextualStep J body) ≫ k := by
  rw [contextualLoop_eq_step, contextualStep_liftExit J central, ← ElgotCategory.naturality, Category.assoc, retainEnvironment_snd]

omit [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [DistributivePremonoidalCategory C] in
private theorem iterate_retype {X X' Y Y' : C} (e : X = X') (k : Y ⟶ Y')
    (f : X ⟶ Y ⨿ X) :
    iterate ((eqToIso e).inv ≫ f ≫ Limits.coprod.map k (eqToIso e).hom) =
      (eqToIso e).inv ≫ iterate f ≫ k := by
  subst X'
  simpa using (ElgotCategory.naturality f k).symm

theorem retainLeft_iterate_shared {E X Y : V}
    (shared : ∃ e : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso e)
    (body : J.obj X ⟶ J.obj (Y ⨿ X)) :
    iterate (retainLeft J (R := E) body ≫ routeEnvironment J E Y X) =
      retainLeft J (R := E) (iterate (body ≫ splitMapCoprod J Y X)) := by
  let t := Functor.StrongPremonoidal.tensorIso (J := J)
  let f := body ≫ splitMapCoprod J Y X
  let δ := DistributivePremonoidalCategory.leftInv (J.obj E) (J.obj Y) (J.obj X)
  let g := (J.obj E ◁ f) ≫ δ
  have step : retainLeft J (R := E) body ≫ routeEnvironment J E Y X =
      (t E X).inv ≫ g ≫ Limits.coprod.map (t E Y).hom (t E X).hom := by
    rw [route_tensor_comparison]
    simp only [retainLeft, leftTensor, id_whiskerRight, Category.id_comp, Category.assoc,
      Iso.hom_inv_id_assoc, g, f, t, δ, whiskerLeft_comp]
  have reindex :
      iterate ((t E X).inv ≫ g ≫ Limits.coprod.map (t E Y).hom (t E X).hom) =
        (t E X).inv ≫ iterate g ≫ (t E Y).hom := by
    obtain ⟨h, ht⟩ := shared
    change t E X = eqToIso h at ht
    rw [ht]
    exact iterate_retype h (t E Y).hom g
  rw [step, reindex]
  dsimp only [g, δ]
  rw [StrongElgotFreydCategory.strength J]
  simp only [retainLeft, leftTensor, id_whiskerRight, Category.id_comp, f, t]

theorem contextualLoop_retain_proof {E A B : V}
    (central : IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    (shared : ∃ e : J.obj E ⊗ J.obj (E ⊗ A) = J.obj (E ⊗ (E ⊗ A)),
      Functor.StrongPremonoidal.tensorIso (J := J) E (E ⊗ A) = eqToIso e)
    (body : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) :
    retainEnvironment J (fst E A) (contextualLoop J body) = iterate (contextualStep J body) := by
  let X := E ⊗ A
  let Y := E ⊗ B
  let f := retainEnvironment J (fst E A) body ≫ J.map (DistributiveTensor.leftIso E B A).inv
  let g := retainLeft J (R := E) f ≫ routeEnvironment J E Y X
  let graph (T : V) := lift (fst E T) (𝟙 (E ⊗ T))
  have old : f ≫ splitMapCoprod J Y X = contextualStep J body := by
    simp only [f, X, Y, contextualStep, routeEnvironment, Category.assoc]
  have simulation : contextualStep J body ≫ Limits.coprod.map (J.map (graph B)) (J.map (graph A)) =
      J.map (graph A) ≫ g := by
    have eq : retainEnvironment J (fst E A) f =
        retainEnvironment J (fst E A) body ≫
          retainEnvironment J (fst E (B ⨿ A)) (J.map (DistributiveTensor.leftIso E B A).inv) := by
      dsimp only [f]
      rw [retainEnvironment_comp_proof, retainEnvironment_twice J central]
      simp only [retainEnvironment, Category.assoc]
    calc
      _ = retainEnvironment J (fst E A) f ≫ routeEnvironment J E Y X := by
        simp only [graph, X, Y, contextualStep, Category.assoc, ← route_graph J E B A, eq]
      _ = _ := by simp only [retainEnvironment, graph, g, Category.assoc]
  have transport : iterate (contextualStep J body) ≫ J.map (graph B) = J.map (graph A) ≫ iterate g := by
    rw [ElgotCategory.naturality]
    apply ElgotFreydCategory.uniformity (J := J)
    rw [Category.assoc]
    have maps : Limits.coprod.map (J.map (graph B)) (𝟙 _) ≫ Limits.coprod.map (𝟙 _) (J.map (graph A)) =
        Limits.coprod.map (J.map (graph B)) (J.map (graph A)) := by
      apply Limits.coprod.hom_ext <;> simp
    rw [maps, simulation]
  have finish : graph B ≫ (E ◁ snd E B) = 𝟙 (E ⊗ B) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [graph]
  rw [contextualLoop_eq_step, retainEnvironment_comp_proof, retainLeft_map]
  change (J.map (graph A) ≫ retainLeft J (iterate (contextualStep J body))) ≫ J.map (E ◁ snd E B) = _
  rw [← old, ← retainLeft_iterate_shared J shared, ← show g =
    retainLeft J (R := E) f ≫ routeEnvironment J E Y X from rfl, ← transport,
    Category.assoc, ← J.map_comp, finish, J.map_id, Category.comp_id, old]

theorem contextualLoop_naturality_proof [FreydCategory.CentralUnit J] {R A B D : V}
    (central : IsCentral (J.map (duplicate R) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) R R).inv))
    (shared : ∃ e : J.obj R ⊗ J.obj (R ⊗ A) = J.obj (R ⊗ (R ⊗ A)),
      Functor.StrongPremonoidal.tensorIso (J := J) R (R ⊗ A) = eqToIso e)
    (f : J.obj (R ⊗ A) ⟶ J.obj (B ⨿ A)) (k : J.obj (R ⊗ B) ⟶ J.obj D) :
    bindArrow J (contextualLoop J f) (J.map (fst R A ▷ B) ≫ k) =
      contextualLoop J (caseWithContext J f
        (J.map (fst R A ▷ B) ≫ k ≫ J.map (coprod.inl : D ⟶ D ⨿ A))
        (J.map (snd (R ⊗ A) A ≫ coprod.inr))) := by
  rw [bind_retainEnvironment_proof, contextualLoop_retain_proof J central shared, case_exit_transform,
    contextualLoop_liftExit_proof J central]

theorem contextualLoop_codiagonal_proof {R A B : V}
    (central : IsCentral (J.map (duplicate R) ≫ (Functor.StrongPremonoidal.tensorIso (J := J) R R).inv))
    (shared : ∃ h : J.obj R ⊗ J.obj (R ⊗ A) = J.obj (R ⊗ (R ⊗ A)),
      Functor.StrongPremonoidal.tensorIso (J := J) R (R ⊗ A) = eqToIso h)
    (f : J.obj (R ⊗ A) ⟶ J.obj ((B ⨿ A) ⨿ A)) :
    contextualLoop J (contextualLoop J f) =
      contextualLoop J (f ≫ J.map (coprod.desc (𝟙 (B ⨿ A)) (coprod.inr : A ⟶ B ⨿ A))) := by
  let collapse := coprod.desc (𝟙 (B ⨿ A)) (coprod.inr : A ⟶ B ⨿ A)
  have body :
      contextualStep J (f ≫ J.map collapse) =
        contextualStep J f ≫ coprod.desc (routeEnvironment J R B A) coprod.inr := by
    simp only [contextualStep, retainEnvironment_comp_proof, retainLeft_map, Category.assoc,
      collapse, route_collapse]
  have nested : contextualStep J (contextualLoop J f) =
      iterate (contextualStep J f) ≫ routeEnvironment J R B A := by
    change retainEnvironment J (fst R A) (contextualLoop J f) ≫ routeEnvironment J R B A = _
    rw [contextualLoop_retain_proof J central shared f]
  rw [contextualLoop_eq_step, nested,
    ElgotCategory.naturality (contextualStep J f) (routeEnvironment J R B A),
    ElgotCategory.codiagonal]
  change _ = contextualLoop J (f ≫ J.map collapse)
  rw [contextualLoop_eq_step, body, Category.assoc, coprod.map_desc, Category.comp_id, Category.id_comp]

theorem contextualLoop_map_value_exit_proof {R A B S : V}
    (f : J.obj (R ⊗ S) ⟶ J.obj (A ⨿ S)) (e : A ⟶ B) :
    contextualLoop J (f ≫ J.map (coprod.map e (𝟙 S))) =
      contextualLoop J f ≫ J.map e := by
  have step : contextualStep J (f ≫ J.map (coprod.map e (𝟙 S))) =
      contextualStep J f ≫ coprod.map (J.map (R ◁ e)) (𝟙 (J.obj (R ⊗ S))) := by
    simp only [contextualStep, retainEnvironment_comp_proof, retainLeft_map, Category.assoc,
      route_map_exit]
  rw [contextualLoop_eq_step, step, ← ElgotCategory.naturality, contextualLoop_eq_step,
    Category.assoc, Category.assoc, ← J.map_comp, ← J.map_comp,
    CartesianMonoidalCategory.whiskerLeft_snd]

end Iteration

end Silmaril.Isotope.LetIter.Semantics.Categorical
