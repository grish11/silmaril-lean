module

public import Silmaril.SSA.Isotope.LetIter.Categorical.AbortSequence.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.Validity.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.LocallySmallValidity.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Admitting the repaired LetIter model with larger objects and small homs -/


open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.LocallySmallValidityProofs

attribute [local instance] CategoryTheory.uliftCategory

abbrev Obj (K : Type u) := ULift.{1} K

variable {K : Type u} [Category.{v} K]

local notation "L" => Obj K
local notation "down" => (CategoryTheory.ULift.downFunctor : L ⥤ K)

local instance downEquivalence : (down).IsEquivalence := by
  change ((CategoryTheory.ULift.equivalence : K ≌ L).inverse).IsEquivalence
  infer_instance

private def liftIso {X Y : L} (i : X.down ≅ Y.down) : X ≅ Y :=
  ⟨i.hom, i.inv, i.hom_inv_id, i.inv_hom_id⟩

local instance liftedTensor [MonoidalCategoryStruct K] : MonoidalCategoryStruct L where
  tensorObj X Y := ⟨X.down ⊗ Y.down⟩
  whiskerLeft X {_ _} f := X.down ◁ f
  whiskerRight {_ _} f Y := MonoidalCategoryStruct.whiskerRight (C := K) f Y.down
  tensorHom f g := MonoidalCategoryStruct.tensorHom (C := K) f g
  tensorUnit := ⟨𝟙_ K⟩
  associator X Y Z := liftIso (α_ X.down Y.down Z.down)
  leftUnitor X := liftIso (λ_ X.down)
  rightUnitor X := liftIso (ρ_ X.down)

section
variable [MonoidalCategory K]

open MonoidalCategory in
local instance liftedMonoidal : MonoidalCategory L where
  toMonoidalCategoryStruct := liftedTensor
  tensorHom_def f g := tensorHom_def (C := K) f g
  id_tensorHom_id X Y := id_tensorHom_id X.down Y.down
  tensorHom_comp_tensorHom f g h k := tensorHom_comp_tensorHom (C := K) f g h k
  whiskerLeft_id X Y := whiskerLeft_id X.down Y.down
  id_whiskerRight X Y := id_whiskerRight X.down Y.down
  associator_naturality f g h := associator_naturality (C := K) f g h
  leftUnitor_naturality f := leftUnitor_naturality (C := K) f
  rightUnitor_naturality f := rightUnitor_naturality (C := K) f
  pentagon W X Y Z := pentagon W.down X.down Y.down Z.down
  triangle X Y := triangle X.down Y.down

end

attribute [local instance] liftedMonoidal

section
variable [MonoidalCategory K] [SymmetricCategory K]

open BraidedCategory in
local instance liftedValueSymmetric : SymmetricCategory L where
  braiding X Y := liftIso (braiding X.down Y.down)
  braiding_naturality_left f Z := braiding_naturality_left (C := K) f Z.down
  braiding_naturality_right X {_ _} f := braiding_naturality_right X.down f
  hexagon_forward X Y Z := hexagon_forward X.down Y.down Z.down
  hexagon_reverse X Y Z := hexagon_reverse X.down Y.down Z.down
  symmetry X Y := SymmetricCategory.symmetry X.down Y.down

end

section
variable [CartesianMonoidalCategory K]

open CartesianMonoidalCategory in
noncomputable local instance liftedCartesian : CartesianMonoidalCategory L where
  toMonoidalCategory := liftedMonoidal
  isTerminalTensorUnit := IsTerminal.ofUniqueHom (fun X => toUnit X.down)
    (fun X f => isTerminalTensorUnit.hom_ext (Y := X.down) f _)
  fst X Y := fst X.down Y.down
  snd X Y := snd X.down Y.down
  fst_def X Y := SemiCartesianMonoidalCategory.fst_def X.down Y.down
  snd_def X Y := SemiCartesianMonoidalCategory.snd_def X.down Y.down
  tensorProductIsBinaryProduct X Y :=
    isLimitOfReflectsOfMapIsLimit down _ _ (tensorProductIsBinaryProduct X.down Y.down)

end

section
variable [PremonoidalCategory K]

open PremonoidalCategory in
private theorem liftCentral {X Y : L} {f : X ⟶ Y} (h : IsCentral (C := K) f) :
    IsCentral f := by
  exact ⟨fun {P Q} g => h.1 (X' := P.down) (Y' := Q.down) g,
    fun {P Q} g => h.2 (X' := P.down) (Y' := Q.down) g⟩

open PremonoidalCategory in
local instance liftedPremonoidal : PremonoidalCategory L where
  tensorHom_def f g := tensorHom_def (C := K) f g
  whiskerLeft_id X Y := whiskerLeft_id X.down Y.down
  whiskerLeft_comp X {_ _ _} f g := whiskerLeft_comp X.down f g
  id_whiskerRight X Y := id_whiskerRight X.down Y.down
  comp_whiskerRight f g W := comp_whiskerRight (C := K) f g W.down
  associator_central X Y Z := liftCentral (associator_central X.down Y.down Z.down)
  leftUnitor_central X := liftCentral (leftUnitor_central X.down)
  rightUnitor_central X := liftCentral (rightUnitor_central X.down)
  associator_naturality_left f Z W := associator_naturality_left (C := K) f Z.down W.down
  associator_naturality_middle X {_ _} f W := associator_naturality_middle X.down f W.down
  associator_naturality_right X Y {_ _} f := associator_naturality_right X.down Y.down f
  leftUnitor_naturality f := leftUnitor_naturality (C := K) f
  rightUnitor_naturality f := rightUnitor_naturality (C := K) f
  pentagon W X Y Z := pentagon W.down X.down Y.down Z.down
  triangle X Y := triangle X.down Y.down

open BraidedPremonoidalCategory in
local instance liftedSymmetric [SymmetricPremonoidalCategory K] : SymmetricPremonoidalCategory L where
  braiding X Y := liftIso (braiding X.down Y.down)
  naturality_left f Z := naturality_left (C := K) f Z.down
  naturality_right X {_ _} f := naturality_right X.down f
  hexagon_forward X Y Z := hexagon_forward X.down Y.down Z.down
  hexagon_reverse X Y Z := hexagon_reverse X.down Y.down Z.down
  braiding_central X Y := liftCentral (braiding_central X.down Y.down)
  symmetry X Y := SymmetricPremonoidalCategory.symmetry X.down Y.down

end

section Coproducts

variable [HasFiniteCoproducts K]

local instance liftedCoproducts : HasFiniteCoproducts L :=
  ⟨fun _ => Adjunction.hasColimitsOfShape_of_equivalence down⟩

noncomputable def coprodIso (X Y : L) : (down).obj (X ⨿ Y) ≅ (down).obj X ⨿ (down).obj Y :=
  (asIso (Limits.coprodComparison down X Y)).symm

@[reassoc] theorem coprodIso_inl (X Y : L) :
    (down).map (coprod.inl : X ⟶ X ⨿ Y) ≫ (coprodIso X Y).hom = coprod.inl :=
  map_inl_inv_coprodComparison down (A := X) (B := Y)

@[reassoc] theorem coprodIso_inr (X Y : L) :
    (down).map (coprod.inr : Y ⟶ X ⨿ Y) ≫ (coprodIso X Y).hom = coprod.inr :=
  map_inr_inv_coprodComparison down (A := X) (B := Y)

@[reassoc] private theorem coprodIso_inv_inl (X Y : L) :
    coprod.inl ≫ (coprodIso X Y).inv = (down).map (coprod.inl : X ⟶ X ⨿ Y) :=
  inl_coprodComparison down X Y

@[reassoc] private theorem coprodIso_inv_inr (X Y : L) :
    coprod.inr ≫ (coprodIso X Y).inv = (down).map (coprod.inr : Y ⟶ X ⨿ Y) :=
  inr_coprodComparison down X Y

@[reassoc] theorem coprodIso_desc {X Y Z : L} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (down).map (coprod.desc f g) = (coprodIso X Y).hom ≫ coprod.desc ((down).map f) ((down).map g) := by
  apply (cancel_epi (coprodIso X Y).inv).mp
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply coprod.hom_ext
  · rw [coprodIso_inv_inl_assoc, ← Functor.map_comp, coprod.inl_desc, coprod.inl_desc]
  · rw [coprodIso_inv_inr_assoc, ← Functor.map_comp, coprod.inr_desc, coprod.inr_desc]

@[reassoc] theorem coprodIso_map {X Y Z W : L} (f : X ⟶ Z) (g : Y ⟶ W) :
    (down).map (coprod.map f g) ≫ (coprodIso Z W).hom =
      (coprodIso X Y).hom ≫ coprod.map ((down).map f) ((down).map g) := by
  apply (cancel_epi (coprodIso X Y).inv).mp
  rw [← Category.assoc (coprodIso X Y).inv (coprodIso X Y).hom, Iso.inv_hom_id, Category.id_comp]
  apply coprod.hom_ext
  · rw [coprodIso_inv_inl_assoc, ← Functor.map_comp_assoc, coprod.inl_map, Functor.map_comp,
      Category.assoc, coprodIso_inl, coprod.inl_map]
  · rw [coprodIso_inv_inr_assoc, ← Functor.map_comp_assoc, coprod.inr_map, Functor.map_comp,
      Category.assoc, coprodIso_inr, coprod.inr_map]

end Coproducts

attribute [local instance] liftedCartesian liftedValueSymmetric liftedPremonoidal
  liftedSymmetric liftedCoproducts

section Iteration

variable [HasFiniteCoproducts K] [Iteration K]

noncomputable local instance liftedIteration : Iteration L where
  iterate {X Y} f := CategoryTheory.iterate (C := K) ((down).map f ≫ (coprodIso Y X).hom)

theorem iterate_map {X Y : L} (f : X ⟶ Y ⨿ X) :
    (down).map (CategoryTheory.iterate f) =
      CategoryTheory.iterate ((down).map f ≫ (coprodIso Y X).hom) := rfl

variable [ElgotCategory K]

local instance liftedElgot : ElgotCategory L where
  fixpoint {X Y} f := by
    apply (down).map_injective
    rw [Functor.map_comp, coprodIso_desc, (down).map_id, iterate_map, ← Category.assoc,
      ← ElgotCategory.fixpoint]
  naturality {X Y Z} f g := by
    apply (down).map_injective
    rw [(down).map_comp, iterate_map, ElgotCategory.naturality, iterate_map,
      (down).map_comp_assoc, coprodIso_map, (down).map_id, Category.assoc]
  codiagonal {X Y} f := by
    apply (down).map_injective
    let c := coprodIso Y X
    let b := (down).map f ≫ (coprodIso (Y ⨿ X) X).hom
    let unfolded := b ≫ coprod.map c.hom (𝟙 ((down).obj X))
    have body : (down).map (CategoryTheory.iterate f) ≫ c.hom = CategoryTheory.iterate unfolded := by
      rw [iterate_map, ElgotCategory.naturality]
    have fold : (down).map (coprod.desc (𝟙 (Y ⨿ X)) (coprod.inr : X ⟶ Y ⨿ X)) ≫ c.hom =
        (coprodIso (Y ⨿ X) X).hom ≫ coprod.map c.hom (𝟙 ((down).obj X)) ≫
          coprod.desc (𝟙 ((down).obj Y ⨿ (down).obj X)) (coprod.inr : (down).obj X ⟶ (down).obj Y ⨿ (down).obj X) := by
      rw [coprodIso_desc, Category.assoc, coprod.desc_comp, coprod.map_desc]
      simp only [(down).map_id, Category.id_comp, Category.comp_id, c, coprodIso_inr]
    rw [iterate_map, body, ElgotCategory.codiagonal, iterate_map, Functor.map_comp,
      Category.assoc ((down).map f), fold]
    congr 1
    simp only [unfolded, b, Category.assoc]

end Iteration

section Distributor

variable [HasFiniteCoproducts K] [MonoidalCategoryStruct K]

theorem leftHom_map
    (comp : ∀ (X : K) {Y Z W : K} (f : Y ⟶ Z) (g : Z ⟶ W), X ◁ (f ≫ g) = X ◁ f ≫ X ◁ g)
    (X Y Z : L) :
    (down).map (DistributiveTensor.leftHom X Y Z) ≫ (X.down ◁ (coprodIso Y Z).hom) =
      (coprodIso (X ⊗ Y) (X ⊗ Z)).hom ≫ DistributiveTensor.leftHom X.down Y.down Z.down := by
  have mapWhisker {A B : L} (f : A ⟶ B) : (down).map (X ◁ f) = X.down ◁ (down).map f := rfl
  have inl : (X.down ◁ (down).map (coprod.inl : Y ⟶ Y ⨿ Z)) ≫ X.down ◁ (coprodIso Y Z).hom =
      X.down ◁ (coprod.inl : (down).obj Y ⟶ (down).obj Y ⨿ (down).obj Z) := by
    rw [← comp, coprodIso_inl]
  have inr : (X.down ◁ (down).map (coprod.inr : Z ⟶ Y ⨿ Z)) ≫ X.down ◁ (coprodIso Y Z).hom =
      X.down ◁ (coprod.inr : (down).obj Z ⟶ (down).obj Y ⨿ (down).obj Z) := by
    rw [← comp, coprodIso_inr]
  simp only [DistributiveTensor.leftHom, coprodIso_desc_assoc, coprod.desc_comp, mapWhisker, inl, inr]
  rfl

theorem liftDistributive [DistributiveTensor K]
    (ident : ∀ X Y : K, X ◁ 𝟙 Y = 𝟙 (X ⊗ Y))
    (comp : ∀ (X : K) {Y Z W : K} (f : Y ⟶ Z) (g : Z ⟶ W), X ◁ (f ≫ g) = X ◁ f ≫ X ◁ g) :
    DistributiveTensor L where
  left_isIso X Y Z := by
    let F : K ⥤ K := {
      obj B := X.down ⊗ B
      map f := X.down ◁ f
      map_id := ident X.down
      map_comp := comp X.down
    }
    have : IsIso (X.down ◁ (coprodIso Y Z).hom) :=
      (F.mapIso (coprodIso Y Z)).isIso_hom
    have : IsIso ((down).map (DistributiveTensor.leftHom X Y Z) ≫ X.down ◁ (coprodIso Y Z).hom) := by
      rw [leftHom_map comp]
      infer_instance
    have : IsIso ((down).map (DistributiveTensor.leftHom X Y Z)) := IsIso.of_isIso_comp_right _ (X.down ◁ (coprodIso Y Z).hom)
    exact isIso_of_reflects_iso _ down

end Distributor

theorem leftIsoInv_map [HasFiniteCoproducts K] [MonoidalCategoryStruct K] [DistributiveTensor K]
    [DistributiveTensor L]
    (comp : ∀ (X : K) {Y Z W : K} (f : Y ⟶ Z) (g : Z ⟶ W), X ◁ (f ≫ g) = X ◁ f ≫ X ◁ g)
    (X Y Z : L) :
    ((down).obj X ◁ (coprodIso Y Z).hom) ≫
      (DistributiveTensor.leftIso ((down).obj X) ((down).obj Y) ((down).obj Z)).inv =
      (down).map ((DistributiveTensor.leftIso X Y Z).inv) ≫ (coprodIso (X ⊗ Y) (X ⊗ Z)).hom := by
  have : IsIso ((down).map (DistributiveTensor.leftHom X Y Z)) :=
    ((down).mapIso (DistributiveTensor.leftIso X Y Z)).isIso_hom
  apply (cancel_epi ((down).map (DistributiveTensor.leftHom X Y Z))).mp
  have hl : DistributiveTensor.leftHom X Y Z ≫ (DistributiveTensor.leftIso X Y Z).inv = 𝟙 _ :=
    (DistributiveTensor.leftIso X Y Z).hom_inv_id
  have hr : DistributiveTensor.leftHom ((down).obj X) ((down).obj Y) ((down).obj Z) ≫
      (DistributiveTensor.leftIso ((down).obj X) ((down).obj Y) ((down).obj Z)).inv = 𝟙 _ :=
    (DistributiveTensor.leftIso _ _ _).hom_inv_id
  have comparison :
      (down).map (DistributiveTensor.leftHom X Y Z) ≫ ((down).obj X ◁ (coprodIso Y Z).hom) =
        (coprodIso (X ⊗ Y) (X ⊗ Z)).hom ≫
          DistributiveTensor.leftHom ((down).obj X) ((down).obj Y) ((down).obj Z) :=
    leftHom_map comp X Y Z
  rw [← Category.assoc, comparison, Category.assoc, hr,
    ← (down).map_comp_assoc, hl, (down).map_id, Category.id_comp]
  exact Category.comp_id _


section
variable [HasFiniteCoproducts K] [MonoidalCategory K] [DistributiveTensor K]

local instance liftedMonoidalDistributive : DistributiveTensor L :=
  liftDistributive MonoidalCategory.whiskerLeft_id MonoidalCategory.whiskerLeft_comp

end

section
variable [HasFiniteCoproducts K] [PremonoidalCategory K] [DistributivePremonoidalCategory K]

local instance liftedPremonoidalDistributive : DistributivePremonoidalCategory L :=
  letI : DistributiveTensor L := liftDistributive PremonoidalCategory.whiskerLeft_id
    PremonoidalCategory.whiskerLeft_comp
  inferInstance

theorem leftInv_map (X Y Z : L) :
    ((down).obj X ◁ (coprodIso Y Z).hom) ≫
      DistributivePremonoidalCategory.leftInv ((down).obj X) ((down).obj Y) ((down).obj Z) =
      (down).map (DistributivePremonoidalCategory.leftInv X Y Z) ≫ (coprodIso (X ⊗ Y) (X ⊗ Z)).hom :=
  leftIsoInv_map PremonoidalCategory.whiskerLeft_comp X Y Z

end

attribute [local instance] liftedIteration liftedElgot liftedMonoidalDistributive liftedPremonoidalDistributive

section Freyd

variable {V : Type u} {C : Type u} [Category.{v} V] [Category.{v} C]

local notation "CUp" => (CategoryTheory.ULift.upFunctor : C ⥤ Obj C)
local notation "VDown" => (CategoryTheory.ULift.downFunctor : Obj V ⥤ V)
local notation "CDown" => (CategoryTheory.ULift.downFunctor : Obj C ⥤ C)

def liftFunctor (J : V ⥤ C) : Obj V ⥤ Obj C :=
  VDown ⋙ J ⋙ CUp

variable [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : V ⥤ C)

section
variable [FreydCategory J]

open Functor.StrongPremonoidal in
noncomputable local instance liftedFreyd : FreydCategory (liftFunctor J) where
  unitIso := liftIso (unitIso (J := J))
  tensorIso X Y := liftIso (tensorIso X.down Y.down)
  tensor_naturality_left f Z := tensor_naturality_left (J := J) f Z.down
  tensor_naturality_right X {_ _} f := tensor_naturality_right (J := J) X.down f
  associativity X Y Z := associativity (J := J) X.down Y.down Z.down
  left_unitality X := left_unitality (J := J) X.down
  right_unitality X := right_unitality (J := J) X.down
  map_central f := liftCentral (map_central (J := J) f)
  braiding X Y := Functor.StrongSymmetricPremonoidal.braiding (J := J) X.down Y.down
  obj_bijective := ⟨
    fun _ _ h => ULift.ext ((FreydCategory.obj_bijective (J := J)).1 (congrArg ULift.down h)),
    fun Y => let ⟨X, h⟩ := (FreydCategory.obj_bijective (J := J)).2 Y.down
      ⟨⟨X⟩, ULift.ext h⟩⟩

local instance liftedCentralUnit [FreydCategory.CentralUnit J] :
    FreydCategory.CentralUnit (liftFunctor J) where
  unit_central := liftCentral (FreydCategory.CentralUnit.unit_central (J := J))

end

attribute [local instance] liftedFreyd liftedCentralUnit

variable [HasFiniteCoproducts V] [DistributiveTensor V]
  [HasFiniteCoproducts C] [DistributivePremonoidalCategory C]

section
variable [DistributiveFreydCategory J]

noncomputable local instance liftedDistributiveFreyd : DistributiveFreydCategory (liftFunctor J) where
  toFreydCategory := liftedFreyd J
  preservesFiniteCoproducts := by
    have : PreservesFiniteCoproducts (liftFunctor J ⋙ CDown) := by
      change PreservesFiniteCoproducts (VDown ⋙ J)
      infer_instance
    exact preservesFiniteCoproducts_of_reflects_of_preserves _ CDown

end

attribute [local instance] liftedDistributiveFreyd

variable [Iteration C] [ElgotCategory C] [strong : StrongElgotFreydCategory J]

private theorem inputUniformity {A D : Obj V} {B : Obj C}
    (f : (liftFunctor J).obj A ⟶ B ⨿ (liftFunctor J).obj A)
    (g : (liftFunctor J).obj D ⟶ B ⨿ (liftFunctor J).obj D) (h : A ⟶ D)
    (comm : f ≫ coprod.map (𝟙 B) ((liftFunctor J).map h) = (liftFunctor J).map h ≫ g) :
    CategoryTheory.iterate f = (liftFunctor J).map h ≫ CategoryTheory.iterate g := by
  apply (CDown).map_injective
  rw [iterate_map, (CDown).map_comp, iterate_map]
  refine ElgotFreydCategory.pure_uniformity J _ _ ((VDown).map h) ?_
  have eq := congrArg (fun k => (CDown).map k ≫ (coprodIso B ((liftFunctor J).obj D)).hom) comm
  simp only [(CDown).map_comp_assoc, coprodIso_map, (CDown).map_id] at eq
  rw [Category.assoc]
  exact eq

include strong in
private theorem liftStrength {X Y : Obj C} (Z : Obj C) (f : X ⟶ Y ⨿ X) :
    CategoryTheory.iterate ((Z ◁ f) ≫ DistributivePremonoidalCategory.leftInv Z Y X) =
      Z ◁ CategoryTheory.iterate f := by
  have wmap {B D : Obj C} (g : B ⟶ D) :
      (CDown).map (Z ◁ g) = (CDown).obj Z ◁ (CDown).map g := rfl
  apply (CDown).map_injective
  rw [iterate_map, (CDown).map_comp_assoc, ← leftInv_map, wmap, wmap, iterate_map,
    ← PremonoidalCategory.whiskerLeft_comp_assoc, StrongElgotFreydCategory.strength J]

noncomputable local instance liftedStrong : StrongElgotFreydCategory (liftFunctor J) where
  toDistributiveFreydCategory := liftedDistributiveFreyd J
  uniformity := inputUniformity J
  iterate_whiskerLeft := liftStrength J

end Freyd

attribute [local instance] liftedStrong

section Environments
open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.Semantics.Categorical
open CartesianMonoidalCategory

variable {τ V : Type u} [TypeFormers τ] [Category.{v} V] [CartesianMonoidalCategory V]
  [HasFiniteCoproducts V] (M : TypeModel τ V)

local notation "VDown" => (CategoryTheory.ULift.downFunctor : Obj V ⥤ V)

@[instance_reducible]
noncomputable def liftTypeModel : TypeModel τ (Obj V) where
  obj A := ⟨M.obj A⟩
  productIso A B := liftIso (M.productIso A B)
  unitIso := liftIso M.unitIso
  coprodIso A B :=
    liftIso ((M.coprodIso A B).trans (LocallySmallValidityProofs.coprodIso ⟨M.obj A⟩ ⟨M.obj B⟩).symm)
  emptyIsInitial := IsInitial.isInitialOfObj VDown ⟨M.obj (empty : τ)⟩ M.emptyIsInitial

local notation "ML" => liftTypeModel M

private theorem downCtx (Γ : Ctx Empty τ) :
    (VDown).obj (ctxObj (ML) Γ) = ctxObj M Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ x A ih => exact congrArg (fun R => R ⊗ M.obj A) ih

private theorem downBound {n : Nat} (β : BoundCtx τ n) :
    (VDown).obj (boundObj (ML) β) = boundObj M β := by
  induction β with
  | nil => rfl
  | snoc β A ih => exact congrArg (fun R => R ⊗ M.obj A) ih

private noncomputable def cmpEnv (Γ : Ctx Empty τ) {n : Nat} (β : BoundCtx τ n) :
    (VDown).obj (envObj (ML) Γ β) ⟶ envObj M Γ β :=
  eqToHom (congrArg₂ (fun R S : V => R ⊗ S) (downCtx M Γ) (downBound M β))

private theorem cmpBoundVar (Γ : Ctx Empty τ) {n : Nat} (β : BoundCtx τ n) (i : Fin n) :
    (VDown).map (boundVar (ML) (Γ := Γ) (β := β) i) =
      cmpEnv M Γ β ≫ boundVar M i := by
  have lookup : ∀ {k : Nat} (δ : BoundCtx τ k) (j : Fin k),
      (VDown).map (boundLookup (ML) (β := δ) j) =
        eqToHom (downBound M δ) ≫ boundLookup M j := by
    intro k δ
    induction δ with
    | nil => exact fun j => j.elim0
    | snoc δ A ih =>
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · have natural {X Y : V} (h : X = Y) :
            snd X (M.obj A) = eqToHom (congrArg (fun R => R ⊗ M.obj A) h) ≫ snd Y (M.obj A) := by
          cases h
          simp
        exact natural (downBound M δ)
      · have natural {X Y : V} (h : X = Y) :
            fst X (M.obj A) ≫ eqToHom h =
              eqToHom (congrArg (fun R => R ⊗ M.obj A) h) ≫ fst Y (M.obj A) := by
          cases h
          simp
        rw [boundLookup, boundLookup, Fin.cases_succ, Fin.cases_succ, (VDown).map_comp, ih j]
        -- Select the same older bound component after the environment transport.
        erw [← Category.assoc, natural (downBound M δ), Category.assoc]
  have projection {R S T U : V} (hr : R = T) (hs : S = U) :
      snd R S ≫ eqToHom hs = eqToHom (congrArg₂ (fun X Y : V => X ⊗ Y) hr hs) ≫ snd T U := by
    cases hr
    cases hs
    simp
  simp only [boundVar, (VDown).map_comp, lookup, cmpEnv, ← Category.assoc]
  erw [projection (downCtx M Γ) (downBound M β)]

private theorem cmpSnoc (Γ : Ctx Empty τ) {n : Nat} (β : BoundCtx τ n) (A : τ) :
    (VDown).map (envSnocIso (ML) Γ β A).hom ≫ cmpEnv M Γ (.snoc β A) =
      (cmpEnv M Γ β ▷ M.obj A) ≫ (envSnocIso M Γ β A).hom := by
  have transport {R S R' S' : V} (hR : R = R') (hS : S = S') (X : V) :
      (α_ R S X).hom ≫ eqToHom (congrArg₂ (fun T U : V => T ⊗ U)
        hR (congrArg (fun T => T ⊗ X) hS)) =
      (eqToHom (congrArg₂ (fun T U : V => T ⊗ U) hR hS) ▷ X) ≫ (α_ R' S' X).hom := by
    cases hR
    cases hS
    simp
  exact transport (downCtx M Γ) (downBound M β) (M.obj A)

private theorem cmpPair (Γ : Ctx Empty τ) {n : Nat} (β : BoundCtx τ n) (A B : τ) :
    (VDown).map (envPairHom (ML) Γ β A B) ≫ cmpEnv M Γ (.snoc (.snoc β A) B) =
      (cmpEnv M Γ β ▷ (M.obj A ⊗ M.obj B)) ≫ envPairHom M Γ β A B := by
  have transport {R S R' S' : V} (hR : R = R') (hS : S = S') (X Y : V) :
      ((α_ R S (X ⊗ Y)).hom ≫ R ◁ (α_ S X Y).inv) ≫
          eqToHom (congrArg₂ (fun T U : V => T ⊗ U) hR (congrArg (fun T => (T ⊗ X) ⊗ Y) hS)) =
        (eqToHom (congrArg₂ (fun T U : V => T ⊗ U) hR hS) ▷ (X ⊗ Y)) ≫
          (α_ R' S' (X ⊗ Y)).hom ≫ R' ◁ (α_ S' X Y).inv := by
    cases hR
    cases hS
    simp
  exact transport (downCtx M Γ) (downBound M β) (M.obj A) (M.obj B)

end Environments

section Denotation
open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.Semantics.Categorical
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (duplicate bind pair retainLeft splitMapCoprod caseWithContext contextualLoop)
open CartesianMonoidalCategory

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
local notation "pairArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair

variable {V : Type u} {C : Type u} [Category.{v} V] [Category.{v} C]

local notation "VDown" => (CategoryTheory.ULift.downFunctor : Obj V ⥤ V)
local notation "CDown" => (CategoryTheory.ULift.downFunctor : Obj C ⥤ C)

theorem liftValueMap (J : V ⥤ C) {X Y : Obj V} (f : X ⟶ Y) :
    (CDown).map ((liftFunctor J).map f) = J.map ((VDown).map f) := rfl

private theorem liftValuePair [CartesianMonoidalCategory V] {R A B : Obj V} (f : R ⟶ A) (g : R ⟶ B) :
    (VDown).map (CartesianMonoidalCategory.lift f g) =
      CartesianMonoidalCategory.lift ((VDown).map f) ((VDown).map g) := by
  apply CartesianMonoidalCategory.hom_ext
  · have h := congrArg (VDown).map (lift_fst f g)
    rw [(VDown).map_comp] at h
    exact h.trans (CartesianMonoidalCategory.lift_fst ((VDown).map f) ((VDown).map g)).symm
  · have h := congrArg (VDown).map (lift_snd f g)
    rw [(VDown).map_comp] at h
    exact h.trans (CartesianMonoidalCategory.lift_snd ((VDown).map f) ((VDown).map g)).symm

variable [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [DistributiveTensor V]
  [HasFiniteCoproducts C] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]

local notation "LJ" => liftFunctor J

private theorem mapRetain {R A B : Obj V} (f : (LJ).obj A ⟶ (LJ).obj B) :
    (CDown).map (retainLeft (LJ) (R := R) f) =
      retainLeft J (R := (VDown).obj R) ((CDown).map f) := rfl

private theorem mapBind {R A B : Obj V} (f : (LJ).obj R ⟶ (LJ).obj A)
    (g : (LJ).obj (R ⊗ A) ⟶ (LJ).obj B) :
    (CDown).map (bindArrow (LJ) f g) = bindArrow J ((CDown).map f) ((CDown).map g) := by
  unfold Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.extend duplicate
  simp only [Functor.map_comp, liftValueMap, liftValuePair]
  rfl

private theorem mapPair {R A B : Obj V} (f : (LJ).obj R ⟶ (LJ).obj A) (g : (LJ).obj R ⟶ (LJ).obj B) :
    (CDown).map (pairArrow (LJ) f g) = pairArrow J ((CDown).map f) ((CDown).map g) := by
  unfold Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.retainedContext
  simp only [mapBind, Functor.map_comp, liftValueMap, liftValuePair]
  rfl

private theorem mapSplit (A B : Obj V) :
    (CDown).map (splitMapCoprod (LJ) A B) ≫ (coprodIso ((LJ).obj A) ((LJ).obj B)).hom =
      J.map (coprodIso A B).hom ≫ splitMapCoprod J ((VDown).obj A) ((VDown).obj B) := by
  let v := coprodIso A B
  let c := coprodIso ((LJ).obj A) ((LJ).obj B)
  let cp := Limits.coprodComparison J ((VDown).obj A) ((VDown).obj B)
  let lp := Limits.coprodComparison (LJ) A B
  have isoComparison : c.inv ≫ (CDown).map lp = cp ≫ J.map v.inv := by
    apply coprod.hom_ext
    · dsimp only [c]
      erw [coprodIso_inv_inl_assoc, ← (CDown).map_comp]
      refine (congrArg (CDown).map (inl_coprodComparison (LJ) A B)).trans ?_
      change J.map ((VDown).map (coprod.inl : A ⟶ A ⨿ B)) =
        (coprod.inl : J.obj ((VDown).obj A) ⟶ J.obj ((VDown).obj A) ⨿ J.obj ((VDown).obj B)) ≫
          cp ≫ J.map v.inv
      erw [inl_coprodComparison_assoc J, ← J.map_comp]
      exact congrArg J.map (coprodIso_inv_inl A B).symm
    · dsimp only [c]
      erw [coprodIso_inv_inr_assoc, ← (CDown).map_comp]
      refine (congrArg (CDown).map (inr_coprodComparison (LJ) A B)).trans ?_
      change J.map ((VDown).map (coprod.inr : B ⟶ A ⨿ B)) =
        (coprod.inr : J.obj ((VDown).obj B) ⟶ J.obj ((VDown).obj A) ⨿ J.obj ((VDown).obj B)) ≫
          cp ≫ J.map v.inv
      erw [inr_coprodComparison_assoc J, ← J.map_comp]
      exact congrArg J.map (coprodIso_inv_inr A B).symm
  change (CDown).map (inv lp) ≫ c.hom = J.map v.hom ≫ inv cp
  apply (cancel_mono cp).mp
  have compare : c.hom ≫ cp = (CDown).map lp ≫ J.map v.hom := by
    apply (cancel_epi c.inv).mp
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      ← Category.assoc, isoComparison, Category.assoc, ← J.map_comp, Iso.inv_hom_id, J.map_id,
      Category.comp_id]
  have inverse : (CDown).map (inv lp) ≫ (CDown).map lp = 𝟙 ((CDown).obj ((LJ).obj (A ⨿ B))) := by
    rw [← (CDown).map_comp, IsIso.inv_hom_id, (CDown).map_id]
  erw [Category.assoc (J.map v.hom), IsIso.inv_hom_id, Category.comp_id,
    Category.assoc ((CDown).map (inv lp)), compare,
    ← Category.assoc ((CDown).map (inv lp)), inverse, Category.id_comp]

@[reassoc] private theorem mapRoute (R A B : Obj V) :
    (CDown).map ((LJ).map (DistributiveTensor.leftIso R A B).inv) ≫
      (CDown).map (splitMapCoprod (LJ) (R ⊗ A) (R ⊗ B)) ≫
        (coprodIso ((LJ).obj (R ⊗ A)) ((LJ).obj (R ⊗ B))).hom =
    J.map ((VDown).obj R ◁ (coprodIso A B).hom) ≫
      J.map (DistributiveTensor.leftIso ((VDown).obj R) ((VDown).obj A) ((VDown).obj B)).inv ≫
        splitMapCoprod J ((VDown).obj R ⊗ (VDown).obj A) ((VDown).obj R ⊗ (VDown).obj B) := by
  rw [liftValueMap, mapSplit]
  erw [← J.map_comp_assoc, ← J.map_comp_assoc, leftIsoInv_map MonoidalCategory.whiskerLeft_comp]
  rfl

private theorem mapCase {R A B D : Obj V}
    (f : (LJ).obj R ⟶ (LJ).obj (A ⨿ B))
    (l : (LJ).obj (R ⊗ A) ⟶ (LJ).obj D)
    (r : (LJ).obj (R ⊗ B) ⟶ (LJ).obj D) :
    (CDown).map (caseWithContext (LJ) f l r) =
    caseWithContext J ((CDown).map f ≫ J.map (coprodIso A B).hom) ((CDown).map l) ((CDown).map r) := by
  unfold caseWithContext
  rw [mapBind]
  simp only [(CDown).map_comp, coprodIso_desc]
  erw [mapRoute_assoc J R A B]
  unfold Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
  rw [extend_postmap]
  simp only [Category.assoc]
  rfl

private theorem retainLeft_post_value {R X Y Z : V} (f : J.obj X ⟶ J.obj Y)
    (p : Y ⟶ Z) :
    retainLeft J (R := R) (f ≫ J.map p) = retainLeft J f ≫ J.map (R ◁ p) := by
  unfold retainLeft
  simp only [PremonoidalCategory.leftTensor, PremonoidalCategory.id_whiskerRight, Category.id_comp,
    PremonoidalCategory.whiskerLeft_comp, Category.assoc,
    Functor.StrongPremonoidal.tensor_naturality_right]

private theorem mapLoop {R A B : Obj V} (f : (LJ).obj (R ⊗ A) ⟶ (LJ).obj (B ⨿ A)) :
    (CDown).map (contextualLoop (LJ) (R := R) f) =
      contextualLoop J (R := (VDown).obj R) ((CDown).map f ≫ J.map (coprodIso B A).hom) := by
  unfold contextualLoop
  rw [(CDown).map_comp, iterate_map]
  simp only [(CDown).map_comp, Category.assoc, mapRetain]
  erw [mapRoute J R B A]
  rw [retainLeft_post_value J]
  simp only [liftValueMap, liftValuePair, (VDown).map_id, Category.assoc]
  rfl

variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ] (M : TypeModel τ V)
  [InstructionModel J M Φ]

local notation "ML" => liftTypeModel M

noncomputable local instance liftInstructions : InstructionModel (LJ) (ML) Φ where
  denote f := InstructionModel.denote (J := J) (M := M) f

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem mapTypeCoprod (A B : τ) :
    (VDown).map ((ML).coprodIso A B).hom ≫ (coprodIso ((ML).obj A) ((ML).obj B)).hom =
      (M.coprodIso A B).hom := by
  change ((M.coprodIso A B).hom ≫ (coprodIso ((ML).obj A) ((ML).obj B)).inv) ≫ _ = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem mapTypeInl (A B : τ) :
    (VDown).map (coprod.inl ≫ ((ML).coprodIso A B).inv) =
      (coprod.inl : M.obj A ⟶ M.obj A ⨿ M.obj B) ≫ (M.coprodIso A B).inv := by
  rw [(VDown).map_comp]
  change (VDown).map (coprod.inl : (ML).obj A ⟶ (ML).obj A ⨿ (ML).obj B) ≫
    (coprodIso ((ML).obj A) ((ML).obj B)).hom ≫ (M.coprodIso A B).inv = _
  rw [coprodIso_inl_assoc]
  rfl

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem mapTypeInr (A B : τ) :
    (VDown).map (coprod.inr ≫ ((ML).coprodIso A B).inv) =
      (coprod.inr : M.obj B ⟶ M.obj A ⨿ M.obj B) ≫ (M.coprodIso A B).inv := by
  rw [(VDown).map_comp]
  change (VDown).map (coprod.inr : (ML).obj B ⟶ (ML).obj A ⨿ (ML).obj B) ≫
    (coprodIso ((ML).obj A) ((ML).obj B)).hom ≫ (M.coprodIso A B).inv = _
  rw [coprodIso_inr_assoc]
  rfl

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem mapEmpty (A : τ) :
    (VDown).map ((ML).emptyIsInitial.to ((ML).obj A)) = M.emptyIsInitial.to (M.obj A) :=
  M.emptyIsInitial.hom_ext _ _

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem mapUnit {Γ : Ctx Empty τ} {n : Nat} (β : BoundCtx τ n) :
    (VDown).map (toUnit (envObj (ML) Γ β) ≫ (ML).unitIso.inv) =
      cmpEnv M Γ β ≫ toUnit (envObj M Γ β) ≫ M.unitIso.inv := by
  rw [(VDown).map_comp, ← Category.assoc]
  exact congrArg (fun f => f ≫ M.unitIso.inv) (isTerminalTensorUnit.hom_ext _ _)

theorem denoteDown {Γ : Ctx Empty τ} {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) :
    (CDown).map (denote (LJ) (ML) d) =
      J.map (cmpEnv M Γ β) ≫ denote J M d := by
  induction d with
  | @fv _ _ x _ _ => exact x.elim
  | bv =>
    simp only [denote, liftValueMap, cmpBoundVar, J.map_comp]
  | unit =>
    simp only [denote, liftValueMap, mapUnit, J.map_comp]
  | op _ ih =>
    simp only [denote, (CDown).map_comp, ih, Category.assoc]
    rfl
  | @inl n β a A B _ ih =>
    simp only [denote, (CDown).map_comp, ih, liftValueMap, mapTypeInl, Category.assoc]
  | @inr n β b A B _ ih =>
    simp only [denote, (CDown).map_comp, ih, liftValueMap, mapTypeInr, Category.assoc]
  | abort _ ih =>
    simp only [denote, (CDown).map_comp, ih, liftValueMap, mapEmpty, Category.assoc]
  | pair _ _ ih₁ ih₂ =>
    simp only [denote, (CDown).map_comp, mapPair, ih₁, ih₂, liftValueMap, pair_pre_map, Category.assoc]
    rfl
  | let₁ _ _ ih₁ ih₂ =>
    simp only [denote, mapBind, (CDown).map_comp, ih₁, ih₂, liftValueMap]
    erw [← J.map_comp_assoc, cmpSnoc, J.map_comp_assoc, bind_pre_map]
  | @let₂ _ β _ _ A B _ _ _ ih₁ ih₂ =>
    simp only [denote, mapBind, (CDown).map_comp, ih₁, ih₂, liftValueMap, MonoidalCategory.id_tensorHom]
    have exchange : ((VDown).obj (envObj (ML) Γ β) ◁ (M.productIso A B).hom) ≫
        (cmpEnv M Γ β ▷ (M.obj A ⊗ M.obj B)) =
      (cmpEnv M Γ β ▷ M.obj (product A B)) ≫ (envObj M Γ β ◁ (M.productIso A B).hom) :=
      MonoidalCategory.whisker_exchange _ _
    erw [← J.map_comp_assoc ((VDown).map (envPairHom (ML) Γ β A B)), cmpPair,
      J.map_comp_assoc, ← J.map_comp_assoc, exchange, J.map_comp_assoc, bind_pre_map]
  | @case _ β _ _ _ A B _ _ _ _ ih₁ ih₂ ih₃ =>
    simp only [denote, mapCase, (CDown).map_comp, ih₁, ih₂, ih₃, liftValueMap, Category.assoc]
    erw [← J.map_comp ((VDown).map (((ML).coprodIso A B).hom)), mapTypeCoprod,
      ← J.map_comp_assoc, cmpSnoc, J.map_comp_assoc,
      ← J.map_comp_assoc ((VDown).map (envSnocIso (ML) Γ β B).hom), cmpSnoc, J.map_comp_assoc,
      case_pre_map]
  | @iter _ β _ _ A B _ _ ih₁ ih₂ =>
    simp only [denote, mapBind, mapLoop, (CDown).map_comp, ih₁, ih₂, liftValueMap, Category.assoc]
    erw [← J.map_comp ((VDown).map (((ML).coprodIso B A).hom)), mapTypeCoprod,
      ← J.map_comp_assoc, cmpSnoc, J.map_comp_assoc, contextualLoop_pre_map, bind_pre_map]

theorem denote_eq_iff {Γ : Ctx Empty τ} {n : Nat} {β : BoundCtx τ n}
    {a b : Tm Empty Φ n} {A : τ} (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) :
    denote (LJ) (ML) da = denote (LJ) (ML) db ↔ denote J M da = denote J M db := by
  have : IsIso (cmpEnv M Γ β) := by unfold cmpEnv; infer_instance
  constructor
  · intro eq
    apply (cancel_epi (J.map (cmpEnv M Γ β))).mp
    rw [← denoteDown J M da, ← denoteDown J M db, eq]
  · intro eq
    apply (CDown).map_injective
    rw [denoteDown J M da, denoteDown J M db, eq]

end Denotation

section Admission

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.Semantics.Categorical
open Silmaril.Isotope.LetIter.LocallyNameless (AbortEquiv Derivation Tm)

variable {V C : Type} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C] [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [Iteration C]
  [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]

private theorem liftIso_eqToIso {K₀ : Type} [Category.{0} K₀] {X Y : K₀} (h : X = Y) :
    liftIso (X := (⟨X⟩ : Obj K₀)) (Y := ⟨Y⟩) (eqToIso h) =
      eqToIso (congrArg (ULift.up : K₀ → Obj K₀) h) := by cases h; rfl

theorem liftSharedTensor
    (h : ∀ R S : V, ∃ e : J.obj R ⊗ J.obj S = J.obj (R ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) R S = eqToIso e)
    (R S : Obj V) :
    ∃ e : (liftFunctor J).obj R ⊗ (liftFunctor J).obj S = (liftFunctor J).obj (R ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := liftFunctor J) R S = eqToIso e := by
  obtain ⟨e, he⟩ := h R.down S.down
  refine ⟨congrArg (ULift.up : C → Obj C) e, ?_⟩
  change liftIso (Functor.StrongPremonoidal.tensorIso (J := J) R.down S.down) = _
  rw [he]
  exact liftIso_eqToIso e

attribute [local instance] liftInstructions

variable {τ Φ ε : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] (M : TypeModel τ V)
  [InstructionModel J M Φ]

theorem liftCoherence (h : TypingCoherent (ν := Empty) J M Φ) :
    TypingCoherent (ν := Empty) (liftFunctor J) (liftTypeModel M) Φ :=
  fun d e => (denote_eq_iff J M d e).mpr (h d e)

omit [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] in
theorem liftPure (pe : ε)
    (h : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    (f : Φ) (hf : IsPure pe f) :
    ∃ p : (liftTypeModel M).obj (instrSrc f) ⟶ (liftTypeModel M).obj (instrTrg f),
      InstructionModel.denote (J := liftFunctor J) (M := liftTypeModel M) f = (liftFunctor J).map p := by
  rcases h f hf with ⟨p, hp⟩
  exact ⟨p, hp⟩

end Admission

section Repaired
open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
open Silmaril.Isotope.LetIter.LocallyNameless (AbortEquiv Derivation Tm)

variable {τ Φ ε : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] (pe : ε)
  {n : Nat} {β : BoundCtx τ n} {a b : Tm Empty Φ n} {A : τ}
  (da : Derivation Φ (Ctx.nil : Ctx Empty τ) β a A)
  (db : Derivation Φ (Ctx.nil : Ctx Empty τ) β b A)

attribute [local instance] liftInstructions

public theorem abortEquiv_iff_repairedLocallySmallValidity :
    AbortEquiv pe (Ctx.nil : Ctx Empty τ) β a b A ↔ RepairedLocallySmallValidity pe da db := by
  constructor
  · intro h V C hv hc cart symV pre symC fcV fcC distV distC iter elgot J strong unit M instr coh shared pure
    exact denote_abortEquiv_of_coherent_shared_tensor J M coh shared pure h da db
  · intro h
    let := repairedInstructionModel (τ := τ) (Φ := Φ) pe
    let Jq := repairedValues (τ := τ) (Φ := Φ) pe
    let m := typeModel (τ := τ) (Φ := Φ) pe
    have : FreydCategory.CentralUnit Jq := repairedCentralUnit pe
    have : FreydCategory.CentralUnit (liftFunctor Jq) := liftedCentralUnit Jq
    have eq := h (liftFunctor Jq) (liftTypeModel m)
      (liftCoherence Jq m (repairedTypingCoherent_empty pe))
      (liftSharedTensor Jq (repairedValues_sharedTensor pe))
      (liftPure Jq m pe (repairedInstructionModel_pure pe))
    exact (repairedDenoteInSyntax_eq_iff pe da db).mp ((denote_eq_iff Jq m da db).mp eq)

end Repaired

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.LocallySmallValidityProofs
