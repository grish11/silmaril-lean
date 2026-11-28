module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Freyd.Defs
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Chosen.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Distributive.Thms

/-! # Distributive Freyd structure of the structural value inclusion -/

public section

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.Extension.Singleton
open Paper.RetainedCase.Chosen (projectedDistributor_eq_iff)
open Paper.RetainedCase (distributorIso distributorIso_hom)
open StructuralValues (valueCartesian valueBraided computationPremonoidal computationSymmetric)

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralValueFreyd

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  [unitEta : Fact (StructuralValues.IncludesUnitEta Seed)]

local notation "Val" => StructuralValues.ValueCategory Seed
local notation "Comp" => TypeCategory Seed
local notation "Obj" => ofType Seed
local notation "valueObj" => StructuralValues.ofSyntaxType Seed
local notation "inc" => StructuralValues.inclusion Seed
local notation "proj" => projection Seed
local notation "cartPair" => CartesianMonoidalCategory.lift
local notation "Fst" => CartesianMonoidalCategory.fst
local notation "Snd" => CartesianMonoidalCategory.snd
local notation "F" => productFst Seed
local notation "S" => productSnd Seed
local notation "Pa" => pairArrows Seed
local infixr:70 " ×ₜ " => Silmaril.product
local infixr:65 " ⊕ₜ " => Silmaril.coprod

noncomputable local instance : CartesianMonoidalCategory Val := valueCartesian Seed
noncomputable local instance : BraidedCategory Val := valueBraided Seed
local instance : PremonoidalCategory Comp := computationPremonoidal Seed
local instance : SymmetricPremonoidalCategory Comp := computationSymmetric Seed
attribute [local instance] StructuralValues.hasFiniteCoproducts StructuralValues.preservesFiniteCoproducts

open PremonoidalCategory (IsCentral)
open ValueCoproducts (exactCopair)

local notation "H" => StructuralValues.HomProperty Seed
local notation "W" => whiskerLeftFunctor Seed

set_option backward.isDefEq.respectTransparency false in
include unitEta in
theorem iso_inv_mem {A B : Comp} (e : A ≅ B) (h : H e.hom) : H e.inv := by
  have hc : IsCentral e.hom :=
    ⟨fun g => (h.1.1 g).1, fun g => (h.1.1 g).2.symm⟩
  have hi := hc.inv e
  refine ⟨⟨fun g => ⟨hi.1 g, (hi.2 g).symm⟩, ?_⟩, ?_⟩
  · apply (cancel_epi e.hom).mp
    rw [← StructuralValues.pair_comp Seed e.hom e.inv e.inv h.1, Iso.hom_inv_id,
      Iso.hom_inv_id_assoc]
    unfold pairArrows whiskerLeft whiskerRight
    rw [(whiskerRightFunctor Seed A).map_id, (W A).map_id]
    exact (Category.id_comp (𝟙 (tensorObj Seed A A))) ▸ Category.comp_id (diagonalArrow Seed A)
  · apply (cancel_epi e.hom).mp
    rw [e.hom_inv_id_assoc, h.2]

set_option backward.isDefEq.respectTransparency false in
include unitEta in
noncomputable def distributor (X A B : τ) :
    valueObj ((X ×ₜ A) ⊕ₜ (X ×ₜ B)) ≅ valueObj (X ×ₜ (A ⊕ₜ B)) := by
  let e : Obj (X ×ₜ (A ⊕ₜ B)) ≅ Obj ((X ×ₜ A) ⊕ₜ (X ×ₜ B)) :=
    (proj).mapIso (distributorIso X A B)
  let l : Obj (X ×ₜ A) ⟶ Obj (X ×ₜ (A ⊕ₜ B)) := (W (Obj X)).map (sumCofan Seed A B).inl
  let r : Obj (X ×ₜ B) ⟶ Obj (X ×ₜ (A ⊕ₜ B)) := (W (Obj X)).map (sumCofan Seed A B).inr
  have he : e.hom = ofRegion Seed (CfgEta.TypeCategory.Retained.distributorRegion_typed X A B) :=
    congrArg (proj).map (distributorIso_hom X A B)
  have legs := (projectedDistributor_eq_iff Seed X A B _).1 he
  have forward : e.inv = exactCopair Seed l r := by
    let hc := sumCofanIsColimit Seed (X ×ₜ A) (X ×ₜ B)
    apply BinaryCofan.IsColimit.hom_ext hc
    · have hl : (sumCofan Seed (X ×ₜ A) (X ×ₜ B)).inl ≫ exactCopair Seed l r = l :=
        hc.fac (BinaryCofan.mk l r) ⟨WalkingPair.left⟩
      have leg : l ≫ e.hom = (sumCofan Seed (X ×ₜ A) (X ×ₜ B)).inl := legs.1
      rw [hl, ← leg, Category.assoc, e.hom_inv_id]
      exact Category.comp_id l
    · have hr : (sumCofan Seed (X ×ₜ A) (X ×ₜ B)).inr ≫ exactCopair Seed l r = r :=
        hc.fac (BinaryCofan.mk l r) ⟨WalkingPair.right⟩
      have leg : r ≫ e.hom = (sumCofan Seed (X ×ₜ A) (X ×ₜ B)).inr := legs.2
      rw [hr, ← leg, Category.assoc, e.hom_inv_id]
      exact Category.comp_id r
  have hl : H l := by
    let f := (valueObj X) ◁ (StructuralValues.sum Seed A B).inl
    have eq : (inc).map f = l :=
      StructuralValues.map_whiskerLeft Seed unitEta.out X (StructuralValues.sum Seed A B).inl
    rw [← eq]
    exact f.property
  have hr : H r := by
    let f := (valueObj X) ◁ (StructuralValues.sum Seed A B).inr
    have eq : (inc).map f = r :=
      StructuralValues.map_whiskerLeft Seed unitEta.out X (StructuralValues.sum Seed A B).inr
    rw [← eq]
    exact f.property
  have hm : H e.inv := forward ▸ StructuralValues.copair_mem Seed hl hr
  exact WideSubcategory.isoMk e.symm hm (iso_inv_mem Seed e.symm hm)

theorem inclusion_mapIso_distributor (X A B : τ) :
    (inc).mapIso (distributor Seed X A B) = ((proj).mapIso (distributorIso X A B)).symm :=
  Iso.ext rfl

set_option backward.isDefEq.respectTransparency false in
noncomputable def whiskeredSumIsColimit (X A B : τ) :
    IsColimit (BinaryCofan.map (MonoidalCategory.tensorLeft (valueObj X)) (StructuralValues.sum Seed A B)) := by
  apply (StructuralValues.sumIsColimit Seed (X ×ₜ A) (X ×ₜ B)).ofIsoColimit
  let e := distributor Seed X A B
  have hi : (inc).map e.inv = ofRegion Seed (CfgEta.TypeCategory.Retained.distributorRegion_typed X A B) :=
    congrArg (proj).map (distributorIso_hom X A B)
  have legs := (projectedDistributor_eq_iff Seed X A B _).1 rfl
  refine BinaryCofan.ext e ?_ ?_
  · apply (inc).map_injective
    change (sumCofan Seed (X ×ₜ A) (X ×ₜ B)).inl =
      (inc).map ((valueObj X) ◁ (StructuralValues.sum Seed A B).inl) ≫ (inc).map e.inv
    rw [hi, StructuralValues.map_whiskerLeft Seed unitEta.out]
    exact legs.1.symm
  · apply (inc).map_injective
    change (sumCofan Seed (X ×ₜ A) (X ×ₜ B)).inr =
      (inc).map ((valueObj X) ◁ (StructuralValues.sum Seed A B).inr) ≫ (inc).map e.inv
    rw [hi, StructuralValues.map_whiskerLeft Seed unitEta.out]
    exact legs.2.symm

set_option backward.isDefEq.respectTransparency false in
private theorem whiskerPreservesBinary (X : τ) :
    PreservesColimitsOfShape (Discrete WalkingPair) (MonoidalCategory.tensorLeft (valueObj X)) where
  preservesColimit {K} := by
    let A : τ := (K.obj ⟨WalkingPair.left⟩).obj.as
    let B : τ := (K.obj ⟨WalkingPair.right⟩).obj.as
    let L := MonoidalCategory.tensorLeft (valueObj X)
    have : PreservesColimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)) L :=
      preservesColimit_of_preserves_colimit_cocone (StructuralValues.sumIsColimit Seed A B)
        (BinaryCofan.isColimitMapCoconeEquiv.symm (whiskeredSumIsColimit Seed X A B))
    exact preservesColimit_of_iso_diagram L (diagramIsoPair K).symm

theorem valueDistributive : DistributiveTensor Val where
  left_isIso X A B := by
    have : PreservesColimitsOfShape (Discrete WalkingPair) (MonoidalCategory.tensorLeft X) :=
      whiskerPreservesBinary Seed X.obj.as
    change IsIso (coprodComparison (MonoidalCategory.tensorLeft X) A B)
    infer_instance

theorem computationDistributive : DistributivePremonoidalCategory Comp where
  toDistributiveTensor :=
    CoproductDistributivity.distributiveTensor_of_whisker Seed (fun X => ⟨Iso.refl (whiskerLeftFunctor Seed X)⟩)

set_option backward.isDefEq.respectTransparency false in
theorem map_lift {X A B : τ} (f : valueObj X ⟶ valueObj A) (g : valueObj X ⟶ valueObj B) :
    (inc).map (cartPair f g) = Pa f.hom g.hom := by
  have hl : (inc).map (cartPair f g) ≫ F A B = f.hom :=
    congrArg (inc).map (CartesianMonoidalCategory.lift_fst f g)
  have hr : (inc).map (cartPair f g) ≫ S A B = g.hom :=
    congrArg (inc).map (CartesianMonoidalCategory.lift_snd f g)
  have e : Pa ((inc).map (cartPair f g) ≫ F A B) ((inc).map (cartPair f g) ≫ S A B) =
      (inc).map (cartPair f g) :=
    StructuralValues.reconstruct Seed (X := X) (A := A) (B := B) (cartPair f g).property
  rw [hl, hr] at e
  exact e.symm

set_option backward.isDefEq.respectTransparency false in
omit unitEta in
private theorem associatePair (A B C : τ) :
    (associateIso Seed (Obj A) (Obj B) (Obj C)).hom =
      Pa (F (A ×ₜ B) C ≫ F A B) (Pa (F (A ×ₜ B) C ≫ S A B) (S (A ×ₜ B) C)) := by
  have h := congrArg (proj).map (Paper.TypeCategory.associate_eq_pair (Φ := Φ) A B C)
  simp only [map_pairArrows, Functor.map_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
omit unitEta in
private theorem braidPair (A B : τ) :
    (braidIso Seed (Obj A) (Obj B)).hom = Pa (S A B) (F A B) := by
  have h := congrArg (proj).map (Paper.TypeCategory.braid_eq_pair (Φ := Φ) A B)
  rw [map_pairArrows] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem map_associator (A B C : τ) :
    (inc).map (α_ (valueObj A) (valueObj B) (valueObj C)).hom =
      (α_ (Obj A) (Obj B) (Obj C)).hom := by
  let p := Fst (valueObj A ⊗ valueObj B) (valueObj C)
  let q := Snd (valueObj A ⊗ valueObj B) (valueObj C)
  have h : (α_ (valueObj A) (valueObj B) (valueObj C)).hom =
      cartPair (p ≫ Fst (valueObj A) (valueObj B)) (cartPair (p ≫ Snd (valueObj A) (valueObj B)) q) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [p]
    · rw [CartesianMonoidalCategory.lift_snd]
      apply CartesianMonoidalCategory.hom_ext <;> simp [p, q, Category.assoc]
  rw [h, map_lift Seed]
  change Pa (F (A ×ₜ B) C ≫ F A B) ((inc).map (cartPair _ _)) = _
  rw [map_lift Seed]
  exact (associatePair Seed A B C).symm

set_option backward.isDefEq.respectTransparency false in
private theorem map_braid (A B : τ) :
    (inc).map (BraidedCategory.braiding (valueObj A) (valueObj B)).hom =
      (BraidedPremonoidalCategory.braiding (Obj A) (Obj B)).hom := by
  rw [← CartesianMonoidalCategory.lift_snd_fst, map_lift Seed]
  exact (braidPair Seed A B).symm

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible]
def freyd : FreydCategory (inc) where
  unitIso := Iso.refl _
  tensorIso _ _ := Iso.refl _
  tensor_naturality_left {X Y} f Z := by
    change whiskerRight Seed f.hom Z.obj ≫ 𝟙 _ = 𝟙 _ ≫ (inc).map (f ▷ Z)
    rw [Category.comp_id, Category.id_comp]
    exact (StructuralValues.map_whiskerRight Seed unitEta.out Z.obj.as f).symm
  tensor_naturality_right X {Y Z} f := by
    change whiskerLeft Seed X.obj f.hom ≫ 𝟙 _ = 𝟙 _ ≫ (inc).map (X ◁ f)
    rw [Category.comp_id, Category.id_comp]
    exact (StructuralValues.map_whiskerLeft Seed unitEta.out X.obj.as f).symm
  associativity X Y Z := by
    dsimp only [Iso.refl_hom]
    simp only [PremonoidalCategory.whiskerLeft_id, PremonoidalCategory.id_whiskerRight, Category.id_comp,
      Category.comp_id]
    exact (map_associator Seed X.obj.as Y.obj.as Z.obj.as).symm
  left_unitality X := by
    simp only [Iso.refl_hom, PremonoidalCategory.id_whiskerRight, Category.id_comp]
    rfl
  right_unitality X := by
    simp only [Iso.refl_hom, PremonoidalCategory.whiskerLeft_id, Category.id_comp]
    rfl
  map_central f :=
    ⟨fun g => (f.property.1.1 g).1, fun g => (f.property.1.1 g).2.symm⟩
  braiding X Y := by
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact map_braid Seed X.obj.as Y.obj.as
  obj_bijective := ⟨fun {_ _} h => WideSubcategory.ext h, fun X => ⟨⟨X⟩, rfl⟩⟩

theorem centralUnit :
    letI := freyd Seed
    FreydCategory.CentralUnit (inc) := by
  let := freyd Seed
  exact ⟨PremonoidalCategory.isCentral_id _⟩

theorem sharedTensor (X Y : Val) :
    letI := freyd Seed
    ∃ h : (inc).obj X ⊗ (inc).obj Y = (inc).obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := (inc)) X Y = eqToIso h :=
  ⟨rfl, rfl⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralValueFreyd
