module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Preservation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldDenotationTripling

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w u₁ u₂ v₁ v₂
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V)

open Paper.Extension.Singleton
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.StructuralValues (inclusion)
open Paper.Extension.Singleton.Generation (Coordinates Preserves mapInCoordinates
  mapInCoordinates_comp mapInCoordinates_id mapInCoordinates_exactCopair)
open Paper.WithCaseReturns.BinaryFold (JoinedStep ternaryStep ternaryFold ternaryFold_arrow ternaryStep_iterate_first)

set_option hygiene false in
local notation "S" => JoinedStep (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Obj" => ofType S
set_option hygiene false in
local notation "Q" => Paper.Extension.Singleton.TypeCategory S
set_option hygiene false in
local notation "I" => iterateChosen S
set_option hygiene false in
local notation "T" => Coordinates.ofModel J M
local infixr:65 " ⊕ₜ " => Silmaril.coprod

section ModelCoordinates

variable (F : Q ⥤ C) (objIso : ∀ A : τ, F.obj (Obj A) ≅ J.obj (M.obj A))
  (laws : Preserves S F objIso (T))

set_option hygiene false in
local notation "image" => mapInCoordinates S F objIso

set_option backward.isDefEq.respectTransparency false

private theorem pureCopair {A B D : τ} (f : M.obj A ⟶ M.obj D) (g : M.obj B ⟶ M.obj D) :
    ((T).sumIso A B).hom ≫ coprod.desc (J.map f) (J.map g) =
      J.map ((M.coprodIso A B).hom ≫ coprod.desc f g) := by
  let c := PreservesColimitPair.iso J (M.obj A) (M.obj B)
  change (J.map (M.coprodIso A B).hom ≫ c.inv) ≫ coprod.desc (J.map f) (J.map g) = _
  rw [Functor.map_comp, Category.assoc]
  congr 1
  apply (cancel_epi c.hom).mp
  rw [Iso.hom_inv_id_assoc]
  apply coprod.hom_ext
  · simp only [c, PreservesColimitPair.iso_hom, inl_coprodComparison_assoc, ← Functor.map_comp, coprod.inl_desc]
  · simp only [c, PreservesColimitPair.iso_hom, inr_coprodComparison_assoc, ← Functor.map_comp, coprod.inr_desc]

include laws in
private theorem image_ternaryFold (A : τ) :
    image ((inclusion S).map (ternaryFold pe A)) =
      J.map ((M.coprodIso A (A ⊕ₜ A)).hom ≫
        coprod.desc (𝟙 (M.obj A)) ((M.coprodIso A A).hom ≫ coprod.desc (𝟙 (M.obj A)) (𝟙 (M.obj A)))) := by
  rw [ternaryFold_arrow pe A, mapInCoordinates_exactCopair S F objIso (T) laws, mapInCoordinates_exactCopair S F objIso (T) laws, mapInCoordinates_id]
  rw [← J.map_id (M.obj A), pureCopair J M, pureCopair J M]

private noncomputable def mappedStep {A B : τ} (f : Obj A ⟶ Obj B ⨿ Obj A) :
    J.obj (M.obj A) ⟶ J.obj (M.obj B) ⨿ J.obj (M.obj A) :=
  image (f ≫ (sumIso S B A).inv) ≫ ((T).sumIso B A).hom

include laws in
private theorem mapIterate {A B : τ} (f : Obj A ⟶ Obj B ⨿ Obj A) :
    image (I f) = CategoryTheory.iterate (mappedStep pe J M F objIso f) :=
  laws.iterate (f ≫ (sumIso S B A).inv)

private theorem exactMap {A D B : τ} (h : Obj A ⟶ Obj D) :
    (sumIso S B A).hom ≫ coprod.map (𝟙 (Obj B)) h ≫ (sumIso S B D).inv =
      exactCopair S (sumCofan S B D).inl (h ≫ (sumCofan S B D).inr) := by
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit S B A)
  · rw [← Category.assoc, sumCofan_inl_sumIso_hom, coprod.inl_map_assoc, Category.id_comp,
      ← sumCofan_inl_sumIso_hom S B D, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact ((sumCofanIsColimit S B A).fac (BinaryCofan.mk (sumCofan S B D).inl
      (h ≫ (sumCofan S B D).inr)) ⟨WalkingPair.left⟩).symm
  · rw [← Category.assoc, sumCofan_inr_sumIso_hom, coprod.inr_map_assoc,
      ← sumCofan_inr_sumIso_hom S B D, Category.assoc (sumCofan S B D).inr, Iso.hom_inv_id, Category.comp_id]
    exact ((sumCofanIsColimit S B A).fac (BinaryCofan.mk (sumCofan S B D).inl
      (h ≫ (sumCofan S B D).inr)) ⟨WalkingPair.right⟩).symm

include laws in
private theorem mapExactMap {A D B : τ} (h : Obj A ⟶ Obj D) :
    image (exactCopair S (sumCofan S B D).inl (h ≫ (sumCofan S B D).inr)) ≫
      ((T).sumIso B D).hom =
    ((T).sumIso B A).hom ≫ coprod.map (𝟙 (J.obj (M.obj B))) (image h) := by
  rw [mapInCoordinates_exactCopair S F objIso (T) laws, mapInCoordinates_comp, laws.inl, laws.inr, Category.assoc]
  congr 1
  rw [coprod.desc_comp]
  apply coprod.hom_ext <;> simp

include laws in
private theorem mapSquare {A D B : τ} (f : Obj A ⟶ Obj B ⨿ Obj A) (g : Obj D ⟶ Obj B ⨿ Obj D)
    (h : Obj A ⟶ Obj D)
    (comm : f ≫ coprod.map (𝟙 (Obj B)) h = h ≫ g) :
    mappedStep pe J M F objIso f ≫ coprod.map (𝟙 _) (image h) =
      image h ≫ mappedStep pe J M F objIso g := by
  let endMap := exactCopair S (sumCofan S B D).inl (h ≫ (sumCofan S B D).inr)
  let f' := f ≫ (sumIso S B A).inv
  let g' := g ≫ (sumIso S B D).inv
  have exactComm : f' ≫ endMap = h ≫ g' := by
    simp only [f', g', endMap, ← exactMap, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc f, comm]
  have eq := congrArg (fun k => image k ≫ ((T).sumIso B D).hom) exactComm
  simpa only [mappedStep, mapInCoordinates_comp, Category.assoc, endMap, mapExactMap pe J M F objIso laws, f', g'] using eq

include laws in
private theorem image_ternary_uniformity {A B : τ} (g : Obj A ⟶ Obj B ⨿ Obj A) :
    image (I (ternaryStep pe g)) =
      image ((inclusion S).map (ternaryFold pe A)) ≫ image (I g) := by
  let h := (inclusion S).map (ternaryFold pe A)
  have pure := image_ternaryFold pe J M F objIso laws A
  have comm := mapSquare pe J M F objIso laws (ternaryStep pe g) g h
    (Paper.WithCaseReturns.BinaryFold.ternaryFold_square pe g)
  rw [show image h = _ from pure] at comm
  rw [mapIterate pe J M F objIso laws, mapIterate pe J M F objIso laws, pure]
  exact ElgotFreydCategory.pure_uniformity J _ _ _ comm

include laws in
private theorem image_tripling {A B : τ} (g : Obj A ⟶ Obj B ⨿ Obj A) :
    image (I (ThreeCycle.triple g)) = image (I g) := by
  let h := (inclusion S).map (ternaryFold pe A)
  let a := (sumCofan S A (A ⊕ₜ A)).inl
  have cycle : image (I (ternaryStep pe g)) = image h ≫ image (I g) :=
    image_ternary_uniformity pe J M F objIso laws g
  have first : a ≫ h = 𝟙 _ := by
    simp only [h, ternaryFold_arrow]
    exact (sumCofanIsColimit S A (A ⊕ₜ A)).fac (BinaryCofan.mk _ _) ⟨WalkingPair.left⟩
  rw [← ternaryStep_iterate_first pe g, mapInCoordinates_comp, cycle,
    ← Category.assoc, ← mapInCoordinates_comp, first, mapInCoordinates_id, Category.id_comp]

end ModelCoordinates

section Denotation

variable [FreydCategory.CentralUnit J] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
  (sound : SeedDenotes (Seed := S) J M)

set_option hygiene false in
local notation "F" => Paper.Extension.Singleton.denoteFunctor J M shared sound
set_option hygiene false in
local notation "exactObj" => (fun A : τ => Iso.refl (J.obj (M.obj A)))

set_option backward.isDefEq.respectTransparency false

private theorem exactImage {A B : τ} (f : Obj A ⟶ Obj B) :
    mapInCoordinates S (F) (exactObj) f = (F).map f := by
  change 𝟙 _ ≫ (F).map f ≫ 𝟙 _ = _
  rw [Category.comp_id, Category.id_comp]

theorem map_ternaryFold (A : τ) :
    (F).map ((inclusion S).map (ternaryFold pe A)) =
      J.map ((M.coprodIso A (A ⊕ₜ A)).hom ≫
        coprod.desc (𝟙 (M.obj A)) ((M.coprodIso A A).hom ≫ coprod.desc (𝟙 (M.obj A)) (𝟙 (M.obj A)))) := by
  simpa only [exactImage] using
    image_ternaryFold pe J M (F) (exactObj) (denoteFunctor_preserves J M shared sound) A

theorem map_ternary_uniformity {A B : τ} (g : Obj A ⟶ Obj B ⨿ Obj A) :
    (F).map (I (ternaryStep pe g)) =
      (F).map ((inclusion S).map (ternaryFold pe A)) ≫ (F).map (I g) := by
  simpa only [exactImage] using
    image_ternary_uniformity pe J M (F) (exactObj) (denoteFunctor_preserves J M shared sound) g

theorem map_tripling {A B : τ} (g : Obj A ⟶ Obj B ⨿ Obj A) :
    (F).map (I (ThreeCycle.triple g)) = (F).map (I g) := by
  simpa only [exactImage] using
    image_tripling pe J M (F) (exactObj) (denoteFunctor_preserves J M shared sound) g

end Denotation

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldDenotationTripling
