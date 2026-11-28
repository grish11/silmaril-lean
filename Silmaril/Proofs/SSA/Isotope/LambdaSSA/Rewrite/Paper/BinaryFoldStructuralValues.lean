module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Elgot.Projection.HiddenBit.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldStructuralValues

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.Extension.Singleton
open CategoryTheory CategoryTheory.Limits
open Paper.WithCaseReturns.BinaryFold (JoinedStep double_step)
open Paper.WithCaseReturns.StructuralValues.HiddenBit (binary_fold_of_right_switch_and_double_of_seed)
open Paper.Extension.Singleton.StructuralValues
  (ofSyntaxType inclusion HomProperty copair_mem sum_inl_mem sum_inr_mem)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "S" => JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Q" => TypeCategory S
local notation "I" => iterateChosen S
local notation "Obj" => ofType S
local notation "VObj" => ofSyntaxType S
local infixr:65 " ⊕ₜ " => Silmaril.coprod

theorem uniformity_of_right_switch_block {A D B : Q}
    (d : A ⨿ (D ⨿ D) ⟶ (B ⨿ A) ⨿ (D ⨿ D)) (e : A ⨿ D ⟶ (B ⨿ A) ⨿ D)
    (square : d ≫ coprod.map (𝟙 (B ⨿ A)) (coprod.desc (𝟙 D) (𝟙 D)) =
      coprod.map (𝟙 A) (coprod.desc (𝟙 D) (𝟙 D)) ≫ e)
    (switch : coprod.inr ≫ (coprod.inr ≫ d) =
      (coprod.inr ≫ e) ≫ coprod.map (𝟙 (B ⨿ A)) (coprod.inl : D ⟶ D ⨿ D)) :
    I (d ≫ (coprod.associator B A (D ⨿ D)).hom) =
      coprod.map (𝟙 A) (coprod.desc (𝟙 D) (𝟙 D)) ≫ I (e ≫ (coprod.associator B A D).hom) := by
  apply iterateChosen_of_right_block S _ d e square
  have inner : (coprod.inr ≫ d) ≫ coprod.map (𝟙 (B ⨿ A)) (coprod.desc (𝟙 D) (𝟙 D)) =
      coprod.desc (𝟙 D) (𝟙 D) ≫ (coprod.inr ≫ e) := by
    simpa only [Category.assoc, coprod.inr_map_assoc] using
      congrArg ((coprod.inr : D ⨿ D ⟶ A ⨿ (D ⨿ D)) ≫ ·) square
  exact binary_fold_of_right_switch_and_double_of_seed S _ _ inner switch (double_step pe _)

set_option backward.isDefEq.respectTransparency false in
private theorem exactCopair_eq {A D : τ} {B : Q} (a : Obj A ⟶ B) (b : Obj D ⟶ B) :
    exactCopair S a b = (sumIso S A D).hom ≫ coprod.desc a b := by
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit S A D)
  · exact ((sumCofanIsColimit S A D).fac (BinaryCofan.mk a b) ⟨WalkingPair.left⟩).trans
      (by
        rw [← Category.assoc, sumCofan_inl_sumIso_hom, coprod.inl_desc]
        rfl)
  · exact ((sumCofanIsColimit S A D).fac (BinaryCofan.mk a b) ⟨WalkingPair.right⟩).trans
      (by
        rw [← Category.assoc, sumCofan_inr_sumIso_hom, coprod.inr_desc]
        rfl)

noncomputable def blockFold (A D : τ) : VObj (A ⊕ₜ (D ⊕ₜ D)) ⟶ VObj (A ⊕ₜ D) :=
  let l := (sumCofan S A D).inl
  let r := (sumCofan S A D).inr
  ⟨exactCopair S l (exactCopair S r r),
    copair_mem S (sum_inl_mem S A D) (copair_mem S (sum_inr_mem S A D) (sum_inr_mem S A D))⟩

set_option backward.isDefEq.respectTransparency false in
theorem blockFold_eq (A D : τ) :
    (inclusion S).map (blockFold pe A D) ≫ (sumIso S A D).hom =
    ((sumIso S A (D ⊕ₜ D)).hom ≫ coprod.map (𝟙 (Obj A)) (sumIso S D D).hom) ≫
      coprod.map (𝟙 (Obj A)) (coprod.desc (𝟙 (Obj D)) (𝟙 (Obj D))) := by
  change exactCopair S (sumCofan S A D).inl
    (exactCopair S (sumCofan S A D).inr (sumCofan S A D).inr) ≫ (sumIso S A D).hom = _
  rw [exactCopair_eq pe, exactCopair_eq pe, Category.assoc, Category.assoc, cancel_epi]
  apply coprod.hom_ext
  · simp only [coprod.inl_desc_assoc, sumCofan_inl_sumIso_hom, coprod.inl_map_assoc, Category.id_comp,
      coprod.inl_map]
  · simp [coprod.desc_comp]

noncomputable def ternaryFold (A : τ) : VObj (A ⊕ₜ (A ⊕ₜ A)) ⟶ VObj A :=
  let i := (HomProperty S).id_mem (Obj A)
  ⟨exactCopair S (𝟙 _) (exactCopair S (𝟙 _) (𝟙 _)), copair_mem S i (copair_mem S i i)⟩

private noncomputable def ternarySplit (A : τ) :
    Obj (A ⊕ₜ (A ⊕ₜ A)) ≅ Obj A ⨿ (Obj A ⨿ Obj A) :=
  sumIso S A (A ⊕ₜ A) ≪≫ coprod.mapIso (Iso.refl (Obj A)) (sumIso S A A)

noncomputable def ternaryStep {A : τ} {B : Q} (g : Obj A ⟶ B ⨿ Obj A) :
    Obj (A ⊕ₜ (A ⊕ₜ A)) ⟶ B ⨿ Obj (A ⊕ₜ (A ⊕ₜ A)) :=
  (ternarySplit pe A).hom ≫ ThreeCycle.step g ≫ coprod.map (𝟙 B) (ternarySplit pe A).inv

theorem ternaryFold_arrow (A : τ) :
    (inclusion S).map (ternaryFold pe A) =
      exactCopair S (𝟙 (ofType S A)) (exactCopair S (𝟙 (ofType S A)) (𝟙 (ofType S A))) := by
  unfold ternaryFold
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem ternaryStep_iterate_first {A : τ} {B : Q} (g : ofType S A ⟶ B ⨿ ofType S A) :
    (sumCofan S A (Silmaril.coprod A A)).inl ≫ I (ternaryStep pe g) = I (ThreeCycle.triple g) := by
  let e := ternarySplit (Φ := Φ) pe A
  have coord : ternaryStep pe g ≫ coprod.map (𝟙 B) e.hom = e.hom ≫ ThreeCycle.step g := by
    simp [ternaryStep, e, coprod.map_map]
  have first : (sumCofan S A (Silmaril.coprod A A)).inl ≫ e.hom = coprod.inl := by
    simp only [e, ternarySplit, Iso.trans_hom, coprod.mapIso_hom, Iso.refl_hom]
    rw [← Category.assoc, sumCofan_inl_sumIso_hom, coprod.inl_map, Category.id_comp]
  rw [uniformity_of_iso S e _ _ coord, ← Category.assoc, first, ThreeCycle.iterate_step_at_first]

set_option backward.isDefEq.respectTransparency false in
private theorem ternaryFold_eq (A : τ) :
    (ternarySplit pe A).hom ≫ ThreeCycle.fold (Obj A) = (inclusion S).map (ternaryFold pe A) := by
  change ((sumIso S A (A ⊕ₜ A)).hom ≫ coprod.map (𝟙 _) (sumIso S A A).hom) ≫ _ =
    exactCopair S (𝟙 _) (exactCopair S (𝟙 _) (𝟙 _))
  rw [exactCopair_eq pe, exactCopair_eq pe, Category.assoc, coprod.map_desc, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
theorem ternaryFold_square {A : τ} {B : Q} (g : Obj A ⟶ B ⨿ Obj A) :
    ternaryStep pe g ≫ coprod.map (𝟙 B) ((inclusion S).map (ternaryFold pe A)) =
      (inclusion S).map (ternaryFold pe A) ≫ g := by
  let e := ternarySplit (Φ := Φ) pe A
  have roundTrip : coprod.map (𝟙 B) e.inv ≫
      coprod.map (𝟙 B) (e.hom ≫ ThreeCycle.fold (Obj A)) =
      coprod.map (𝟙 B) (ThreeCycle.fold (Obj A)) := by simp [coprod.map_map]
  rw [← ternaryFold_eq pe A]
  change (e.hom ≫ ThreeCycle.step g ≫ coprod.map (𝟙 B) e.inv) ≫
    coprod.map (𝟙 B) (e.hom ≫ ThreeCycle.fold (Obj A)) = (e.hom ≫ ThreeCycle.fold (Obj A)) ≫ g
  simp only [Category.assoc, roundTrip, ThreeCycle.square S g]

set_option backward.isDefEq.respectTransparency false in
theorem ternaryFold_iff_triple {A : τ} {B : Q} (g : Obj A ⟶ B ⨿ Obj A) :
    I (ternaryStep pe g) = (inclusion S).map (ternaryFold pe A) ≫ I g ↔
      I (ThreeCycle.triple g) = I g := by
  let e := ternarySplit (Φ := Φ) pe A
  have coord : ternaryStep pe g ≫ coprod.map (𝟙 B) e.hom = e.hom ≫ ThreeCycle.step g := by
    simp [ternaryStep, e, coprod.map_map]
  rw [uniformity_of_iso S e _ _ coord, ← ternaryFold_eq pe A]
  change e.hom ≫ I (ThreeCycle.step g) = (e.hom ≫ ThreeCycle.fold (Obj A)) ≫ I g ↔ _
  rw [Category.assoc, cancel_epi]
  exact ThreeCycle.fold_iff_triple S g

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldStructuralValues
