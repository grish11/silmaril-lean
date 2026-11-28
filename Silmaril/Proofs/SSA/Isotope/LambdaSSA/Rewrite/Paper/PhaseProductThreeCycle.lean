module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.PhaseProduct.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.ProductBeta.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PhaseProductThreeCycle

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open Paper.TypeCategory.PhaseProduct
open Paper.RetainedCase.Chosen (paperChosenDistributor_hom)
open CfgEta.TypeCategory (productFstBranches whiskerLeftRegion_typed seqValueBranches)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => Paper.TypeCategory (τ := τ) Φ
local notation "T" => Paper.TypeCategory.ofType (Φ := Φ)
local notation "U" => (Silmaril.unit : τ)
local infixr:70 " ×ₜ " => Silmaril.product
local infixr:65 " ⊕ₜ " => Silmaril.coprod
local notation "W" => Packet (Φ := Φ)

set_option backward.isDefEq.respectTransparency false

private theorem retained_fst_of_branch (A : τ) {D E : τ} {a : Tm Φ} (ha : Tm.BranchValue [D] a E) :
    whiskerLeft (T A) (ofRegion (.br (ℓ := 0) rfl ha)) ≫ ofRegion (τ := τ) (productFstBranches (Φ := Φ) A E) =
      ofRegion (τ := τ) (productFstBranches (Φ := Φ) A D) := by
  let hr : ValueBranches [D] (.br 0 a) [E] := .br rfl ha
  change whiskerLeft (T A) (ofRegion hr) ≫ _ = _
  rw [whiskerLeft_ofRegion]
  unfold tensorObj
  rw [ofRegion_comp _ _
    (seqValueBranches (whiskerLeftRegion_typed A hr) (productFstBranches A E))]
  apply (ofRegion_eq_iff _ _).2
  apply Paper.Eqv.let₂ (A := A) (B := D) (.var rfl)
  let ρ := Silmaril.DeBruijn.lift (Nat.succ ∘ Nat.succ)
  change Paper.Eqv [D, A, A ×ₜ D] (.let₂ (.pair (.var 1) (a.rename ρ)) (.br 0 (.var 1)))
    (.br 0 (.var 1)) [A]
  have ren : Ren [D] [D, A, A ×ₜ D] ρ := by
    intro i X hi
    cases i with
    | zero => cases Option.some.inj hi; rfl
    | succ i => simp [At] at hi
  have ha' : Tm.BranchValue [D, A, A ×ₜ D] (a.rename ρ) E := by
    simpa only [Tm.rename_eq_subst] using ha.subst (σ := Tm.var ∘ ρ) (fun _ _ hi => .var (ren hi))
  exact .productBeta (.let₂Beta (.var rfl) ha' (.br rfl (.var (i := 1) rfl)))

@[reassoc] private theorem splitPair_inl (A X Y : τ) :
    coprod.inl ≫ (splitPair (Φ := Φ) A X Y).hom =
      (whiskerLeftFunctor (T A)).map (sumCofan X Y).inl := by
  let F := whiskerLeftFunctor (T A)
  have inj : (coprod.inl : T X ⟶ T X ⨿ T Y) ≫ (sumIso X Y).inv = (sumCofan X Y).inl := by
    rw [← sumCofan_inl_sumIso_hom (Φ := Φ) X Y, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change coprod.inl ≫ (Paper.RetainedCase.Chosen.paperChosenDistributor A X Y).hom ≫
    F.map (sumIso X Y).inv = _
  rw [paperChosenDistributor_hom]
  change (coprod.inl : F.obj (T X) ⟶ F.obj (T X) ⨿ F.obj (T Y)) ≫
    coprodComparison F (T X) (T Y) ≫ F.map (sumIso X Y).inv = _
  rw [← Category.assoc, inl_coprodComparison, ← F.map_comp, inj]

@[reassoc] private theorem splitPair_inr (A X Y : τ) :
    coprod.inr ≫ (splitPair (Φ := Φ) A X Y).hom =
      (whiskerLeftFunctor (T A)).map (sumCofan X Y).inr := by
  let F := whiskerLeftFunctor (T A)
  have inj : (coprod.inr : T Y ⟶ T X ⨿ T Y) ≫ (sumIso X Y).inv = (sumCofan X Y).inr := by
    rw [← sumCofan_inr_sumIso_hom (Φ := Φ) X Y, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change coprod.inr ≫ (Paper.RetainedCase.Chosen.paperChosenDistributor A X Y).hom ≫
    F.map (sumIso X Y).inv = _
  rw [paperChosenDistributor_hom]
  change (coprod.inr : F.obj (T Y) ⟶ F.obj (T X) ⨿ F.obj (T Y)) ≫
    coprodComparison F (T X) (T Y) ≫ F.map (sumIso X Y).inv = _
  rw [← Category.assoc, inr_coprodComparison, ← F.map_comp, inj]

private theorem left_retained (A X Y : τ) :
    (whiskerLeftFunctor (T A)).map (sumCofan X Y).inl ≫ ofRegion (τ := τ) (productFstBranches (Φ := Φ) A (X ⊕ₜ Y)) =
      ofRegion (τ := τ) (productFstBranches (Φ := Φ) A X) := by
  rw [sumCofan_inl]
  exact retained_fst_of_branch A (.inl (.var rfl))

private theorem right_retained (A X Y : τ) :
    (whiskerLeftFunctor (T A)).map (sumCofan X Y).inr ≫ ofRegion (τ := τ) (productFstBranches (Φ := Φ) A (X ⊕ₜ Y)) =
      ofRegion (τ := τ) (productFstBranches (Φ := Φ) A Y) := by
  rw [sumCofan_inr]
  exact retained_fst_of_branch A (.inr (.var rfl))

theorem split_payload (A : τ) :
    (split (Φ := Φ) A).hom ≫ payload A =
      coprod.desc (rightUnitProjection A) (coprod.desc (rightUnitProjection A) (rightUnitProjection A)) := by
  apply coprod.hom_ext
  · simp only [split, Iso.trans_hom, coprod.mapIso_hom, Iso.refl_hom, Category.assoc,
      coprod.inl_map_assoc, Category.id_comp, splitPair_inl_assoc, coprod.inl_desc]
    exact left_retained (Φ := Φ) A U (U ⊕ₜ U)
  · apply coprod.hom_ext
    · simp only [split, Iso.trans_hom, coprod.mapIso_hom, Iso.refl_hom, Category.assoc,
        coprod.inr_map_assoc, splitPair_inl_assoc, splitPair_inr_assoc]
      rw [right_retained (Φ := Φ) A U (U ⊕ₜ U)]
      let d : W A ⟶ T A := rightUnitProjection A
      rw [show (coprod.inr : W A ⨿ W A ⟶ W A ⨿ (W A ⨿ W A)) ≫ coprod.desc d (coprod.desc d d) =
        coprod.desc d d from coprod.inr_desc _ _, coprod.inl_desc]
      exact left_retained (Φ := Φ) A U U
    · simp only [split, Iso.trans_hom, coprod.mapIso_hom, Iso.refl_hom, Category.assoc,
        coprod.inr_map_assoc, splitPair_inr_assoc, coprod.inr_desc]
      rw [right_retained (Φ := Φ) A U (U ⊕ₜ U)]
      exact right_retained (Φ := Φ) A U U

theorem native_square {A : τ} {B : P} (f : T A ⟶ B ⨿ T A) :
    step f ≫ coprod.map (𝟙 B) (payload A) = payload A ≫ f := by
  let s := split (Φ := Φ) A
  let i₀ : W A ⟶ W A ⨿ (W A ⨿ W A) := coprod.inl
  let i₁ : W A ⟶ W A ⨿ (W A ⨿ W A) := coprod.inl ≫ coprod.inr
  let i₂ : W A ⟶ W A ⨿ (W A ⨿ W A) := coprod.inr ≫ coprod.inr
  have leg {i : W A ⟶ W A ⨿ (W A ⨿ W A)} (h : i ≫ s.hom ≫ payload A = rightUnitProjection A) :
      (packetStep f ≫ coprod.map (𝟙 B) (i ≫ s.hom)) ≫ coprod.map (𝟙 B) (payload A) =
        rightUnitProjection A ≫ f := by
    rw [Category.assoc, coprod.map_map, Category.id_comp, Category.assoc i, h, packetStep]
    simp only [Category.assoc, coprod.map_map, rightUnit_section_projection,
      coprod.map_id_id, Category.comp_id]
  have zero := leg (i := i₀) (by simp [i₀, s, split_payload])
  have one := leg (i := i₁) (by simp [i₁, s, split_payload])
  have two := leg (i := i₂) (by simp [i₂, s, split_payload])
  apply (cancel_epi s.hom).mp
  rw [← Category.assoc s.hom (payload A), show s.hom ≫ payload A = _ from split_payload A]
  change s.hom ≫ (s.inv ≫ _) ≫ coprod.map (𝟙 B) (payload A) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  apply coprod.hom_ext
  · simpa only [i₁, Category.assoc, coprod.inl_desc_assoc] using one
  · apply coprod.hom_ext
    · simpa only [i₂, Category.assoc, coprod.inr_desc_assoc, coprod.inl_desc_assoc] using two
    · simpa only [i₀, Category.assoc, coprod.inr_desc_assoc] using zero

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PhaseProductThreeCycle
