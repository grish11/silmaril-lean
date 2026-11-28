module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Blocks.Defs

/-! # Elimination of the right block, with feedback in the left block -/

public section

universe v u

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.BlockIteration

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (BlockSystem)

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] (S : BlockSystem C) {Y : C}

/-- Split a row's targets: jumps to the left block stay outside the inner
loop, jumps to the right block are inside it. -/
noncomputable def split (Y : C) : (Y ⨿ S.left) ⨿ S.right ⟶ (Y ⨿ S.sum) ⨿ S.sum :=
  coprod.desc (coprod.desc (coprod.inl ≫ coprod.inl) (S.inl ≫ coprod.inr ≫ coprod.inl))
    (S.inr ≫ coprod.inr)

theorem split_flat : split S Y ≫ coprod.desc (𝟙 _) coprod.inr = S.route Y := by
  unfold split BlockSystem.route
  apply coprod.hom_ext
  · apply coprod.hom_ext <;> simp
  · simp

theorem bekic (r : S.left ⟶ (Y ⨿ S.left) ⨿ S.right) (c : S.right ⟶ (Y ⨿ S.left) ⨿ S.right) :
    S.inl ≫ S.iter (S.joined r c) = S.iter (r ≫ coprod.desc (𝟙 _) (S.iter c)) ∧
    S.inr ≫ S.iter (S.joined r c) =
      S.iter c ≫ coprod.desc (𝟙 Y) (S.inl ≫ S.iter (S.joined r c)) := by
  let f : S.sum ⟶ (Y ⨿ S.sum) ⨿ S.sum := S.desc (r ≫ split S Y) (c ≫ split S Y)
  have fl : S.inl ≫ f = r ≫ split S Y := S.inl_desc _ _
  have fr : S.inr ≫ f = c ≫ split S Y := S.inr_desc _ _
  have flat : f ≫ coprod.desc (𝟙 _) coprod.inr = S.joined r c := by
    apply S.ext
    · rw [reassoc_of% fl, split_flat]
      exact (S.inl_desc _ _).symm
    · rw [reassoc_of% fr, split_flat]
      exact (S.inr_desc _ _).symm
  have second : S.inr ≫ S.iter f = S.iter c ≫ coprod.map (𝟙 Y) S.inl := by
    have comm : (c ≫ coprod.map (coprod.map (𝟙 Y) S.inl) (𝟙 _)) ≫ coprod.map (𝟙 _) S.inr =
        S.inr ≫ f := by
      rw [fr, Category.assoc]
      congr 1
      unfold split
      apply coprod.hom_ext
      · apply coprod.hom_ext <;> simp
      · simp
    rw [← S.uniform_inr _ f comm, S.naturality]
  have first : S.inl ≫ S.iter f =
      (r ≫ coprod.desc (𝟙 _) (S.iter c)) ≫ coprod.map (𝟙 Y) S.inl := by
    rw [S.fixpoint f, reassoc_of% fl, Category.assoc]
    congr 1
    unfold split
    apply coprod.hom_ext
    · apply coprod.hom_ext <;> simp
    · simp only [coprod.inr_desc_assoc, Category.assoc, coprod.inr_desc]
      exact second
  have outer := S.uniform_inl (r ≫ coprod.desc (𝟙 _) (S.iter c)) (S.iter f) first.symm
  have joined : S.iter (S.iter f) = S.iter (S.joined r c) := by rw [S.codiagonal, flat]
  refine ⟨?_, ?_⟩
  · rw [outer, joined]
  · rw [← joined]
    conv_lhs => rw [S.fixpoint (S.iter f)]
    rw [reassoc_of% second]
    congr 1
    apply coprod.hom_ext <;> simp

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.BlockIteration
