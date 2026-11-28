module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.SlotMaps.Boundary.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.SlotMaps.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms

/-! # Coordinates of the finite state map on an ordered boundary -/

public section

universe u u₁ v₁

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.CfgSlotBoundary

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {κ : Type u} (M : TypeModel (Ty κ) V) {n : Nat} {P Q : Fin n → Ty κ}

private theorem local_look (P : Fin n → Ty κ) (i : Fin n) : At (List.ofFn P) i (P i) :=
  by simp [At, i.isLt]

private theorem merge_split (P : Fin n → Ty κ) (L : LCtx (Ty κ)) :
    mergeLabels M P L ≫ labelAppendSplit M (List.ofFn P) L = 𝟙 _ := by
  apply coprod.hom_ext
  · rw [mergeLabels, Category.comp_id, coprod.inl_desc_assoc]
    apply labelHom_ext M
    intro i A h
    rw [labelInject_labelMap_assoc, labelAppendSplit_exit]
  · rw [mergeLabels, Category.comp_id, coprod.inr_desc_assoc]
    apply labelHom_ext M
    intro i A h
    have lt : i < n := by simpa using (List.getElem?_eq_some_iff.mp h).1
    let j : Fin n := ⟨i, lt⟩
    have eq : P j = A := Option.some.inj ((local_look P j).symm.trans h)
    subst A
    change labelInject M j (local_look P j) ≫ _ = _
    rw [labelInject_labelMap_assoc]
    exact labelAppendSplit_local M P L j _ _

theorem split (slot : ∀ i, M.obj (P i) ⟶ M.obj (Q i)) (L : LCtx (Ty κ)) :
    mapSlotBoundary M slot L ≫ labelAppendSplit M (List.ofFn Q) L =
      labelAppendSplit M (List.ofFn P) L ≫ coprod.map (𝟙 _) (mapSlotLabels M slot) := by
  simp only [mapSlotBoundary, Category.assoc, merge_split, Category.comp_id]

theorem local_coord (slot : ∀ i, M.obj (P i) ⟶ M.obj (Q i)) (L : LCtx (Ty κ)) (i : Fin n)
    (hi : At (List.ofFn P ++ L) i (P i)) (hj : At (List.ofFn Q ++ L) i (Q i)) :
    labelInject M i hi ≫ mapSlotBoundary M slot L = slot i ≫ labelInject M i hj := by
  rw [mapSlotBoundary, ← Category.assoc, labelAppendSplit_local M P L i hi (local_look P i),
    Category.assoc, ← Category.assoc coprod.inr, coprod.inr_map, Category.assoc,
    mapSlotLabels_inject_assoc M slot i (local_look P i) (local_look Q i),
    mergeLabels, coprod.inr_desc, labelInject_labelMap]
  rfl

theorem exit_coord (slot : ∀ i, M.obj (P i) ⟶ M.obj (Q i)) (L : LCtx (Ty κ)) {i : Nat} {A : Ty κ}
    (hi : At L i A) (hp : At (List.ofFn P ++ L) (n+i) A) (hq : At (List.ofFn Q ++ L) (n+i) A) :
    labelInject M (n+i) hp ≫ mapSlotBoundary M slot L = labelInject M (n+i) hq := by
  rw [mapSlotBoundary, ← Category.assoc, labelAppendSplit_exit M P L hi,
    Category.assoc, ← Category.assoc coprod.inl, coprod.inl_map, Category.id_comp,
    mergeLabels, coprod.inl_desc, labelInject_labelMap]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.CfgSlotBoundary
