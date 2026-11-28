module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Classes.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms

/-! # Pairs of duplicates are phases of the pair, compatibly with the folds -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonClasses

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option backward.isDefEq.respectTransparency false

/-- Rolling gives uniformity along every iso of default Paper. -/
theorem iterate_iso {X W Y : Paper.TypeCategory (τ := τ) Φ} (ψ : X ≅ W) (J : X ⟶ Y ⨿ X) :
    iterate J = ψ.hom ≫ iterate (ψ.inv ≫ J ≫ coprod.map (𝟙 Y) ψ.hom) := by
  have roll := iterate_roll ψ.hom (ψ.inv ≫ J)
  rwa [Iso.hom_inv_id_assoc, Category.assoc] at roll

variable (A B : τ)

theorem assoc_desc {X Y W T : τ} (u : ofType (Φ := Φ) (Silmaril.coprod X Y) ⟶ ofType T)
    (v : ofType (Φ := Φ) W ⟶ ofType T) :
    (sumAssoc X Y W).hom ≫ (sumIso (Silmaril.coprod X Y) W).hom ≫ coprod.desc u v =
      (sumIso X (Silmaril.coprod Y W)).hom ≫ coprod.desc (sumInl X Y ≫ u)
        ((sumIso Y W).hom ≫ coprod.desc (sumInr X Y ≫ u) v) := by
  have key : (coprod.associator (ofType (Φ := Φ) X) (ofType Y) (ofType W)).inv ≫
      coprod.map (sumIso X Y).inv (𝟙 _) ≫ coprod.desc u v =
      coprod.desc (sumInl X Y ≫ u) (coprod.desc (sumInr X Y ≫ u) v) := by
    apply coprod.hom_ext
    · simp [sumInl]
    · apply coprod.hom_ext <;> simp [sumInr]
  simp only [sumAssoc, Iso.trans_hom, Iso.symm_hom, coprod.mapIso_hom, Iso.refl_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [key]
  congr 1
  apply coprod.hom_ext <;> simp

theorem pairIso_fold : ∀ n,
    (pairIso (Φ := Φ) A B n).hom ≫ phaseFold (Silmaril.coprod A B) n = pairFold A B n
  | 0 => Category.id_comp _
  | n + 1 => by
    have ih := pairIso_fold n
    have inner : (sumMapIso (Silmaril.coprod A B) (pairIso (Φ := Φ) A B n)).hom ≫
        phaseFold (Silmaril.coprod A B) (n + 1) =
        (sumIso (Silmaril.coprod A B) (pairPhases A B n)).hom ≫ coprod.desc (𝟙 _) (pairFold A B n) := by
      simp only [sumMapIso, phaseFold, Iso.trans_hom, Iso.symm_hom, coprod.mapIso_hom, Iso.refl_hom,
        Category.assoc, Iso.inv_hom_id_assoc, coprod.map_desc, Category.id_comp, ih]
    have e : (pairIso (Φ := Φ) A B (n + 1)).hom =
        (sumAssoc A B (pairPhases A B n)).hom ≫ (sumMapIso (Silmaril.coprod A B) (pairIso A B n)).hom := rfl
    rw [e, Category.assoc, inner, assoc_desc]
    simp only [pairFold, Category.comp_id]

theorem pairFold_inl (n : Nat) :
    sumInl A (Silmaril.coprod B (pairPhases A B n)) ≫ pairFold (Φ := Φ) A B (n + 1) = sumInl A B := by
  simp [sumInl, pairFold]

theorem pairFold_inr_inl (n : Nat) :
    sumInl B (pairPhases A B n) ≫ sumInr A (Silmaril.coprod B (pairPhases A B n)) ≫
      pairFold (Φ := Φ) A B (n + 1) = sumInr A B := by
  simp [sumInl, sumInr, pairFold]

theorem pairFold_inr_inr (n : Nat) :
    sumInr B (pairPhases A B n) ≫ sumInr A (Silmaril.coprod B (pairPhases A B n)) ≫
      pairFold (Φ := Φ) A B (n + 1) = pairFold A B n := by
  simp [sumInr, pairFold]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonClasses
