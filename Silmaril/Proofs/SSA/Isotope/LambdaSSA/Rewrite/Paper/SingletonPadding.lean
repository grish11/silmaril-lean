module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Padding.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Classes.Thms
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonBlocks

/-! # Unreachable padding in default Paper -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonPadding

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option backward.isDefEq.respectTransparency false

theorem inl_desc {U X T : τ} (a : ofType (Φ := Φ) U ⟶ ofType T) (b : ofType (Φ := Φ) X ⟶ ofType T) :
    sumInl U X ≫ sumDesc a b = a :=
  (SingletonBlocks.blockSystem U X).inl_desc a b

theorem inr_desc {U X T : τ} (a : ofType (Φ := Φ) U ⟶ ofType T) (b : ofType (Φ := Φ) X ⟶ ofType T) :
    sumInr U X ≫ sumDesc a b = b :=
  (SingletonBlocks.blockSystem U X).inr_desc a b

theorem desc_eta {U X T : τ} (x : ofType (Φ := Φ) (Silmaril.coprod U X) ⟶ ofType T) :
    x = sumDesc (sumInl U X ≫ x) (sumInr U X ≫ x) :=
  SingletonBlocks.sum_decomp U X x

theorem desc_ext {U X T : τ} {x y : ofType (Φ := Φ) (Silmaril.coprod U X) ⟶ ofType T}
    (hl : sumInl U X ≫ x = sumInl U X ≫ y) (hr : sumInr U X ≫ x = sumInr U X ≫ y) : x = y :=
  SingletonPhases.sum_ext U X hl hr

theorem desc_comp {U X T W : τ} (a : ofType (Φ := Φ) U ⟶ ofType T) (b : ofType (Φ := Φ) X ⟶ ofType T)
    (f : ofType (Φ := Φ) T ⟶ ofType W) : sumDesc a b ≫ f = sumDesc (a ≫ f) (b ≫ f) :=
  desc_ext (by rw [← Category.assoc, inl_desc, inl_desc]) (by rw [← Category.assoc, inr_desc, inr_desc])

theorem desc_inl_inr (U X : τ) : sumDesc (sumInl (Φ := Φ) U X) (sumInr U X) = 𝟙 _ := by
  have eta := desc_eta (𝟙 (ofType (Φ := Φ) (Silmaril.coprod U X)))
  rw [Category.comp_id, Category.comp_id] at eta
  exact eta.symm

variable (U : τ) {X Z Y : τ} (u : ofType (Φ := Φ) U ⟶ ofType Z) (s : ofType (Φ := Φ) Z ⟶ ofType X)
  (J : ofType (Φ := Φ) X ⟶ ofType Y ⨿ ofType X) (T : ofType (Φ := Φ) Z ⟶ ofType Y ⨿ ofType Z)

/-- Entering the padded table at an old state is the original loop. The
embedding is a constructor injection, so this is default Paper. -/
theorem iterate_padStep : iterate J = sumInr U X ≫ iterate (padStep U u s J T) :=
  SingletonPhases.uniform_inr U X Y J (padStep U u s J T) (inr_desc _ _).symm

/-- The padded state map is a simulation of the padded table when the
original one is, and `s` picks a state of each class. -/
theorem padStep_square (h : ofType (Φ := Φ) X ⟶ ofType Z) (sect : s ≫ h = 𝟙 _)
    (square : J ≫ coprod.map (𝟙 _) h = h ≫ T) :
    padStep U u s J T ≫ coprod.map (𝟙 _) (sumDesc u h) = sumDesc u h ≫ T := by
  apply desc_ext
  · have row : sumInl U X ≫ padStep U u s J T = u ≫ T ≫ coprod.map (𝟙 _) (s ≫ sumInr U X) :=
      inl_desc _ _
    have back : coprod.map (𝟙 (ofType (Φ := Φ) Y)) (s ≫ sumInr U X) ≫ coprod.map (𝟙 _) (sumDesc u h) =
        𝟙 _ := by
      rw [coprod.map_map, Category.id_comp, Category.assoc, inr_desc, sect, coprod.map_id_id]
    rw [reassoc_of% row, back, Category.comp_id, ← Category.assoc, inl_desc]
  · have row : sumInr U X ≫ padStep U u s J T = J ≫ coprod.map (𝟙 _) (sumInr U X) := inr_desc _ _
    have fold : coprod.map (𝟙 (ofType (Φ := Φ) Y)) (sumInr U X) ≫ coprod.map (𝟙 _) (sumDesc u h) =
        coprod.map (𝟙 _) h := by
      rw [coprod.map_map, Category.id_comp, inr_desc]
    rw [reassoc_of% row, fold, square, ← Category.assoc, inr_desc]

variable (A B : τ)

theorem pairFirst_fold : ∀ n, pairFirst (Φ := Φ) A B n ≫ pairFold A B n = sumInl A B
  | 0 => Category.comp_id _
  | n + 1 => pairFold_inl A B n

theorem short_split (n : Nat) :
    pairFold (Φ := Φ) A B (n + 1) = sumDesc (sumInl A B) (shortFold A B n) := by
  have eta := desc_eta (pairFold (Φ := Φ) A B (n + 1))
  rw [pairFold_inl] at eta
  exact eta

theorem shortSection_fold (n : Nat) : shortSection (Φ := Φ) A B n ≫ shortFold A B n = 𝟙 _ := by
  apply desc_ext
  · have leg : sumInl A B ≫ shortSection (Φ := Φ) A B n = pairFirst A B n ≫ sumInr B _ := inl_desc _ _
    rw [reassoc_of% leg, Category.comp_id]
    unfold shortFold
    rw [pairFold_inr_inr, pairFirst_fold]
  · have leg : sumInr A B ≫ shortSection (Φ := Φ) A B n = sumInl B _ := inr_desc _ _
    rw [reassoc_of% leg, Category.comp_id]
    unfold shortFold
    exact pairFold_inr_inl A B n

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonPadding
