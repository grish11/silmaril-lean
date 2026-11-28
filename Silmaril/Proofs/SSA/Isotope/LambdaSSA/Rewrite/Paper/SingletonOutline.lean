module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Sums.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms

/-! # Outlining a row that never repeats into itself -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonOutline

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option backward.isDefEq.respectTransparency false

variable {R P Y : τ} (r₀ : ofType (Φ := Φ) R ⟶ ofType Y ⨿ ofType P)
  (c : ofType (Φ := Φ) P ⟶ ofType Y ⨿ ofType (Silmaril.coprod R P))

/-- The row of the new state: `r₀`, landing in the old states. -/
noncomputable abbrev front : ofType (Φ := Φ) R ⟶ ofType Y ⨿ ofType (Silmaril.coprod R P) :=
  r₀ ≫ coprod.map (𝟙 _) (sumInr R P)

/-- Run `r₀` in place of a jump to the new state. -/
noncomputable abbrev inlineAt : ofType (Φ := Φ) Y ⨿ ofType (Silmaril.coprod R P) ⟶ ofType Y ⨿ ofType P :=
  coprod.desc coprod.inl (sumDesc r₀ coprod.inr)

/-- The same, staying in the larger state type. -/
noncomputable abbrev inlineIn :
    ofType (Φ := Φ) Y ⨿ ofType (Silmaril.coprod R P) ⟶ ofType Y ⨿ ofType (Silmaril.coprod R P) :=
  coprod.desc coprod.inl (sumDesc (front r₀) (sumInr R P ≫ coprod.inr))

theorem inlineAt_in : inlineAt r₀ ≫ coprod.map (𝟙 _) (sumInr R P) = inlineIn (P := P) r₀ := by
  apply coprod.hom_ext
  · simp
  · simp [sumDesc_comp]

/-- A double step: a jump to the new state continues the inner loop there. -/
noncomputable abbrev double :
    ofType (Φ := Φ) (Silmaril.coprod R P) ⟶
      (ofType Y ⨿ ofType (Silmaril.coprod R P)) ⨿ ofType (Silmaril.coprod R P) :=
  sumDesc (front r₀ ≫ coprod.inl)
    (c ≫ coprod.desc (coprod.inl ≫ coprod.inl)
      (sumDesc (sumInl R P ≫ coprod.inr) (sumInr R P ≫ coprod.inr ≫ coprod.inl)))

theorem double_left : sumInl R P ≫ iterate (double r₀ c) = front r₀ := by
  rw [iterate_fixpoint, ← Category.assoc, sumInl_sumDesc, Category.assoc, coprod.inl_desc, Category.comp_id]

theorem double_iterate : iterate (double r₀ c) = sumDesc (front r₀) (c ≫ inlineIn r₀) := by
  have left := double_left r₀ c
  have right : sumInr R P ≫ iterate (double r₀ c) = c ≫ inlineIn r₀ := by
    rw [iterate_fixpoint, ← Category.assoc, sumInr_sumDesc, Category.assoc]
    congr 1
    apply coprod.hom_ext
    · simp
    · simp [sumDesc_comp, left]
  rw [← sumDesc_eta (iterate (double r₀ c)), left, right]

theorem double_flat : double r₀ c ≫ coprod.desc (𝟙 _) coprod.inr = sumDesc (front r₀) c := by
  have tail : coprod.desc (coprod.inl ≫ coprod.inl)
      (sumDesc (sumInl R P ≫ coprod.inr) (sumInr R P ≫ coprod.inr ≫ coprod.inl)) ≫
        coprod.desc (𝟙 (ofType (Φ := Φ) Y ⨿ ofType (Silmaril.coprod R P))) coprod.inr = 𝟙 _ := by
    apply coprod.hom_ext
    · simp
    · simp [sumDesc_comp, sumDesc_eta]
  rw [sumDesc_comp, Category.assoc, coprod.inl_desc, Category.comp_id, Category.assoc, tail, Category.comp_id]

/-- Entering the table with the new state at an old state is the loop of
the old rows with `r₀` run in place of each jump to the new state. -/
theorem outline : iterate (c ≫ inlineAt r₀) = sumInr R P ≫ iterate (sumDesc (front r₀) c) := by
  have roll := iterate_roll (sumInr R P) (sumDesc r₀ (c ≫ inlineAt r₀))
  have padded : sumDesc r₀ (c ≫ inlineAt r₀) ≫ coprod.map (𝟙 _) (sumInr R P) =
      sumDesc (front r₀) (c ≫ inlineIn r₀) := by
    rw [sumDesc_comp, Category.assoc, inlineAt_in]
  rw [sumInr_sumDesc, padded, ← double_iterate, iterate_codiagonal, double_flat] at roll
  exact roll

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonOutline
