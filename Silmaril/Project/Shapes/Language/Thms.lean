module

public import Silmaril.Project.Shapes.Language.Defs

/-!
# Standard problem shapes: languages, what each status means

For an instance that leaves only the sentence `x` free, the four SZS statuses are the
statements below (each is the shape of `@[answers … s]` for that status, so an answer of status
`s` *is* a proof of the right-hand side, and conversely):

* `member`: `thm` ↔ `L = Set.univ`, `sat` ↔ `L.Nonempty`, `uns` ↔ `L = ∅`, `csa` ↔ `L ≠ Set.univ`;
* `subset_at`: `thm` ↔ `L ⊆ K`, `csa` ↔ `(L \ K).Nonempty`;
* `eq_at`: `thm` ↔ `L = K`, `csa` ↔ `L ≠ K`;
* `bound_at`: `thm` ↔ `L ⊆ {x | μ x ≤ b}`, `csa` ↔ some member has `b < μ x`;
* `eq_within_at`: `thm` ↔ `L = Languages.within K μ b`.
-/

@[expose] public section

namespace Silmaril.Project.Shapes

variable {α : Type} {L K : Set α} {μ : α → ℕ} {b : ℕ}

theorem member_thm_iff : (∀ x, Member L x) ↔ L = Set.univ := Set.eq_univ_iff_forall.symm

theorem member_sat_iff : (∃ x, Member L x) ↔ L.Nonempty := Iff.rfl

theorem member_uns_iff : (∀ x, ¬ Member L x) ↔ L = ∅ := Set.eq_empty_iff_forall_notMem.symm

theorem member_csa_iff : (∃ x, ¬ Member L x) ↔ L ≠ Set.univ := by
  rw [Ne, ← member_thm_iff, not_forall]

theorem subsetAt_thm_iff : (∀ x, SubsetAt L K x) ↔ L ⊆ K := Iff.rfl

theorem subsetAt_csa_iff : (∃ x, ¬ SubsetAt L K x) ↔ (L \ K).Nonempty := by
  simp only [SubsetAt, Classical.not_imp]; rfl

theorem eqAt_thm_iff : (∀ x, EqAt L K x) ↔ L = K := Set.ext_iff.symm

theorem eqAt_csa_iff : (∃ x, ¬ EqAt L K x) ↔ L ≠ K := by
  rw [Ne, ← eqAt_thm_iff, not_forall]

theorem boundAt_thm_iff : (∀ x, BoundAt L μ b x) ↔ L ⊆ {x | μ x ≤ b} := Iff.rfl

theorem boundAt_csa_iff : (∃ x, ¬ BoundAt L μ b x) ↔ ∃ x ∈ L, b < μ x := by
  simp only [BoundAt, Classical.not_imp, not_le]

theorem eqWithinAt_thm_iff : (∀ x, EqWithinAt L K μ b x) ↔ L = Languages.within K μ b :=
  (Set.ext_iff (a := L) (b := Languages.within K μ b)).symm

end Silmaril.Project.Shapes
