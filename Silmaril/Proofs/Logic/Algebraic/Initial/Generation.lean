module

public import Silmaril.Logic.Algebraic.Initial.Generation.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Generation

open Silmaril.Logic.Institution.Examples
open Presented.Characterization
variable {A : EQ.Signature}

/-- Actual ground-term ranges are closed under every sorted operation. -/
theorem groundStep_evaluationRange_le (M : EQ.Algebra A) :
    groundStep M (evaluationRange M) ≤ evaluationRange M := by
  classical
  rintro s x ⟨n, w, op, args, hargs, rfl⟩
  change (∀ i, ∃ t : Ground A (w i), evaluate M t = args i) at hargs
  choose terms hterms using hargs
  refine ⟨EQ.Term.app op terms, ?_⟩
  change M.op op (fun i => evaluate M (terms i)) = M.op op args
  exact congrArg (M.op op) (funext hterms)

/-- Least-fixed-point induction uses actual operation closure, not a model field. -/
theorem generated_le_of_closed (M : EQ.Algebra A) (X : Family M)
    (h : groundStep M X ≤ X) : generated M ≤ X :=
  (groundStep M).lfp_le h

theorem generated_unfold (M : EQ.Algebra A) :
    groundStep M (generated M) = generated M :=
  (groundStep M).map_lfp

theorem generated_le_evaluationRange (M : EQ.Algebra A) :
    generated M ≤ evaluationRange M :=
  generated_le_of_closed M (evaluationRange M) (groundStep_evaluationRange_le M)

/-- Every existing sorted public ground term evaluates into the fixed point.
The variable case is impossible because the original context is empty. -/
theorem evaluate_mem_generated (M : EQ.Algebra A) {s : A.S} (t : Ground A s) :
    evaluate M t ∈ generated M s := by
  induction t with
  | var i => exact i.elim0
  | @app n w s op args ih =>
      apply (generated_unfold M).le s
      exact ⟨n, w, op, (fun i => evaluate M (args i)), ih, rfl⟩

theorem evaluationRange_le_generated (M : EQ.Algebra A) :
    evaluationRange M ≤ generated M := by
  rintro s x ⟨t, rfl⟩
  exact evaluate_mem_generated M t

/-- Arbitrary sorts and arbitrary operation families: the independently defined
product least fixed point is exactly the family of actual ground-evaluation ranges. -/
theorem generated_eq_evaluationRange (M : EQ.Algebra A) :
    generated M = evaluationRange M :=
  le_antisymm (generated_le_evaluationRange M) (evaluationRange_le_generated M)

/-- The componentwise statement uses the existing public Ground and evaluate. -/
theorem groundStep_lfp_eq_range (M : EQ.Algebra A) (s : A.S) :
    (groundStep M).lfp s = Set.range (evaluate M (s := s)) :=
  congrFun (generated_eq_evaluationRange M) s

/-- Actual operation-closed families contain the values of every ground term. -/
theorem evaluate_mem_of_closed (M : EQ.Algebra A) (X : Family M)
    (h : groundStep M X ≤ X) {s : A.S} (t : Ground A s) :
    evaluate M t ∈ X s :=
  generated_le_of_closed M X h s (evaluate_mem_generated M t)

/-- Existing algebraic generatedness is exactly coverage by this independent
least fixed point, with no inhabitance or finiteness hypothesis. -/
theorem generated_iff_eq_top (M : EQ.Algebra A) :
    Presented.Characterization.Generated M ↔ generated M = ⊤ := by
  constructor
  · intro h
    funext s
    apply Set.ext
    intro x
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨t, rfl⟩ := h s x
      exact evaluate_mem_generated M t
  · intro h s x
    have hx : x ∈ generated M s := by
      rw [h]
      trivial
    change x ∈ (groundStep M).lfp s at hx
    rw [groundStep_lfp_eq_range M s] at hx
    exact hx

end Silmaril.Logic.Algebraic.Initial.Generation
