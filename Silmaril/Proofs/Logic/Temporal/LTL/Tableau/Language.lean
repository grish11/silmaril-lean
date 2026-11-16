module

public import Silmaril.Proofs.Logic.Temporal.LTL.Tableau.Completeness

@[expose] public section
noncomputable section
open Classical
namespace Silmaril.Logic.Temporal.LTL.Tableau
open Buchi.Automaton

/-- Exact packing bridge: finite automaton runs and Boolean occurrence runs
use the same time sequence and the same finite source guards. -/
theorem accepts_iff_run {Atom : Type} (p : NNF.Formula Atom) (word : Nat → Atom → Prop) :
    (automaton p).Accepts word ↔ ∃ run : Nat → State (shape p),
      bit (run 0) = true ∧ (∀ t, Local p (word t) (run t) (run (t+1))) ∧ Fair p run := by
  constructor
  · show (automaton p).Accepts word → _
    rintro ⟨r, hi, hr, hf⟩
    let run := fun t => (stateEquiv (shape p)).symm (r t)
    refine ⟨run, hi, ?_, ?_⟩
    · intro t
      exact (transition_holds p (word t) _ _).mp (hr t)
    · intro i t
      obtain ⟨u, hu, h⟩ := hf (occurrenceEquiv (shape p) i) t
      refine ⟨u, hu, ?_⟩
      change discharged p (run u) ((occurrenceEquiv (shape p)).symm
        (occurrenceEquiv (shape p) i)) at h
      simpa only [Equiv.symm_apply_apply] using h
  · show _ → (automaton p).Accepts word
    rintro ⟨run, hi, hr, hf⟩
    refine ⟨fun t => stateEquiv (shape p) (run t), ?_, ?_, ?_⟩
    · change bit ((stateEquiv (shape p)).symm (stateEquiv (shape p) (run 0))) = true
      simpa only [Equiv.symm_apply_apply] using hi
    · intro t
      change (transition p ((stateEquiv (shape p)).symm (stateEquiv (shape p) (run t)))
        ((stateEquiv (shape p)).symm (stateEquiv (shape p) (run (t+1))))).Holds (word t)
      simpa only [Equiv.symm_apply_apply] using (transition_holds p (word t) _ _).mpr (hr t)
    · intro i t
      obtain ⟨u, hu, h⟩ := hf ((occurrenceEquiv (shape p)).symm i) t
      refine ⟨u, hu, ?_⟩
      change discharged p ((stateEquiv (shape p)).symm (stateEquiv (shape p) (run u)))
        ((occurrenceEquiv (shape p)).symm i)
      simpa only [Equiv.symm_apply_apply] using h

/-- Full NNF word-language theorem, proved by active-bit soundness and a
canonical true-subformula assignment for completeness. -/
theorem accepts_iff {Atom : Type} (p : NNF.Formula Atom) (word : Nat → Atom → Prop) :
    (automaton p).Accepts word ↔ p.Holds word 0 := by
  rw [accepts_iff_run]
  constructor
  · rintro ⟨run, hi, hr, hf⟩
    exact active_sound p word run hr hf 0 hi
  · intro h
    exact ⟨truth p word, (truth_bit p word 0).mpr h, truth_local p word, truth_fair p word⟩

/-- All of the existing LTL grammar, including arbitrary temporal negation. -/
theorem accepts_normalize {Atom : Type} (p : LTL.Formula Atom) (M : LTL.Model Atom) :
    (automaton (NNF.normalize false p)).Accepts M.val ↔ p.Holds M 0 :=
  (accepts_iff _ _).trans (NNF.normalize_positive M p 0)

/-- Renaming atoms cannot change the finite occurrence-tree shape. -/
theorem shape_map {Atom Atom' : Type} (f : Atom → Atom') (p : NNF.Formula Atom) :
    shape (p.map f) = shape p := by
  induction p <;> simp_all [shape, NNF.Formula.map]

/-- Semantic naturality for arbitrary atom maps, including atom identification.
Both compiled automata use the same erased finite state shape. -/
theorem accepts_map {Atom Atom' : Type} (f : Atom → Atom') (p : NNF.Formula Atom)
    (word : Nat → Atom' → Prop) :
    (automaton (p.map f)).Accepts word ↔ (automaton p).Accepts (fun t a => word t (f a)) := by
  rw [accepts_iff, accepts_iff]
  exact NNF.Formula.holds_map f word p 0

end Silmaril.Logic.Temporal.LTL.Tableau
