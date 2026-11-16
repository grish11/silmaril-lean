module

public import Silmaril.Proofs.Logic.Temporal.Buchi.Automaton.Generalized.Counter

@[expose] public section
noncomputable section
open Classical
namespace Silmaril.Logic.Temporal.Buchi.Automaton.Generalized

/-- The compiled edge is exactly the original source guard and monitor update. -/
theorem compile_step {Atom : Type} {n k : Nat} (A : Symbolic Atom n k)
    (letter : Atom → Prop) (x y : Fin n × Fin (k+1)) :
    (A.compile.guard (stateEquiv n k x) (stateEquiv n k y)).Holds letter ↔
      (A.guard x.1 y.1).Holds letter ∧
        y.2 = advance (fun i => x.1 ∈ A.accepting i) x.2 := by
  simp only [Symbolic.compile, Equiv.symm_apply_apply]
  split <;> simp_all [Guard.Holds]

/-- Exact word language equivalence, with an independently defined coherent run. -/
theorem accepts_compile {Atom : Type} {n k : Nat} (A : Symbolic Atom n k)
    (word : Nat → Atom → Prop) : A.compile.automaton.Accepts word ↔ A.Accepts word := by
  constructor
  · show A.compile.automaton.Accepts word → A.Accepts word
    rintro ⟨s, hi, hs, hf⟩
    let r := fun t => ((stateEquiv n k).symm (s t)).1
    let c := fun t => ((stateEquiv n k).symm (s t)).2
    have hstep (t) : (A.guard (r t) (r (t+1))).Holds (word t) ∧
        c (t+1) = advance (fun i => r t ∈ A.accepting i) (c t) := by
      apply (compile_step A (word t) _ _).mp
      simpa only [Automaton.Symbolic.automaton, Equiv.apply_symm_apply] using hs t
    refine ⟨r, hi.1, fun t => (hstep t).1, ?_⟩
    exact (recurrent_iff (fun t i => r t ∈ A.accepting i) c (fun t => (hstep t).2)).mp hf
  · show A.Accepts word → A.compile.automaton.Accepts word
    rintro ⟨r, hi, hr, hf⟩
    let hit := fun t i => r t ∈ A.accepting i
    let c := counter hit
    refine ⟨fun t => stateEquiv n k (r t, c t), ?_, ?_, ?_⟩
    · change ((stateEquiv n k).symm (stateEquiv n k (r 0, c 0))).1 ∈ A.initial ∧
        ((stateEquiv n k).symm (stateEquiv n k (r 0, c 0))).2 = 0
      rw [Equiv.symm_apply_apply]
      exact ⟨hi, rfl⟩
    · intro t
      exact (compile_step A (word t) _ _).mpr ⟨hr t, rfl⟩
    · have hc : ∀ t, ∃ u, t ≤ u ∧ (c u).val = k :=
        (recurrent_iff hit c (fun _ => rfl)).mpr hf
      simpa only [Automaton.Recurrent, Symbolic.compile, Automaton.Symbolic.automaton,
        Set.mem_ofPred_eq, Equiv.symm_apply_apply] using hc

/-- The graph path is shared unchanged; the compiler adds only finite run state. -/
theorem acceptsPath_compile {Atom W : Type} {n k : Nat} (A : Symbolic Atom n k)
    (R : W → W → Prop) (label : W → Atom → Prop) (w : W) :
    A.compile.automaton.AcceptsPath R label w ↔ A.AcceptsPath R label w := by
  constructor
  · rintro ⟨p, hp, ha⟩
    exact ⟨p, hp, (accepts_compile A _).mp ha⟩
  · rintro ⟨p, hp, ha⟩
    exact ⟨p, hp, (accepts_compile A _).mpr ha⟩

/-- The emitted ordinary automaton commutes with arbitrary atom maps. -/
theorem compile_map {Atom Atom' : Type} {n k : Nat} (A : Symbolic Atom n k)
    (f : Atom → Atom') : (A.map f).compile = A.compile.map f := by
  unfold Symbolic.compile Symbolic.map Automaton.Symbolic.map
  congr 1
  funext x y
  dsimp only
  split <;> rfl

/-- Semantic pullback retains the same infinite-run witness, even when atoms merge. -/
theorem accepts_map {Atom Atom' : Type} {n k : Nat} (A : Symbolic Atom n k)
    (f : Atom → Atom') (word : Nat → Atom' → Prop) :
    (A.map f).Accepts word ↔ A.Accepts (fun t a => word t (f a)) := by
  simp only [Symbolic.Accepts, Symbolic.IsRun, Symbolic.Recurrent, Symbolic.map,
    Guard.holds_map, Function.comp_def]

/-- Zero fairness requirements accept precisely the infinite initial valid runs. -/
theorem accepts_zero {Atom : Type} {n : Nat} (A : Symbolic Atom n 0)
    (word : Nat → Atom → Prop) :
    A.Accepts word ↔ ∃ r, r 0 ∈ A.initial ∧ A.IsRun word r := by
  constructor
  · rintro ⟨r, hi, hr, _⟩
    exact ⟨r, hi, hr⟩
  · rintro ⟨r, hi, hr⟩
    exact ⟨r, hi, hr, fun i => Fin.elim0 i⟩

theorem not_accepts_zero_states {Atom : Type} {k : Nat} (A : Symbolic Atom 0 k)
    (word : Nat → Atom → Prop) : ¬ A.Accepts word := by
  rintro ⟨r, _, _, _⟩
  exact Fin.elim0 (r 0)

end Silmaril.Logic.Temporal.Buchi.Automaton.Generalized
