module

public import Silmaril.Proofs.Logic.Temporal.CTLStar.FiniteTableau.Completeness

@[expose] public section
noncomputable section
open Classical
namespace Silmaril.Logic.Temporal.CTLStar.FiniteTableau
open LTL.Tableau

/-- Exact finite-word language, with the terminal letter consumed exactly once. -/
theorem accepts_iff {A : Type} (p : NNF.Formula A) (n : Nat) (word : Nat → A → Prop) :
    Accepts p n word ↔ p.Holds (some n) word 0 := by
  constructor
  · rintro ⟨run, initial, steps, last⟩
    exact (run_exact p n word run (fun t ht => (transition_holds _ _ _ _).mp (steps t ht))
      ((terminal_holds _ _ _).mp last) 0 (Nat.zero_le n)).mp initial
  · intro h
    refine ⟨truth p n word, (truth_bit _ _ _ _).mpr h, ?_, ?_⟩
    · intro t ht
      exact (transition_holds _ _ _ _).mpr (truth_local p n word t ht)
    · exact (terminal_holds _ _ _).mpr (truth_end p n word)

/-- The language theorem also reads actual existing finite maximal CTL* paths. -/
theorem accepts_path_iff {A : Type} {S : Signature} (leaf : A → StateFormula S)
    (M : Model S) (path : Path M.toModal.accessible) (p : NNF.Formula A)
    (n : Nat) (hlast : path.last = some n) :
    Accepts p n (fun t a => (leaf a).Holds M (path.state t)) ↔
      (p.toPathFormula leaf).Holds M path 0 := by
  rw [accepts_iff]
  rw [← hlast]
  exact p.holds_toPathFormula leaf M path 0 path.valid_zero

end Silmaril.Logic.Temporal.CTLStar.FiniteTableau
