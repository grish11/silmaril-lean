module

public import Silmaril.Games.Abstract.SessionLinkCex.Defs
public import Silmaril.Games.Abstract.StratSession.Defs

/-!
# Linking counterexamples: shared facts

Constant streams are replicated lists, and the moves of replicated rounds and calls.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.SessionLinkCex

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession

theorem streamTake_const {α : Type} (x : α) (n : ℕ) :
    streamTake (fun _ => x) n = List.replicate n x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, ← ih]; simp [streamTake, List.ofFn_succ]

theorem streamTake_succ {α : Type} (ω : ℕ → α) (n : ℕ) :
    streamTake ω (n + 1) = ω 0 :: streamTake (fun i => ω (i + 1)) n := by
  simp [streamTake, List.ofFn_succ]

theorem rounds_cons_iff {E : Sig.{0}} {S A B : Type} {t : ObsTriple E S A B} {s s₂ : S}
    {x : A × List (Call E) × B} {rs : List (A × List (Call E) × B)} :
    Rounds t s (x :: rs) s₂ ↔ ∃ s₁, (x.2.1, End.ret x.2.2 s₁) ∈ t.1 s x.1 ∧ Rounds t s₁ rs s₂ := by
  constructor
  · rintro (_ | ⟨h, hr⟩)
    exact ⟨_, h, hr⟩
  · rintro ⟨_, h, hr⟩
    exact .cons h hr

theorem rounds_nil_iff {E : Sig.{0}} {S A B : Type} {t : ObsTriple E S A B} {s s₂ : S} :
    Rounds t s [] s₂ ↔ s = s₂ :=
  ⟨by rintro ⟨⟩; rfl, by rintro rfl; exact .nil _⟩

end Silmaril.Proofs.Games.Abstract.SessionLinkCex
