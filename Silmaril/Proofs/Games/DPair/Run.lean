module

public import Silmaril.Games.Pair.Defs

/-!
# Pairing divergence-observing strategies: the running side

A half of a play of `E ↠ F₁ ⊕ₛ F₂` that ends running ends running on the
current side, and the play itself runs the same question
(`run_of_halves_left`, `run_of_halves_right`). This is the `div_run` field of
`DStrategy.pair`.
-/

public section

namespace Silmaril.Proofs.Games.DPair

open Silmaril.Games

universe u

variable {E F₁ F₂ : Sig.{u}}

/-- If the left half of a legal play runs `q`, the play runs `.inl q` on the left side. -/
theorem run_of_halves_left {p : List (Move E (F₁ ⊕ₛ F₂))} (hp : Legal p) {q : F₁.Op}
    (h : Path .idle (Split.halves false p).1 (.run q)) :
    Split.side false p = false ∧ Path .idle p (.run (.inl q)) := by
  obtain ⟨y, hy⟩ := hp
  obtain ⟨y₁, y₂, h₁, -, hr⟩ := Split.halves_path hy (Split.Rel.idle false)
  cases Path.det h₁ h
  generalize hb : Split.side false p = b at hr
  cases hr
  exact ⟨rfl, hy⟩

/-- If the right half of a legal play runs `q`, the play runs `.inr q` on the right side. -/
theorem run_of_halves_right {p : List (Move E (F₁ ⊕ₛ F₂))} (hp : Legal p) {q : F₂.Op}
    (h : Path .idle (Split.halves false p).2 (.run q)) :
    Split.side false p = true ∧ Path .idle p (.run (.inr q)) := by
  obtain ⟨y, hy⟩ := hp
  obtain ⟨y₁, y₂, -, h₂, hr⟩ := Split.halves_path hy (Split.Rel.idle false)
  cases Path.det h₂ h
  generalize hb : Split.side false p = b at hr
  cases hr
  exact ⟨rfl, hy⟩

end Silmaril.Proofs.Games.DPair
