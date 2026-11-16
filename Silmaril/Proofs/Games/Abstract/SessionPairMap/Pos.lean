module

public import Silmaril.Games.Abstract.SessionPair.Defs

/-!
# Relabelling along `pairMove`: positions

`pairMove` changes only answers, so positions of the pairing game correspond to positions of the
paired session's game (`posMap`), and steps and paths are preserved (`step_map`, `path_map`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionPairMap

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratSession

universe u

variable {E : Sig.{u}} {A₁ A₂ B₁ B₂ : Type u}

/-- The same position, at the paired session's interface. -/
def posMap : Pos E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂) → Pos E (sig1 (A₁ ⊕ A₂) (B₁ ⊕ B₂))
  | .idle => .idle
  | .run a => .run a
  | .wait a m => .wait a m

theorem step_map {x y : Pos E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)} {o : Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)}
    (h : Step x o y) : Step (posMap x) (pairMove o) (posMap y) := by
  cases h with
  | ask => constructor
  | call => constructor
  | reply => constructor
  | ret q r => rcases q with q | q <;> exact Step.ret _ _

theorem path_map {x y : Pos E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)}
    {p : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))} (h : Path x p y) :
    Path (posMap x) (p.map pairMove) (posMap y) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (step_map h) ih

end Silmaril.Proofs.Games.Abstract.SessionPairMap
