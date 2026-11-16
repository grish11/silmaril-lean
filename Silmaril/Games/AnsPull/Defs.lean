module

public import Silmaril.Games.AnsMap.Defs
public import Silmaril.Games.DPull.Defs

/-!
# Relabelling answers below a strategy

`Silmaril.Games.AnsMap` relabels the answers a strategy *gives* (`DStrategy.mapAns`, composition
with `ansH k` above). This module relabels the answers a strategy *receives*: for a lower
interface `E` and answer types `B' : E.Op → Type`, a strategy `τ` over `⟨E.Op, B'⟩` reads, through
`k q : E.Ar q → B' q`, a lower answer `n` to `q` as `k q n`.

* `lowMove k : Move E G → Move ⟨E.Op, B'⟩ G`: a lower answer `n` to `q` becomes `k q n`;
  everything else is unchanged. `posLow` is the same position at the relabelled interface.
  They are compatible with the legality automata (`pullData_lowMove`), as are `ansMove k` and
  `posAns` (`pullData_ansMove`).
* `DStrategy.pullAns k τ : DStrategy E G`: the plays, divergences and infinite plays whose lower
  relabellings are those of `τ` (`DStrategy.pull` along `lowMove k`). `k` need not be injective.
* `sumAns k₁ k₂`: the relabelling of the answers of a sum, side by side.

`Silmaril.Games.AnsPull.Thms` shows that composing with `ansH k` *below* is `pullAns k`, that
pulling distributes over pairing, and derives the handler laws on divergence-observing
strategies for relabelling handlers (below and above a pairing, below and above another handler,
and cancellation of inverse relabellings).
-/

@[expose] public section

namespace Silmaril.Games

universe u

variable {E G : Sig.{u}} {B' : E.Op → Type u}

/-- Relabel the answer of a lower move along `k`; other moves are unchanged. -/
def lowMove (k : (q : E.Op) → E.Ar q → B' q) : Move E G → Move (Sig.mk E.Op B') G
  | .inl (.ask q) => .inl (.ask q)
  | .inl (.ans q n) => .inl (.ans q (k q n))
  | .inr o => .inr o

/-- The same position, at the relabelled lower interface. -/
def posLow : Pos E G → Pos (Sig.mk E.Op B') G
  | .idle => .idle
  | .run g => .run g
  | .wait g q => .wait g q

/-- The lower relabelling is compatible with the legality automata. -/
theorem pullData_lowMove (k : (q : E.Op) → E.Ar q → B' q) :
    PullData (lowMove (G := G) k) posLow where
  idle := rfl
  step h := by cases h <;> constructor
  lift {x o _} h := by
    rcases o with (q | ⟨q, n⟩) | (q | ⟨q, n⟩) <;> cases x <;> cases h <;> exact ⟨_, by constructor⟩
  run {x _} h := by cases x <;> simp [posLow] at h ⊢

/-- The upper relabelling is compatible with the legality automata. -/
theorem pullData_ansMove {F : Sig.{u}} {B : F.Op → Type u} (k : (q : F.Op) → F.Ar q → B q) :
    PullData (ansMove (E := E) k) posAns where
  idle := rfl
  step h := step_ans k h
  lift {x o _} h := by
    rcases o with (q | ⟨q, n⟩) | (q | ⟨q, n⟩) <;> cases x <;> cases h <;> exact ⟨_, by constructor⟩
  run {x _} h := by cases x <;> simp [posAns] at h ⊢

/-- **Relabel the answers received from below** along `k`: the plays, divergences and infinite
plays whose lower relabellings are those of `τ`. -/
def DStrategy.pullAns (k : (q : E.Op) → E.Ar q → B' q) (τ : DStrategy (Sig.mk E.Op B') G) :
    DStrategy E G :=
  τ.pull (lowMove k) posLow (pullData_lowMove k)

/-- The answers of a sum relabelled side by side. -/
def sumAns {F₁ F₂ : Sig.{u}} {B₁ : F₁.Op → Type u} {B₂ : F₂.Op → Type u}
    (k₁ : (q : F₁.Op) → F₁.Ar q → B₁ q) (k₂ : (q : F₂.Op) → F₂.Ar q → B₂ q) :
    (a : (F₁ ⊕ₛ F₂).Op) → (F₁ ⊕ₛ F₂).Ar a → (Sig.mk F₁.Op B₁ ⊕ₛ Sig.mk F₂.Op B₂).Ar a
  | .inl q, n => k₁ q n
  | .inr q, n => k₂ q n

end Silmaril.Games
