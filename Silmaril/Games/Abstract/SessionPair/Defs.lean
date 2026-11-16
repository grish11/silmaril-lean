module

public import Silmaril.Games.Abstract.StratSession.Defs

/-!
# Pairing sessions: two independent store-retaining triples side by side

Two store-retaining triples `t₁ : ObsTriple E S₁ A₁ (B₁ ⊕ PUnit)` and
`t₂ : ObsTriple E S₂ A₂ (B₂ ⊕ PUnit)` (`StratSession`) sharing the lower
interface `E` give the **paired triple**
`pairS t₁ t₂ : ObsTriple E (S₁ × S₂) (A₁ ⊕ A₂) ((B₁ ⊕ B₂) ⊕ PUnit)`. A round on
`.inl a₁` is a round of `t₁` at `(s₁, a₁)` on the first store, keeping the
second store; its value `.inl b₁` is shown as `.inl (.inl b₁)` and its
continuing trap as `.inr ()` (`pairEndL`). Rounds on `.inr a₂` are symmetric. Pending
calls and productive streams are those of the component of the question.

**Relabelling.** The session of the paired triple
(`threadS (pairS t₁ t₂) (s₁, s₂)`) and the pairing (`DStrategy.pair`) of the
two sessions `threadS t₁ s₁` and `threadS t₂ s₂` live on different interfaces,
`sig1 (A₁ ⊕ A₂) (B₁ ⊕ B₂)` and `sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂`, with the same
questions; `pairMove` relabels the answers of the latter (`x ↦ Sum.map .inl id x`
on the left, and `.inr` on the right). It is injective on moves.

Theorems in `Silmaril.Games.Abstract.SessionPair.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.StratSession

open Silmaril.Games

universe u

variable {E : Sig.{u}} {S₁ S₂ A₁ A₂ B₁ B₂ : Type u}

/-- The end of a left round in the paired triple: the second store is kept. -/
def pairEndL (s₂ : S₂) : End S₁ (B₁ ⊕ PUnit.{u + 1}) → End (S₁ × S₂) ((B₁ ⊕ B₂) ⊕ PUnit.{u + 1})
  | .ret x s => .ret (Sum.map .inl id x) (s, s₂)
  | .trap => .trap
  | .div => .div

/-- The end of a right round in the paired triple: the first store is kept. -/
def pairEndR (s₁ : S₁) : End S₂ (B₂ ⊕ PUnit.{u + 1}) → End (S₁ × S₂) ((B₁ ⊕ B₂) ⊕ PUnit.{u + 1})
  | .ret x s => .ret (Sum.map .inr id x) (s₁, s)
  | .trap => .trap
  | .div => .div

/-- **The paired triple**: a round on `.inl a₁` is a round of `t₁` on the first store, a round on
`.inr a₂` is a round of `t₂` on the second store. -/
def pairS (t₁ : ObsTriple E S₁ A₁ (B₁ ⊕ PUnit.{u + 1}))
    (t₂ : ObsTriple E S₂ A₂ (B₂ ⊕ PUnit.{u + 1})) :
    ObsTriple E (S₁ × S₂) (A₁ ⊕ A₂) ((B₁ ⊕ B₂) ⊕ PUnit.{u + 1}) :=
  (fun σ => Sum.elim (fun a => (fun x => (x.1, pairEndL σ.2 x.2)) '' t₁.1 σ.1 a)
      (fun a => (fun x => (x.1, pairEndR σ.1 x.2)) '' t₂.1 σ.2 a),
    fun σ => Sum.elim (t₁.2.1 σ.1) (t₂.2.1 σ.2),
    fun σ => Sum.elim (t₁.2.2 σ.1) (t₂.2.2 σ.2))

/-- Relabel a move of the pairing of two sessions as a move of the paired session: an answer
`x` to `.inl a₁` is `Sum.map .inl id x`, an answer to `.inr a₂` is `Sum.map .inr id x`. -/
def pairMove : Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂) → Move E (sig1 (A₁ ⊕ A₂) (B₁ ⊕ B₂))
  | .inl e => .inl e
  | .inr (.ask a) => .inr (.ask a)
  | .inr (.ans (.inl a) x) => .inr (.ans (.inl a) (Sum.map .inl id (x : B₁ ⊕ PUnit.{u + 1})))
  | .inr (.ans (.inr a) x) => .inr (.ans (.inr a) (Sum.map .inr id (x : B₂ ⊕ PUnit.{u + 1})))

end Silmaril.Games.Abstract.StratSession
