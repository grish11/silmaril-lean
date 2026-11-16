module

public import Silmaril.Games.Pair.Defs
public import Silmaril.Games.Div.Defs
import Silmaril.Proofs.Games.DPair.Run

/-!
# Pairing divergence-observing strategies

`σ₁.pair σ₂ : DStrategy E (F₁ ⊕ₛ F₂)` for `σ₁ : DStrategy E F₁` and
`σ₂ : DStrategy E F₂` extends `Strategy.pair` (`Silmaril.Games.Pair.Defs`) to
divergence and infinite plays. The finite plays are those of
`Strategy.pair σ₁.toStrategy σ₂.toStrategy`: the legal plays whose halves
(`Split.halves false`) are plays of the components. Rounds never overlap, so at
most one component is active at a time.

* **Divergence.** A play diverges when one of its halves is a divergent play of
  its component. Divergent plays end running, so that half is the one of the
  active component (the current side, `Split.side`), and the other half is idle
  (`DStrategy.mem_div_pair_iff` in `Thms`).
* **Infinite plays.** An infinite play `I` of the pairing is an infinite trace
  of finite plays whose *projections* are allowed by the components. The left
  projection `Split.infL I` is the set of prefixes of the left halves of the
  members of `I`, and similarly `Split.infR I`. A projection is either an
  infinite trace (the component moves forever) or bounded (the component stops,
  in one of its finite plays). The pairing requires every infinite projection to
  be an infinite play of its component. Since a play is as long as its two
  halves together, at least one projection of an infinite play is infinite
  (`Split.isInfPlay_infL_or_infR`): an infinite play of a pairing comes from an
  infinite play of a component, interleaved with finitely or infinitely many
  rounds of the other.

`Split.liftL` and `Split.liftR` embed the moves of one side into the pairing;
they send plays, divergences and infinite plays of a component to those of the
pairing (`Thms`).
-/

@[expose] public section

namespace Silmaril.Games

universe u

variable {E F₁ F₂ : Sig.{u}}

namespace Split

/-- The left projection of a set of plays: the prefixes of the left halves. -/
def infL (I : Set (List (Move E (F₁ ⊕ₛ F₂)))) : Set (List (Move E F₁)) :=
  {s | ∃ p ∈ I, s <+: (halves false p).1}

/-- The right projection of a set of plays: the prefixes of the right halves. -/
def infR (I : Set (List (Move E (F₁ ⊕ₛ F₂)))) : Set (List (Move E F₂)) :=
  {s | ∃ p ∈ I, s <+: (halves false p).2}

/-- A move of the left component as a move of the pairing. -/
def liftL : Move E F₁ → Move E (F₁ ⊕ₛ F₂)
  | .inl e => .inl e
  | .inr (.ask q) => .inr (.ask (.inl q))
  | .inr (.ans q r) => .inr (.ans (.inl q) r)

/-- A move of the right component as a move of the pairing. -/
def liftR : Move E F₂ → Move E (F₁ ⊕ₛ F₂)
  | .inl e => .inl e
  | .inr (.ask q) => .inr (.ask (.inr q))
  | .inr (.ans q r) => .inr (.ans (.inr q) r)

end Split

namespace DStrategy

/-- **The pairing of divergence-observing strategies**: the finite plays of
`Strategy.pair`; a play diverges when a half diverges; an infinite play has its
infinite projections among the infinite plays of the components. -/
def pair (σ₁ : DStrategy E F₁) (σ₂ : DStrategy E F₂) : DStrategy E (F₁ ⊕ₛ F₂) where
  toStrategy := σ₁.toStrategy.pair σ₂.toStrategy
  div := {p | p ∈ σ₁.toStrategy.pair σ₂.toStrategy ∧
    ((Split.halves false p).1 ∈ σ₁.div ∨ (Split.halves false p).2 ∈ σ₂.div)}
  inf := {I | IsInfPlay I ∧ I ⊆ (σ₁.toStrategy.pair σ₂.toStrategy).plays ∧
    (IsInfPlay (Split.infL I) → Split.infL I ∈ σ₁.inf) ∧
    (IsInfPlay (Split.infR I) → Split.infR I ∈ σ₂.inf)}
  div_mem h := h.1
  div_run := by
    rintro p ⟨hp, h | h⟩
    · obtain ⟨q, hq⟩ := σ₁.div_run h
      exact ⟨_, (Silmaril.Proofs.Games.DPair.run_of_halves_left hp.1 hq).2⟩
    · obtain ⟨q, hq⟩ := σ₂.div_run h
      exact ⟨_, (Silmaril.Proofs.Games.DPair.run_of_halves_right hp.1 hq).2⟩
  inf_isInf h := h.1
  inf_sub h := h.2.1

end DStrategy

end Silmaril.Games
