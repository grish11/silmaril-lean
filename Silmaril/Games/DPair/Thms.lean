module

public import Silmaril.Games.DPair.Defs
import Silmaril.Proofs.Games.DPair.Basic

/-!
# Pairing divergence-observing strategies: theorems

* The finite plays are those of `Strategy.pair` (`toStrategy_pair`, `rfl`).
* **Divergence** (`mem_div_pair_iff`): a play of the pairing diverges iff the
  component of the current side (`Split.side false p`) diverges on its half.
* **Infinite plays** (`mem_inf_pair`): an infinite trace of plays whose infinite
  projections are infinite plays of the components. Every infinite trace has an
  infinite projection (`Split.isInfPlay_infL_or_infR`); a projection is infinite
  iff its halves are unbounded (`Split.isInfPlay_infL_iff`).
* **Lifting a side**: plays, divergences and infinite plays of a component,
  lifted along `Split.liftL`/`Split.liftR`, are those of the pairing
  (`mem_pair_map_liftL`, `div_map_liftL`, `inf_map_liftL`, and the right
  versions).
* The pairing is monotone (`pair_mono`), and the pairing of the least readings
  is the least reading of the pairing (`pair_ofStrategy`).

Proofs are in `Silmaril.Proofs.Games.DPair`.
-/

public section

namespace Silmaril.Games

universe u

variable {E F₁ F₂ : Sig.{u}}

namespace Split

/-- A play is as long as its two halves together. -/
theorem halves_length (b : Bool) (p : List (Move E (F₁ ⊕ₛ F₂))) :
    (halves b p).1.length + (halves b p).2.length = p.length :=
  Silmaril.Proofs.Games.DPair.halves_length b p

/-- The left projection of an infinite trace is infinite iff its left halves are unbounded. -/
theorem isInfPlay_infL_iff {I : Set (List (Move E (F₁ ⊕ₛ F₂)))} (hI : IsInfPlay I) :
    IsInfPlay (infL I) ↔ ∀ k, ∃ p ∈ I, k ≤ (halves false p).1.length :=
  Silmaril.Proofs.Games.DPair.isInfPlay_infL_iff hI

/-- The right projection of an infinite trace is infinite iff its right halves are unbounded. -/
theorem isInfPlay_infR_iff {I : Set (List (Move E (F₁ ⊕ₛ F₂)))} (hI : IsInfPlay I) :
    IsInfPlay (infR I) ↔ ∀ k, ∃ p ∈ I, k ≤ (halves false p).2.length :=
  Silmaril.Proofs.Games.DPair.isInfPlay_infR_iff hI

/-- **An infinite trace has an infinite projection.** -/
theorem isInfPlay_infL_or_infR {I : Set (List (Move E (F₁ ⊕ₛ F₂)))} (hI : IsInfPlay I) :
    IsInfPlay (infL I) ∨ IsInfPlay (infR I) :=
  Silmaril.Proofs.Games.DPair.isInfPlay_infL_or_infR hI

end Split

namespace DStrategy

/-- The finite plays of a pairing are those of the pairing of finite plays. -/
@[simp] theorem toStrategy_pair (σ₁ : DStrategy E F₁) (σ₂ : DStrategy E F₂) :
    (σ₁.pair σ₂).toStrategy = σ₁.toStrategy.pair σ₂.toStrategy := rfl

/-- The finite plays of a pairing are those of the pairing of finite plays. -/
@[simp] theorem forget_pair (σ₁ : DStrategy E F₁) (σ₂ : DStrategy E F₂) :
    (σ₁.pair σ₂).forget = σ₁.forget.pair σ₂.forget := rfl

/-- The divergent plays of a pairing: plays with a divergent half. -/
theorem mem_div_pair {σ₁ : DStrategy E F₁} {σ₂ : DStrategy E F₂}
    {p : List (Move E (F₁ ⊕ₛ F₂))} :
    p ∈ (σ₁.pair σ₂).div ↔ p ∈ σ₁.toStrategy.pair σ₂.toStrategy ∧
      ((Split.halves false p).1 ∈ σ₁.div ∨ (Split.halves false p).2 ∈ σ₂.div) := Iff.rfl

/-- **A play of a pairing diverges iff the active component diverges on its half.** -/
theorem mem_div_pair_iff {σ₁ : DStrategy E F₁} {σ₂ : DStrategy E F₂}
    {p : List (Move E (F₁ ⊕ₛ F₂))} :
    p ∈ (σ₁.pair σ₂).div ↔ p ∈ σ₁.toStrategy.pair σ₂.toStrategy ∧
      ((Split.side false p = false ∧ (Split.halves false p).1 ∈ σ₁.div) ∨
        (Split.side false p = true ∧ (Split.halves false p).2 ∈ σ₂.div)) :=
  Silmaril.Proofs.Games.DPair.mem_div_pair_iff

/-- **The infinite plays of a pairing**: infinite traces of plays whose infinite projections are
infinite plays of the components. -/
theorem mem_inf_pair {σ₁ : DStrategy E F₁} {σ₂ : DStrategy E F₂}
    {I : Set (List (Move E (F₁ ⊕ₛ F₂)))} :
    I ∈ (σ₁.pair σ₂).inf ↔ IsInfPlay I ∧ I ⊆ (σ₁.toStrategy.pair σ₂.toStrategy).plays ∧
      (IsInfPlay (Split.infL I) → Split.infL I ∈ σ₁.inf) ∧
      (IsInfPlay (Split.infR I) → Split.infR I ∈ σ₂.inf) := Iff.rfl

/-- An infinite play of a pairing has an infinite projection, an infinite play of its
component. -/
theorem exists_inf_of_mem_inf_pair {σ₁ : DStrategy E F₁} {σ₂ : DStrategy E F₂}
    {I : Set (List (Move E (F₁ ⊕ₛ F₂)))} (h : I ∈ (σ₁.pair σ₂).inf) :
    Split.infL I ∈ σ₁.inf ∨ Split.infR I ∈ σ₂.inf :=
  (Split.isInfPlay_infL_or_infR h.1).imp h.2.2.1 h.2.2.2

/-- A lifted play of the left component is a play of the pairing. -/
theorem mem_pair_map_liftL {σ₁ : DStrategy E F₁} (σ₂ : DStrategy E F₂) {s : List (Move E F₁)}
    (hs : s ∈ σ₁.toStrategy) : s.map (Split.liftL (F₂ := F₂)) ∈ (σ₁.pair σ₂).toStrategy :=
  Silmaril.Proofs.Games.DPair.mem_pair_map_liftL σ₂.toStrategy hs

/-- A lifted play of the right component is a play of the pairing. -/
theorem mem_pair_map_liftR (σ₁ : DStrategy E F₁) {σ₂ : DStrategy E F₂} {s : List (Move E F₂)}
    (hs : s ∈ σ₂.toStrategy) : s.map (Split.liftR (F₁ := F₁)) ∈ (σ₁.pair σ₂).toStrategy :=
  Silmaril.Proofs.Games.DPair.mem_pair_map_liftR σ₁.toStrategy hs

/-- A lifted divergence of the left component is a divergence of the pairing. -/
theorem div_map_liftL {σ₁ : DStrategy E F₁} (σ₂ : DStrategy E F₂) {s : List (Move E F₁)}
    (hs : s ∈ σ₁.div) : s.map (Split.liftL (F₂ := F₂)) ∈ (σ₁.pair σ₂).div :=
  Silmaril.Proofs.Games.DPair.div_map_liftL σ₂ hs

/-- A lifted divergence of the right component is a divergence of the pairing. -/
theorem div_map_liftR (σ₁ : DStrategy E F₁) {σ₂ : DStrategy E F₂} {s : List (Move E F₂)}
    (hs : s ∈ σ₂.div) : s.map (Split.liftR (F₁ := F₁)) ∈ (σ₁.pair σ₂).div :=
  Silmaril.Proofs.Games.DPair.div_map_liftR σ₁ hs

/-- A lifted infinite play of the left component is an infinite play of the pairing. -/
theorem inf_map_liftL {σ₁ : DStrategy E F₁} (σ₂ : DStrategy E F₂) {I : Set (List (Move E F₁))}
    (hI : I ∈ σ₁.inf) : List.map (Split.liftL (F₂ := F₂)) '' I ∈ (σ₁.pair σ₂).inf :=
  Silmaril.Proofs.Games.DPair.inf_map_liftL σ₁ σ₂ hI

/-- A lifted infinite play of the right component is an infinite play of the pairing. -/
theorem inf_map_liftR (σ₁ : DStrategy E F₁) {σ₂ : DStrategy E F₂} {I : Set (List (Move E F₂))}
    (hI : I ∈ σ₂.inf) : List.map (Split.liftR (F₁ := F₁)) '' I ∈ (σ₁.pair σ₂).inf :=
  Silmaril.Proofs.Games.DPair.inf_map_liftR σ₁ σ₂ hI

/-- Pairing is monotone. -/
theorem pair_mono {σ₁ τ₁ : DStrategy E F₁} {σ₂ τ₂ : DStrategy E F₂} (h₁ : σ₁ ≤ τ₁)
    (h₂ : σ₂ ≤ τ₂) : σ₁.pair σ₂ ≤ τ₁.pair τ₂ :=
  Silmaril.Proofs.Games.DPair.pair_mono h₁ h₂

/-- **Pairing the least readings** (no divergence, no infinite play) gives the least reading of
the pairing. -/
theorem pair_ofStrategy (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    (ofStrategy σ₁).pair (ofStrategy σ₂) = ofStrategy (σ₁.pair σ₂) :=
  Silmaril.Proofs.Games.DPair.pair_ofStrategy σ₁ σ₂

end DStrategy

end Silmaril.Games
