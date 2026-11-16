module

public import Silmaril.Games.DivCompChatter.Defs
public import Silmaril.Games.DivComp.Thms
import Silmaril.Proofs.Games.DivCompChatter.Basic

/-!
# Hidden chatter of a composite

The divergences of `σ.comp τ` (`DStrategy.mem_div_comp`) include *hidden
chatter*: an infinite interaction `i : InfInteraction σ τ` whose visible part
stays `p`. This module characterises it by the components' own infinite plays.

* **Chatter is a pair of infinite plays chattering** (`InfInteraction.chatter_iff`):
  such an interaction exists iff there are `I ∈ σ.inf` and `J ∈ τ.inf` with
  `Chatter I J p`, i.e. arbitrarily long members of `I` and `J` interact with
  visible part `p`. Forwards, both sides of a chattering interaction move
  forever (`InfInteraction.chatter_inf`), and their limits are `I` and `J`.
  Backwards, the interacting pairs are chosen ever longer; with the visible
  part fixed, the two sides of an interaction differ in length by a fixed
  amount, so both sides grow, and since `I` and `J` are totally ordered by the
  prefix order the chosen pairs form increasing chains converging to `I` and
  `J`.
* **Nested composites** (`chatter_comp_right_iff`, `chatter_comp_left_iff`):
  chatter of `σ` with `τ.comp ρ` is an infinite play of `σ` chattering with the
  visible limit of an infinite interaction of `τ` and `ρ`, and symmetrically.
  The visible part of that inner interaction necessarily grows forever, as
  `mem_inf_comp` requires. When `ρ` makes `τ` move whenever the visible play
  grows (e.g. a handler on top that always calls), the inner interaction also
  plays an infinite play of `τ` (`chatter_comp_right_iff_of_moves`).
* Hence the divergences of a composite, with hidden chatter in closed form
  (`div_comp_eq`).

Proofs are in `Silmaril.Proofs.Games.DivCompChatter`.
-/

public section

namespace Silmaril.Games.DStrategy

universe u

variable {E F G H : Sig.{u}}

/-- **Hidden chatter, characterised by the components' infinite plays.** An
infinite interaction of `σ` and `τ` whose visible part stays `p` exists iff an
infinite play of `σ` and an infinite play of `τ` chatter after `p`. -/
theorem InfInteraction.chatter_iff {σ : DStrategy E F} {τ : DStrategy F G}
    {p : List (Move E G)} :
    (∃ i : InfInteraction σ τ, ∀ m, i.p m = p) ↔ ∃ I ∈ σ.inf, ∃ J ∈ τ.inf, Chatter I J p :=
  Silmaril.Proofs.Games.DivCompChatter.chatter_iff

/-- Two chattering infinite plays make the composite diverge. -/
theorem mem_div_comp_of_chatter_inf {σ : DStrategy E F} {τ : DStrategy F G}
    {p : List (Move E G)} {I : Set (List (Move E F))} (hI : I ∈ σ.inf)
    {J : Set (List (Move F G))} (hJ : J ∈ τ.inf) (h : Chatter I J p) : p ∈ (σ.comp τ).div :=
  .inr (InfInteraction.chatter_iff.2 ⟨I, hI, J, hJ, h⟩)

/-- **Divergence of a composite**, with hidden chatter in terms of the
components' infinite plays. -/
theorem div_comp_eq (σ : DStrategy E F) (τ : DStrategy F G) :
    (σ.comp τ).div =
      {p | ∃ s t, Zip s t p ∧ ((s ∈ σ.div ∧ t ∈ τ.toStrategy) ∨ (s ∈ σ.toStrategy ∧ t ∈ τ.div))} ∪
      {p | ∃ I ∈ σ.inf, ∃ J ∈ τ.inf, Chatter I J p} := by
  ext p
  exact mem_div_comp.trans (or_congr Iff.rfl InfInteraction.chatter_iff)

/-- **Hidden chatter with a composite on the right.** -/
theorem chatter_comp_right_iff {σ : DStrategy E F} {τ : DStrategy F G} {ρ : DStrategy G H}
    {p : List (Move E H)} :
    (∃ i : InfInteraction σ (τ.comp ρ), ∀ m, i.p m = p) ↔
      ∃ I ∈ σ.inf, ∃ j : InfInteraction τ ρ, Chatter I j.p.lim p :=
  Silmaril.Proofs.Games.DivCompChatter.chatter_comp_right_iff

/-- **Hidden chatter with a composite on the left.** -/
theorem chatter_comp_left_iff {σ : DStrategy E F} {τ : DStrategy F G} {ρ : DStrategy G H}
    {p : List (Move E H)} :
    (∃ i : InfInteraction (σ.comp τ) ρ, ∀ m, i.p m = p) ↔
      ∃ j : InfInteraction σ τ, ∃ K ∈ ρ.inf, Chatter j.p.lim K p :=
  Silmaril.Proofs.Games.DivCompChatter.chatter_comp_left_iff

/-- **Hidden chatter with a composite on the right, through an upper component
that makes the lower one move** whenever the visible play grows: the lower
component plays one of its infinite plays. -/
theorem chatter_comp_right_iff_of_moves {σ : DStrategy E F} {τ : DStrategy F G}
    {ρ : DStrategy G H} (hρ : ∀ j : InfInteraction τ ρ, j.p.Unbounded → j.s.Unbounded)
    {p : List (Move E H)} :
    (∃ i : InfInteraction σ (τ.comp ρ), ∀ m, i.p m = p) ↔
      ∃ I ∈ σ.inf, ∃ j : InfInteraction τ ρ, j.s.Unbounded ∧ j.s.lim ∈ τ.inf ∧
        Chatter I j.p.lim p :=
  Silmaril.Proofs.Games.DivCompChatter.chatter_comp_right_iff_of_moves hρ

end Silmaril.Games.DStrategy
