module

public import Silmaril.Proofs.Wasm.Component.DWiringLaws.Inf

/-!
# Copycat beside a strategy: divergence and infinite plays

Copycat never diverges and has every infinite trace of its plays, so in a
pairing `(DStrategy.id E).pair N` only `N` constrains divergence
(`div_pair_id`) and infinite plays (`inf_pair_id`): the left projection of an
infinite trace of pairing plays is always an infinite play of copycat.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiringLaws

open Silmaril.Games Silmaril.Wasm.Component

universe u

variable {E F : Sig.{u}}

theorem div_pair_id (N : DStrategy E F) :
    ((DStrategy.id E).pair N).div =
      {a | a ∈ (Strategy.id E).pair N.toStrategy ∧ (Split.halves false a).2 ∈ N.div} := by
  ext a
  rw [DStrategy.mem_div_pair, DStrategy.div_id]
  simp only [Set.mem_empty_iff_false, false_or]
  rfl

theorem inf_pair_id (N : DStrategy E F) :
    ((DStrategy.id E).pair N).inf =
      {K | IsInfPlay K ∧ K ⊆ ((Strategy.id E).pair N.toStrategy).plays ∧
        (IsInfPlay (Split.infR K) → Split.infR K ∈ N.inf)} := by
  ext K
  rw [DStrategy.mem_inf_pair]
  constructor
  · rintro ⟨h₁, h₂, -, h₄⟩
    exact ⟨h₁, h₂, h₄⟩
  · rintro ⟨h₁, h₂, h₄⟩
    refine ⟨h₁, h₂, fun hL => DStrategy.mem_inf_id.2 ⟨hL, ?_⟩, h₄⟩
    rintro q ⟨p, hp, hq⟩
    exact (Strategy.id E).of_prefix (h₂ hp).2.1 hq

end Silmaril.Proofs.Wasm.Component.DWiringLaws
