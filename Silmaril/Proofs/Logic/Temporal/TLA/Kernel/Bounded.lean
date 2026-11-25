module

public import Silmaril.Logic.Temporal.TLA.Kernel.Defs

public section

namespace Silmaril.Proofs.Logic.Temporal.TLA.Kernel

open Silmaril.Logic.Temporal.TLA.Kernel

variable {Γ : Scope} {Node : Type}

theorem mem_transitions (domain : Bounded Γ Node) (ρ : RigidEnv Γ)
    (step : StepPredicate Γ) (src dst : Node) :
    (src, dst) ∈ domain.transitions ρ step ↔
      src ∈ domain.states ∧ dst ∈ domain.states ∧
        step.toAction ρ (domain.valuation src) (domain.valuation dst) := by
  simp only [Bounded.transitions, List.mem_flatMap, List.mem_map, List.mem_filter, Prod.mk.injEq]
  have checked := @decide_eq_true_iff _ (step.decision ρ (domain.valuation src, domain.valuation dst))
  exact ⟨fun ⟨_, hs, _, ⟨ht, h⟩, rfl, rfl⟩ => ⟨hs, ht, checked.mp h⟩,
    fun ⟨hs, ht, h⟩ => ⟨src, hs, dst, ⟨ht, checked.mpr h⟩, rfl, rfl⟩⟩

end Silmaril.Proofs.Logic.Temporal.TLA.Kernel
