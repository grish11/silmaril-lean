module

public import Silmaril.Proofs.Wasm.Component.DWiringChatter3.Top

/-!
# Infinite plays of `ext`, routed

`ext e D N = D.comp (extTop e N)`; `inf_comp_eq` reads its infinite plays as
runs of `D` and `extTop e N` interleaved, and `isRun_extTop_iff` reads the runs
of `extTop e N` through `splitRoute e`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiringChatter3

open Silmaril.Games Silmaril.Wasm.Component

/-- **Infinite plays of `ext`, routed.** -/
theorem inf_ext_routed {X : Sig.{0}} (e : Nat) (D : DStrategy X sigU) (N : DStrategy sigU sigU) :
    (DStrategy.ext e D N).inf = {J | IsInfPlay J ∧ ∃ I C,
      (I ∈ D.inf ∨ ∃ s₀ ∈ D.toStrategy, I = prefixes s₀) ∧
      (IsInfPlay C ∨ ∃ c₀, C = prefixes c₀) ∧
      (∀ c ∈ C, Legal c ∧ c.map (splitRoute e) ∈ (Strategy.id sigU).pair N.toStrategy) ∧
      (IsInfPlay (Split.infR (List.map (splitRoute e) '' C)) →
        Split.infR (List.map (splitRoute e) '' C) ∈ N.inf) ∧
      Interleaved I C J} := by
  rw [DStrategy.ext_eq_comp, inf_comp_eq]
  ext J
  refine and_congr_right fun _ => exists_congr fun I => exists_congr fun C => ?_
  rw [isRun_extTop_iff]
  exact ⟨fun ⟨h₁, ⟨h₂, h₃, h₄⟩, h₅⟩ => ⟨h₁, h₂, h₃, h₄, h₅⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅⟩ => ⟨h₁, ⟨h₂, h₃, h₄⟩, h₅⟩⟩

end Silmaril.Proofs.Wasm.Component.DWiringChatter3
