module

public import Silmaril.Wasm.Abstract.HostStrat.Defs

/-!
# Invocations against a host as canonical strategies (proofs)

`obsTriple_congr`: observation families that agree on the questions `Ok` give the same triple.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostStrat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type}

theorem obsTriple_congr {Ok : Store H → Nat × List Val → Prop}
    {O O' : Store H → Nat × List Val → FullObs H → Prop}
    (h : ∀ s q, Ok s q → ∀ x, O s q x ↔ O' s q x) : obsTriple Ok O = obsTriple Ok O' := by
  refine Prod.ext (funext fun s => funext fun q => Set.ext fun x => ?_)
    (Prod.ext (funext fun s => funext fun q => Set.ext fun x => ?_)
      (funext fun s => funext fun q => Set.ext fun x => ?_)) <;>
  simp only [obsTriple, Set.mem_ofPred_eq] <;>
  exact ⟨fun ⟨hq, hx⟩ => ⟨hq, by simpa only [h s q hq] using hx⟩,
    fun ⟨hq, hx⟩ => ⟨hq, by simpa only [h s q hq] using hx⟩⟩

end Silmaril.Proofs.Wasm.Abstract.HostStrat
