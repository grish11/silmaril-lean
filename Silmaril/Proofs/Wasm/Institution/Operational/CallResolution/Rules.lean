module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Proofs

open Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution.Runtime (FuncAddr)

theorem invert {fs : List FuncAddr} {src dst : State} (edge : Edge fs src dst) :
    ∃ i a, src = .call i ∧ dst = .invoke a ∧ fs[i.toNat]? = some a := by
  refine Derives.least (M := fun j : Judgment =>
    ∃ i a, j.1 = .call i ∧ j.2 = .invoke a ∧ fs[i.toNat]? = some a) edge ?_
  intro r member _
  change RuleInstance fs r at member
  cases member with
  | call i a lookup => exact ⟨i, a, rfl, rfl, lookup⟩

end Silmaril.Wasm.Institution.Operational.CallResolution.Proofs
