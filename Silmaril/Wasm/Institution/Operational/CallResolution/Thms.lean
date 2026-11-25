module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution

open Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution.Runtime (FuncAddr)

theorem resolves {fs : List FuncAddr} {i : FuncIdx} {a : FuncAddr}
    (lookup : fs[i.toNat]? = some a) : Edge fs (.call i) (.invoke a) :=
  Derives.apply (R := (presentation fs).rules) (r := ⟨[], (.call i, .invoke a)⟩)
    (.call i a lookup) (fun _ h => nomatch h)

theorem invert {fs : List FuncAddr} {src dst : State} (edge : Edge fs src dst) :
    ∃ i a, src = .call i ∧ dst = .invoke a ∧ fs[i.toNat]? = some a :=
  Proofs.invert edge

end Silmaril.Wasm.Institution.Operational.CallResolution
