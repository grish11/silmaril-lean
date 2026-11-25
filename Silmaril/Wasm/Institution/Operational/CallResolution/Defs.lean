module

public import Silmaril.Logic.Operational.SOS.Thms
public import Silmaril.Wasm.Execution.Runtime

/-!
# Direct call resolution

The presentation resolves the caller's local function index to a store address.
The native successor is poised at invocation. Invocation, including entry into
a callee frame or a host call, is a subsequent native step outside this slice.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution.Runtime (FuncAddr)

inductive State where
  | call (i : FuncIdx)
  | invoke (address : FuncAddr)

abbrev Judgment := State × State

inductive RuleInstance (functions : List FuncAddr) : Rule Judgment → Prop where
  | call (i : FuncIdx) (address : FuncAddr) (lookup : functions[i.toNat]? = some address) :
      RuleInstance functions ⟨[], (.call i, .invoke address)⟩

def shape : SOS.Shape.{0} := ⟨⟨State, Unit⟩, Judgment, fun (a, _, b) => (a, b)⟩
def presentation (functions : List FuncAddr) : SOS.Presentation :=
  ⟨shape, {r | RuleInstance functions r}⟩

abbrev Edge (functions : List FuncAddr) (a b : State) :=
  (presentation functions).Derives (a, b)

end Silmaril.Wasm.Institution.Operational.CallResolution
