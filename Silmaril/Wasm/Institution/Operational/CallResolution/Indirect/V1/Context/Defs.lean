module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.V1.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Defs
public import Silmaril.Wasm.V1.Execution.Inversion

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect

open Execution.Runtime (Frame FuncAddr Value)
open Wasm.V1.Execution
open CallContinuation.OuterCall.Ranked.Graph

/-- The active module resolves its one table operand at slot zero and supplies
the exact V1 type. Every initialized entry has a body in the checked graph.
The graph layout separately binds each body to its allocated non-host function. -/
structure Site.V1Checked {H : Type} (site : Site) (program : Memory32.Program) (s : Store H)
    (caller : Frame) : Prop where
  table : frameTable s caller = some site.table
  signature : caller.module.types[site.typeIndex.toNat]? = some site.signature
  targets : ∀ a : FuncAddr, some a ∈ site.table.refs → ∃ fn, program.lookup a = some fn

def v1Plug {H : Type} (saved : List Value) (tail : List Admin) (c : Config H) : Config H :=
  ⟨c.store, c.frame, values saved ++ c.code ++ tail⟩

/-- A cut before the callee produces a result, or precisely at delivery to the
caller. In the latter case the remaining caller run uses native steps. -/
def v1CalleeEndpoint {H : Type} (saved : List Value) (tail : List Admin) (cut dst : Config H) : Prop :=
  (Rigid cut.store cut.code ∧ dst = v1Plug saved tail cut) ∨
  (∃ r, cut.code = result r) ∧ Steps CallFrame.v1NoHost (v1Plug saved tail cut) dst

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect
