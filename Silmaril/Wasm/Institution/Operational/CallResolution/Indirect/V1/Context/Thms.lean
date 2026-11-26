module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.V1.Context.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.V1.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.V1.Context

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect

open Execution.Runtime (Frame FuncAddr MemAddr MemInst Value)
open Wasm.V1.Execution
open CallContinuation.OuterCall.Ranked.Graph

/-- Successful lookup at the checked site selects an allocated graph function
with exactly the declared V1 signature, even after the selected memory changes. -/
theorem Site.v1_resolved_target {H : Type} {site : Site} {program : Memory32.Program} {m : MemAddr}
    {base : Store H} {initial : MemInst} (layout : Memory32.Layout program base m initial)
    {caller : Frame} (checked : site.V1Checked program base caller)
    {bytes : ByteArray} {selector : BitVec 32} {address : FuncAddr}
    (resolved : v1Resolve (Memory32.storeWithBytes base m initial bytes) caller site.typeIndex selector =
      some (.resolved address)) :
    ∃ fn, program.lookup address = some fn ∧ fn.declaration.type = site.signature :=
  Proofs.V1Context.resolved_target layout checked resolved

/-- Under a suspended operand prefix and continuation, a live invocation or
frame reflects exactly one existing checked Memory32 edge. -/
theorem v1_callee_step_iff {H : Type} {mode : Memory32.MemoryMode} {calls : Memory32.CallMode}
    {program : Memory32.Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (checked : program.checkV1 m mode calls = true) (layout : Memory32.Layout program base m initial)
    (matched : mode.matches initial) {src : Memory32.State} {rank : Nat}
    (ready : Memory32.ReadyFor mode program m calls rank initial.data.size src)
    (rigid : Rigid (Memory32.render base m initial src).store src.code)
    {saved : List Value} {tail : List Admin} {dst : Config H} :
    Step CallFrame.v1NoHost (v1Plug saved tail (Memory32.render base m initial src)) dst ↔
      ∃ out, Memory32.EdgeAt mode program m src out ∧
        Memory32.ReadyFor mode program m calls rank initial.data.size out ∧
        dst = v1Plug saved tail (Memory32.render base m initial out) :=
  Proofs.V1Context.checked_step_iff checked layout matched ready rigid

/-- Finite runs at one successfully resolved site read back through the pending
invoke and live callee, including result delivery or trap. Once the callee
finishes, execution of the supplied caller tail is represented by native steps. -/
theorem Site.v1_run_iff {H : Type} {mode : Memory32.MemoryMode} {calls : Memory32.CallMode}
    {program : Memory32.Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (graph : program.checkV1 m mode calls = true) (layout : Memory32.Layout program base m initial)
    (matched : mode.matches initial) {site : Site} {caller : Frame} (checked : site.V1Checked program base caller)
    {bytes : ByteArray} (extent : mode.extent initial.data.size bytes)
    {selector : BitVec 32} {address : FuncAddr}
    (resolved : v1Resolve (Memory32.storeWithBytes base m initial bytes) caller site.typeIndex selector =
      some (.resolved address))
    {saved args : List Value} (typed : args.map Value.type = site.signature.params)
    {tail : List Admin} {dst : Config H} :
    let src := v1Source (Memory32.storeWithBytes base m initial bytes) caller site.typeIndex selector (saved ++ args) tail
    let invoke : Memory32.State := ⟨bytes, caller, values args ++ [.invoke address]⟩
    Steps CallFrame.v1NoHost src dst ↔ dst = src ∨
      ∃ fn, program.lookup address = some fn ∧ ∃ out, Memory32.RunsAt mode program m invoke out ∧
        Memory32.ReadyFor mode program m calls (fn.rank + 1) initial.data.size out ∧
        v1CalleeEndpoint saved tail (Memory32.render base m initial out) dst :=
  Proofs.V1Context.run_iff graph layout matched checked extent resolved typed

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect
