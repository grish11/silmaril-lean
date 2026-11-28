module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Entry.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.HostEntry

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry

open Execution.Runtime (Frame MemAddr MemInst Value)
open Wasm.V1.Execution

variable {H : Type} {entry : HostEntry H} {host : HostSemantics H} {mode : MemoryMode}
  {program : Program} {memory : MemAddr} {calls : CallMode} {base : Store H} {initial : MemInst}
  {bytes : ByteArray} {outer : Frame} {args : List Value}

/-- Each phase retains its argument, continuation or shared-store invariant. -/
theorem Edge.ready (graphChecked : program.checkV1 memory mode calls = true)
    (checked : entry.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (extent : mode.extent initial.data.size bytes)
    (contract : entry.Contract host mode memory initial (storeWithBytes base memory initial bytes))
    {src dst : Phase}
    (edge : entry.Edge host mode program memory base initial bytes outer args src dst)
    (before : entry.Ready mode program memory calls initial args src) :
    entry.Ready mode program memory calls initial args dst :=
  Proofs.preserves graphChecked checked layout extent contract edge before

/-- Exact native successors from each admitted phase of a designated direct host entry.
The host can deliver any contracted return or take a declared divergence self-step. -/
theorem v1_step_iff (graphChecked : program.checkV1 memory mode calls = true)
    (checked : entry.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size bytes)
    (contract : entry.Contract host mode memory initial (storeWithBytes base memory initial bytes))
    {src : Phase} (ready : entry.Ready mode program memory calls initial args src) {dst : Config H} :
    Step host (entry.render base memory initial bytes outer args src) dst ↔
      ∃ next, entry.Edge host mode program memory base initial bytes outer args src next ∧
        entry.Ready mode program memory calls initial args next ∧ dst = entry.render base memory initial bytes outer args next :=
  Proofs.step_iff graphChecked checked layout matched extent contract ready

/-- Native entry and the checked numeric prefix reach a typed pending site
or a prefix trap in finitely many steps, independently of host outcomes. -/
theorem v1_reaches_site (checked : entry.Checked mode program memory calls base outer args) :
    (∃ saved actual, entry.Ready mode program memory calls initial args (.pending saved actual) ∧
      Steps host (entry.render base memory initial bytes outer args .call)
        (entry.render base memory initial bytes outer args (.pending saved actual))) ∨
    (∃ saved tail, Steps host (entry.render base memory initial bytes outer args .call)
      (entry.render base memory initial bytes outer args (.trapped saved tail))) :=
  Proofs.reaches_site checked

/-- Read back every finite native prefix, including prefix traps, a parked
invocation, and execution of the resumed graph continuation. -/
theorem v1_run_iff (graphChecked : program.checkV1 memory mode calls = true)
    (checked : entry.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size bytes)
    (contract : entry.Contract host mode memory initial (storeWithBytes base memory initial bytes))
    {src : Phase} (ready : entry.Ready mode program memory calls initial args src) {dst : Config H} :
    Steps host (entry.render base memory initial bytes outer args src) dst ↔
      ∃ next, entry.Runs host mode program memory base initial bytes outer args src next ∧
        entry.Ready mode program memory calls initial args next ∧ dst = entry.render base memory initial bytes outer args next :=
  Proofs.run_iff graphChecked checked layout matched extent contract ready

/-- An ordinary source call opens the allocated body, initializes locals,
and computes the arguments of the designated site within the exact native
label and frame. Only source and embedding evidence is required at entry. -/
theorem v1_call_run_iff (graphChecked : program.checkV1 memory mode calls = true)
    (checked : entry.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size bytes)
    (contract : entry.Contract host mode memory initial (storeWithBytes base memory initial bytes))
    {dst : Config H} :
    Steps host ⟨storeWithBytes base memory initial bytes, outer, values args ++ [.source (.call entry.index)]⟩ dst ↔
      ∃ next, entry.Runs host mode program memory base initial bytes outer args .call next ∧
        entry.Ready mode program memory calls initial args next ∧
        dst = entry.render base memory initial bytes outer args next :=
  v1_run_iff (src := .call) graphChecked checked layout matched extent contract trivial

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry
