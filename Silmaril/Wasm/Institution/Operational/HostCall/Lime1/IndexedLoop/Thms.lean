module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Readback

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop

open Execution.Runtime (Frame)
open Wasm.Lime1.Execution

variable {H : Type} {p : Program H} {base : Store H} {mem : Memory32 base} {host : HostSemantics H}
  {outer : Frame} {index : FuncIdx} {arg : BitVec 64} {dst : Config H}

/-- Each graph successor represents exactly one native step, including the
pending restart, repeated host invocation, and distinct trap cleanup steps. -/
theorem step_iff (checked : p.Checked mem outer index) (contract : p.Contract mem host) {a : State H}
    (ready : p.Ready mem host arg a.phase) (live : mem.Live a.bytes) :
    Step host (p.render mem outer index arg a) dst ↔
      ∃ next, Edge p mem host arg a next ∧ dst = p.render mem outer index arg next :=
  Proofs.step_iff checked contract ready live

/-- Read back any finite native endpoint from a graph phase with live memory. -/
theorem run_iff (checked : p.Checked mem outer index) (contract : p.Contract mem host) {a : State H}
    (ready : p.Ready mem host arg a.phase) (live : mem.Live a.bytes) :
    Steps host (p.render mem outer index arg a) dst ↔
      ∃ next, Relation.ReflTransGen (Edge p mem host arg) a next ∧
        p.Ready mem host arg next.phase ∧ mem.Live next.bytes ∧ dst = p.render mem outer index arg next :=
  Proofs.run_iff checked contract ready live

/-- Start at an ordinary typed source invocation in the allocated base store.
The checked source links, phase signatures and embedding contract supply the
premises for each reached loop boundary and indirect callee phase. The
checked endpoint carries the live bytes after any reached callee write. -/
theorem call_run_iff (checked : p.Checked mem outer index) (contract : p.Contract mem host) :
    Steps host ⟨base, outer, values [i64 arg] ++ [.source (.call index)]⟩ dst ↔
      ∃ next, Relation.ReflTransGen (Edge p mem host arg) ⟨mem.initial.data, .source⟩ next ∧
        mem.Live next.bytes ∧ dst = p.render mem outer index arg next :=
  Proofs.call_run_iff checked contract

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop
