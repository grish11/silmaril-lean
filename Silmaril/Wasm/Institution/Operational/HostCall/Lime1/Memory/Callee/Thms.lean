module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Native
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Preservation

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee

open Execution.Runtime (Frame Value)
open Wasm.Lime1.Execution

variable {H : Type} {base : Store H} {mem : Memory32 base} {callee : MemoryTarget}
  {caller : Frame} {saved : List Value} {tail : List Admin} {bytes written : ByteArray} {phase next : Phase}
  {dst : Config H}

theorem ready_step (checked : callee.Checked mem) (move : Edge callee bytes phase written next)
    (ready : Ready callee phase) : Ready callee next :=
  Proofs.ready_step checked move ready

theorem live_step (move : Edge callee bytes phase written next) (live : mem.Live bytes) : mem.Live written :=
  Proofs.live_step move live

/-- A step keeps the full ordered argument and result checks and the allocated
memory's fixed extent. The byte array may change only at a successful store. -/
theorem preserves (checked : callee.Checked mem) (move : Edge callee bytes phase written next)
    (ready : Ready callee phase) (live : mem.Live bytes) : Ready callee next ∧ mem.Live written :=
  ⟨Proofs.ready_step checked move ready, Proofs.live_step move live⟩

/-- Exact native steps of the reached callee in the caller's operand and
instruction context. Native label and frame exits are distinct. After the
frame exit, the enclosing checked continuation takes over. -/
theorem step_iff (checked : callee.Checked mem) (allocated : callee.Allocated base)
    (ready : Ready callee phase) (live : mem.Live bytes) (notDone : ∀ out, phase ≠ .done out) :
    Internal (config mem caller saved tail callee bytes phase) dst ↔
      ∃ written next, Edge callee bytes phase written next ∧ dst = config mem caller saved tail callee written next :=
  Proofs.step_iff checked allocated ready live notDone

/-- The suspended caller cannot reach a host while this callee is live. -/
theorem absent (s : Store H) (allocated : callee.Allocated s) (notDone : ∀ out, phase ≠ .done out) :
    Execution.Runtime.decomposeFrom? coding s [] (values saved ++ render callee phase ++ tail) = none :=
  Proofs.absent s allocated notDone

/-- The caller's surrounding label remains in place while the callee steps. -/
theorem stays (notDone : ∀ out, phase ≠ .done out)
    {types : List Wasm.Lime1.FuncType} {n : Nat} {cont : Wasm.Lime1.Expr} {out : List Admin} :
    ¬ PureStep types [.label n cont (values saved ++ render callee phase ++ tail)] out :=
  Proofs.stays notDone

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee
