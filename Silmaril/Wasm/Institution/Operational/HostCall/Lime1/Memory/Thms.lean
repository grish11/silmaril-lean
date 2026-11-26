module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Memory

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1

open Execution.Runtime (Frame Value)
open Wasm.Lime1.Execution

variable {H : Type} {base : Store H} {mem : Memory32 base} {bytes : ByteArray}

/-- Every frame linked at slot zero reads the current designated bytes,
including after a callee or host changes them. -/
theorem Memory32.frameMemory_store {active : Frame} (slot : active.module.memories[0]? = some mem.address) :
    frameMemory (mem.store bytes) active = some (mem.address, { mem.initial with data := bytes }) :=
  Proofs.memory_at slot

/-- The callee updates the same live store supplied to the caller. A
successful write keeps its fixed extent, and a bounds trap retains the current
bytes. Both successors retain the saved operands and exact native suffixes. -/
theorem Memory32.activation_store_iff_at {host : HostSemantics H} {caller callee : Frame} {arity : Nat}
    {callerSaved saved : List Value} {callerTail tail : List Admin} {arg : Wasm.V1.MemArg} {ptr word : BitVec 32}
    {dst : Config H} (slot : callee.module.memories[0]? = some mem.address) (live : mem.Live bytes) :
    let s := mem.store bytes
    let m := { mem.initial with data := bytes }
    Step host ⟨s, caller, MemoryWrite.limeActivationCode arity callee callerSaved callerTail
      (values saved ++ (MemoryWrite.limeConfigAt arg s callee mem.address m (.store ptr word)).code ++ tail)⟩ dst ↔
      (∃ written, MemoryWrite.EdgeAt bytes arg.offset.val (.store ptr word) (.written written) ∧ mem.Live written ∧
        dst = ⟨mem.store written, caller, MemoryWrite.limeActivationCode arity callee callerSaved callerTail
          (values saved ++ tail)⟩) ∨
      (MemoryWrite.EdgeAt bytes arg.offset.val (.store ptr word) .trap ∧
        dst = ⟨s, caller, MemoryWrite.limeActivationCode arity callee callerSaved callerTail
          (values saved ++ .trap :: tail)⟩) :=
  Proofs.activation_store_live_iff slot live

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1
