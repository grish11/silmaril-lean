module

public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryWrite.Lime1Context

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryWrite

open Execution.Runtime (Frame MemAddr MemInst Value)
open Wasm.Lime1.Execution

/-- Reflect a leading full-width load with the saved operands and tail intact. -/
theorem lime_context_load_step_iff_at {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} {immediate : Wasm.V1.MemArg} {ptr : BitVec 32}
    {saved : List Value} {tail : List Admin} {dst : Config H}
    (lookup : frameMemory s f = some (a, m)) :
    Step host ⟨s, f, values saved ++ MemoryQuery.limeCodeAt immediate (.load ptr) ++ tail⟩ dst ↔
      ∃ out, MemoryQuery.EdgeAt m.data immediate.offset.val (.load ptr) out ∧
        dst = ⟨s, f, values saved ++ MemoryQuery.limeCodeAt immediate out ++ tail⟩ :=
  Proofs.Lime1Context.load_step_iff lookup

/-- Reflect a leading full-width store, with the exact update or bounds trap. -/
theorem lime_context_store_step_iff_at {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} {immediate : Wasm.V1.MemArg} {ptr word : BitVec 32}
    {saved : List Value} {tail : List Admin} {dst : Config H}
    (lookup : frameMemory s f = some (a, m)) :
    Step host ⟨s, f, values saved ++ (limeConfigAt immediate s f a m (.store ptr word)).code ++ tail⟩ dst ↔
      ∃ out, EdgeAt m.data immediate.offset.val (.store ptr word) out ∧
        let next := limeConfigAt immediate s f a m out
        dst = ⟨next.store, next.frame, values saved ++ next.code ++ tail⟩ :=
  Proofs.Lime1Context.store_step_iff lookup

/-- A load step inside the entered result label and frame preserves both continuations. -/
theorem lime_activation_load_step_iff_at {H : Type} {host : HostSemantics H} {s : Store H}
    {caller callee : Frame} {arity : Nat} {callerSaved saved : List Value} {callerTail tail : List Admin}
    {a : MemAddr} {m : MemInst} {immediate : Wasm.V1.MemArg} {ptr : BitVec 32}
    {dst : Config H} (lookup : frameMemory s callee = some (a, m)) :
    Step host ⟨s, caller, limeActivationCode arity callee callerSaved callerTail
      (values saved ++ MemoryQuery.limeCodeAt immediate (.load ptr) ++ tail)⟩ dst ↔
      ∃ out, MemoryQuery.EdgeAt m.data immediate.offset.val (.load ptr) out ∧
        dst = ⟨s, caller, limeActivationCode arity callee callerSaved callerTail
          (values saved ++ MemoryQuery.limeCodeAt immediate out ++ tail)⟩ :=
  Proofs.Lime1Context.load_activation_iff lookup

/-- A store step inside the entered result label and frame updates the caller’s live store. -/
theorem lime_activation_store_step_iff_at {H : Type} {host : HostSemantics H} {s : Store H}
    {caller callee : Frame} {arity : Nat} {callerSaved saved : List Value} {callerTail tail : List Admin}
    {a : MemAddr} {m : MemInst} {immediate : Wasm.V1.MemArg} {ptr word : BitVec 32}
    {dst : Config H} (lookup : frameMemory s callee = some (a, m)) :
    Step host ⟨s, caller, limeActivationCode arity callee callerSaved callerTail
      (values saved ++ (limeConfigAt immediate s callee a m (.store ptr word)).code ++ tail)⟩ dst ↔
      ∃ out, EdgeAt m.data immediate.offset.val (.store ptr word) out ∧
        let next := limeConfigAt immediate s callee a m out
        dst = ⟨next.store, caller, limeActivationCode arity next.frame callerSaved callerTail
          (values saved ++ next.code ++ tail)⟩ :=
  Proofs.Lime1Context.store_activation_iff lookup

end Silmaril.Wasm.Institution.Operational.MemoryWrite
