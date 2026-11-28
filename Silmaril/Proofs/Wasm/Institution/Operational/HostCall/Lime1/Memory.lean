module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Defs
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Lime1Context.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Proofs

open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall.Ranked
open Wasm.Lime1.Execution

variable {H : Type} {base : Store H} {mem : Memory32 base} {bytes : ByteArray}

theorem initial_live : mem.Live mem.initial.data := by
  unfold Memory32.Live
  cases mem.extent with
  | fixed => rfl
  | growing admitted => exact ⟨Nat.le_refl _, admitted⟩

theorem live_same_size {next : ByteArray} (live : mem.Live bytes) (same : next.size = bytes.size) :
    mem.Live next := by
  unfold Memory32.Live at live ⊢
  cases extent : mem.extent with
  | fixed => exact same.trans (by simpa only [extent] using live)
  | growing _ => simpa only [extent, Graph.Memory32.GrowthExtent, Graph.Memory32.BoundedExtent,
      MemoryGrow.SizeAllows, Execution.Memory.size, same] using live

theorem live_grow {next : ByteArray} {delta : BitVec 32}
    (enabled : mem.extent.growthEnabled = true) (live : mem.Live bytes)
    (edge : MemoryGrow.Edge (mem.current bytes) (.request delta) (.grown next)) : mem.Live next := by
  unfold Memory32.Live at live ⊢
  cases extent : mem.extent with
  | fixed => simp [extent, MemoryExtent.growthEnabled] at enabled
  | growing _ =>
    exact Graph.Memory32.BoundedExtent.grow (by simpa only [extent] using live) edge

theorem memory_at {active : Frame} (slot : active.module.memories[0]? = some mem.address) :
    frameMemory (mem.store bytes) active = some (mem.address, { mem.initial with data := bytes }) := by
  have bound := (List.getElem?_eq_some_iff.mp mem.allocated).1
  simp [frameMemory, slot, Memory32.store, Memory32.current, setMemory, bound]

private theorem store_again (written : ByteArray) :
    setMemory (mem.store bytes) mem.address { mem.initial with data := written } = mem.store written := by
  simp [Memory32.store, Memory32.current, setMemory, List.set_set]

theorem activation_store_live_iff {host : HostSemantics H} {caller callee : Frame} {arity : Nat}
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
          (values saved ++ .trap :: tail)⟩) := by
  dsimp only
  rw [MemoryWrite.lime_activation_store_step_iff_at (memory_at (bytes := bytes) slot)]
  constructor
  · rintro ⟨out, edge, rfl⟩
    cases out with
    | store => cases MemoryWrite.invert_at edge
    | written written =>
      have size : written.size = bytes.size := MemoryWrite.closed_at edge
      exact .inl ⟨written, edge, live_same_size live size, by
        simp [MemoryWrite.limeConfigAt, store_again, List.append_nil]⟩
    | trap => exact .inr ⟨edge, by simp [MemoryWrite.limeConfigAt]⟩
  · rintro (⟨written, edge, _, rfl⟩ | ⟨edge, rfl⟩)
    · exact ⟨.written written, edge, by simp [MemoryWrite.limeConfigAt, store_again, List.append_nil]⟩
    · exact ⟨.trap, edge, by simp [MemoryWrite.limeConfigAt]⟩

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Proofs
