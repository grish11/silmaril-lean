module

import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Institution.Operational.MemoryQuery
open Silmaril.Wasm.SingleThreaded.Det (noHost)

private def bytes : ByteArray := ⟨#[0x12, 0x34, 0x56, 0x78]⟩
private def memory : Runtime.MemInst := ⟨bytes, none⟩
private def addr : Runtime.MemAddr := ⟨0⟩
private def frame : Runtime.Frame := ⟨[], { memories := [addr] }⟩
private def store : V1.Execution.Store Unit := { memories := [memory] }
private def host : V1.Execution.HostSemantics Unit := fun _ _ _ _ => False
private def limeHost : Lime1.Execution.HostSemantics Unit := fun _ _ _ _ => False

private theorem found : V1.Execution.frameMemory store frame = some (addr, memory) := rfl
private theorem limeFound :
    Lime1.Execution.frameMemory (store.mapCode V1.Func.toLime) frame = some (addr, memory) :=
  (V1.Execution.map_frameMemory store frame).trans found

private theorem loads : Edge memory.data (.load 0) (.value 0x78563412) :=
  fact (.load 0 _ (by decide))

private theorem traps : Edge memory.data (.load 1) .trap :=
  fact (.loadTrap 1 (by decide))

example : V1.Execution.Step host ⟨store, frame, v1Code (.load 0)⟩
    ⟨store, frame, v1Code (.value 0x78563412)⟩ := v1_sound found loads

example : Lime1.Execution.Step limeHost ⟨store.mapCode V1.Func.toLime, frame, limeCode (.load 1)⟩
    ⟨store.mapCode V1.Func.toLime, frame, [.trap]⟩ := lime_sound limeFound traps

example : Execution.Core.Step Numerics.Profile.spec noHost
    (v1Config store frame (.load 0)).toLime.toCore
    (v1Config store frame (.value 0x78563412)).toLime.toCore := by
  rw [v1_to_lime, v1_to_lime, lime_to_core, lime_to_core]
  exact core_sound (memory_toCore limeFound) rfl loads

example {target : Execution.Core.Config Unit}
    (path : Execution.Core.Steps Numerics.Profile.spec noHost
      (v1Config store frame (.load 1)).toLime.toCore target) :
    ∃ out, Relation.ReflTransGen (Edge memory.data) (.load 1) out ∧
      target = (v1Config store frame out).toLime.toCore := by
  rw [v1_to_lime, lime_to_core] at path
  obtain ⟨out, exactPath, eq⟩ := (core_run_iff (memory_toCore limeFound) rfl).mp path
  exact ⟨out, exactPath, by rw [v1_to_lime, lime_to_core, eq]⟩

example (page : ByteArray) (size : page.size = Memory.pageSize) :
    Edge page .size (.value (BitVec.ofNat 32 1)) := by
  have pages : Memory.size page = 1 := by simp [Memory.size, size, Memory.pageSize]
  simpa only [pages] using fact (RuleInstance.size (bytes := page))

example : Edge ByteArray.empty .size (.value 0) := fact .size

example : V1.Execution.frameMemory ({} : V1.Execution.Store Unit) frame = none := rfl
