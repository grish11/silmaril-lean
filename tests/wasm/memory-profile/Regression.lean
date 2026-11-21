module

import Silmaril.Wasm.Execution.Core.MemoryProfile.Thms
public meta import Silmaril.Wasm.Execution.Core.MemoryProfile.Defs

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Execution.Core.MemoryProfile Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.Validation Silmaril.Semantics.Operational

private def oracle : GrowOracle := fun _ _ _ _ => false
private def zeros : ByteArray := ⟨Array.replicate Memory.pageSize 0⟩
private theorem zeros_page : zeros.size = Memory.pageSize := by simp [zeros, ByteArray.size]

private def roundTrip : Code 0 1 :=
  .const 8 (.const 20 (.const 22 (.add (.store (.const 8 (.load .done))))))

private def nearEnd : Code 0 1 :=
  .const 7 (.const 65535 (.load (.add .done)))

private def nearEndStore : Code 0 1 :=
  .const 7 (.const 65535 (.const 42 (.store .done)))

private theorem roundTrip_answer {before : ByteArray} (page : before.size = Memory.pageSize) :
    ∃ after, roundTrip.eval .nil before = ⟨after, .values [word 42]⟩ ∧
      Memory.store before 8 (count := 4) (42 : BitVec 32) = some after := by
  have bound : 8 + 4 ≤ before.size := by rw [page]; decide
  let after := (Memory.encodeLE 4 (42 : BitVec 32).toNat).copySlice 0 before 8 4
  have writes : Memory.store before 8 (count := 4) (42 : BitVec 32) = some after := by
    simp [Memory.store, Memory.writeBytes, bound, after]
  have loads := Memory.load_store before after 8 4 (42 : BitVec 32) writes
  refine ⟨after, ?_, writes⟩
  change (match Memory.store before 8 (count := 4) (42 : BitVec 32) with
    | none => (⟨before, .trap⟩ : Answer)
    | some stored => match Memory.load stored 8 4 with
      | none => ⟨stored, .trap⟩
      | some bits => ⟨stored, .values [word bits]⟩) = _
  simp only [writes, loads]

example : (opSem oracle 1).May ⟨zeros, roundTrip, roundTrip.start_typed .nil zeros_page⟩
    (.returned (.ok [word 42])) := by
  obtain ⟨_, answer, _⟩ := roundTrip_answer zeros_page
  refine ⟨_, rfl, (roundTrip.may_iff .nil zeros (roundTrip.start_typed .nil zeros_page) _).mpr ?_⟩
  rw [answer]
  rfl

private theorem oobLoad {before : ByteArray} (page : before.size = Memory.pageSize) :
    nearEnd.eval .nil before = ⟨before, .trap⟩ := by
  have outside : ¬ 65535 + 4 ≤ before.size := by rw [page]; decide
  change (match Memory.load before 65535 4 with
    | none => (⟨before, .trap⟩ : Answer)
    | some bits => ⟨before, .values [word (7 + bits)]⟩) = _
  simp [Memory.load, Memory.readBytes, outside]

private theorem oobStore {before : ByteArray} (page : before.size = Memory.pageSize) :
    nearEndStore.eval .nil before = ⟨before, .trap⟩ := by
  have outside : ¬ 65535 + 4 ≤ before.size := by rw [page]; decide
  change (match Memory.store before 65535 (count := 4) (42 : BitVec 32) with
    | none => (⟨before, .trap⟩ : Answer)
    | some stored => ⟨stored, .values [word 7]⟩) = _
  simp [Memory.store, Memory.writeBytes, outside]

example {bytes : ByteArray} (page : bytes.size = Memory.pageSize) :
    (semantics oracle 1).toOpSem.TrapReachable (nearEnd.start .nil bytes) ∧
    (semantics oracle 1).SafeAt (nearEnd.start .nil bytes) := by
  have typed := nearEnd.start_typed .nil page
  refine ⟨(nearEnd.may_iff .nil bytes typed .trap).mpr ?_, nearEnd.safe .nil bytes typed⟩
  rw [oobLoad page]
  rfl

example : Steps (profile oracle) noHost (nearEndStore.start .nil zeros) (config zeros [.trap]) := by
  exact ((nearEndStore.normal_iff .nil zeros _).mpr (by rw [oobStore zeros_page]; rfl)).1

private def unsupported : Config Unit := config zeros [.plain (.memorySize index)]

private theorem unsupported_typed : ConfigOk unsupported (resultTypes 1) :=
  config_typed zeros_page (.single (.plain (.memory (.memorySize (a := .i32) rfl))))

example : ConfigOk unsupported (resultTypes 1) ∧
    (∃ next, Step (profile oracle) noHost unsupported next) ∧
    (semantics oracle 1).UBReachable unsupported ∧
    ¬ (semantics oracle 1).toOpSem.May unsupported .trap := by
  have rejected : ¬ Admitted 1 unsupported := by
    intro admitted
    have allowed := admitted.2.2.2 (.plain (.memorySize index)) (by simp [unsupported, config])
    cases allowed
  refine ⟨unsupported_typed, ⟨_, .memory (.size (mi := memory zeros) rfl)⟩, ⟨_, .refl, .inr rejected⟩, ?_⟩
  rintro ⟨target, path, observation⟩
  rcases path.cases_head with rfl | ⟨_, edge, _⟩
  · exact rejected observation.1
  · exact rejected edge.1

example : index.toNat < 2 ^ 32 ∧ memarg0.offset.val < 2 ^ 32 ∧ memarg0.align.val = 0 := by decide

public def main : IO Unit := do
  let answer := roundTrip.eval .nil zeros
  let returned := match answer.result with
    | .values [.num ⟨.int .i32, bits⟩] => bits == 42
    | _ => false
  unless returned && zeros[8]! == 0 && answer.bytes[8]! == 42 && answer.bytes.size == zeros.size do
    throw (IO.userError "expected a changed byte and returned i32(42)")
  for answer in [nearEnd.eval .nil zeros, nearEndStore.eval .nil zeros] do
    match answer.result with
    | .trap => unless answer.bytes == zeros do throw (IO.userError "OOB changed bytes")
    | _ => throw (IO.userError "expected an OOB trap")
  IO.println "Core memory profile: add/store/load and both OOB traps checked"

#print axioms load_step_iff
#print axioms store_step_iff
#print axioms Code.start_typed
#print axioms Code.raw_prefix_admitted
#print axioms Code.normal_iff
#print axioms Code.reach_iff
#print axioms Code.may_iff
#print axioms Code.safe
#print axioms Code.not_diverges
