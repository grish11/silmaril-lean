module

public import SqliteWasm.ElementInit
public import SqliteWasm.AllocatedEntries
import SqliteWasm.ElementApplication
import SqliteWasm.DataApplication
import SqliteWasm.InitialMemoryReads
import Silmaril.Wasm.Auto2.Kernel.Thms

public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core

set_option maxRecDepth 65536
set_option maxHeartbeats 600000

theorem reactorAllocatedSegments {before allocated : Store Nat} {mi : ModuleInst}
    (alloc : allocModule? before sqlite reactorImportAddrs [.i32 126112, .i32 0]
      [.null] [reactorElementRefs] = some (allocated, mi)) :
    ∃ runtime mem, initSegments? evalConst? allocated { module := mi } sqlite =
        some (runtime, { module := mi }) ∧
      runtime.funcs = allocated.funcs ∧
      runtime.global? { module := mi } ⟨1⟩ =
        some (before.globals.length + 1, ⟨⟨.const, .i32⟩, .i32 0⟩) ∧
      runtime.mem? { module := mi } ⟨0⟩ = some (before.mems.length, mem) ∧
      mem.bytes.size = 131072 ∧
      Memory.load mem.bytes 59328 4 = some 0 ∧ Memory.load mem.bytes 59892 4 = some 0 := by
  have typed := reactorAllocatedTableElementAndGlobal alloc (by rfl) (by rfl)
  obtain ⟨⟨table, elem, tableAt, tableRefs, elemAt, elemRefs⟩, globalAt⟩ := typed
  let f : Frame := { module := mi }
  let elemStore := (allocated.setTable before.tables.length
    { table with refs := table.refs.take 1 ++ elem.refs ++ table.refs.drop 343 }).setElem before.elems.length []
  have tableBound : 343 ≤ table.refs.length := by rw [tableRefs, List.length_replicate]
  have count : elem.refs.length = 342 := by rw [elemRefs, reactorElementRefsLength]
  have elemRun : initElem? evalConst? allocated f sqlite = some (elemStore, f) :=
    reactorElementPhase tableAt elemAt tableBound count
  obtain ⟨memAt, first, second⟩ := reactorAllocatedMemoryAndData alloc (by rfl)
  have memAfterElem : elemStore.mem? f ⟨0⟩ = some (before.mems.length, reactorAllocationMemory) := memAt
  have firstAfterElem : elemStore.data? f ⟨0⟩ = some (before.datas.length, ⟨reactorData0.bytes⟩) := first
  have secondAfterElem : elemStore.data? f ⟨1⟩ = some (before.datas.length + 1, ⟨reactorData1.bytes⟩) := second
  have initialBound : 59324 ≤ reactorAllocationMemory.bytes.size := by
    change 59324 ≤ (Array.replicate 131072 (0 : UInt8)).size
    rw [Array.size_replicate]
    decide
  let mem := { reactorAllocationMemory with bytes := reactorDataMemory reactorZeroMemory }
  let updated := elemStore.setMem before.mems.length mem
  let runtime := (updated.setData before.datas.length .empty).setData (before.datas.length + 1) .empty
  have dataRun : initData? evalConst? elemStore f sqlite = some (runtime, f) :=
    reactorDataApplied memAfterElem firstAfterElem secondAfterElem initialBound
  have segments : initSegments? evalConst? allocated f sqlite = some (runtime, f) := by
    unfold initSegments?
    rw [elemRun]
    exact dataRun
  have memRuntime : runtime.mem? f ⟨0⟩ = some (before.mems.length, mem) :=
    Silmaril.Proofs.Wasm.Auto2.Kernel.mem?_setMem memAfterElem mem
  have reads : mem.bytes.size = 131072 ∧
      Memory.load mem.bytes 59328 4 = some 0 ∧ Memory.load mem.bytes 59892 4 = some 0 :=
    reactorInitialReads
  exact ⟨runtime, mem, segments, rfl, globalAt, memRuntime, reads.1, reads.2.1, reads.2.2⟩

#print axioms reactorAllocatedSegments

end SqliteWasm
