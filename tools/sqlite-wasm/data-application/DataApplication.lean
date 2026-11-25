module

public import SqliteWasm.WholeModule
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInit
public import Silmaril.Wasm.Execution.Core.Exec.ConstEval
import Silmaril.Wasm.Auto2.Kernel.Thms
import Silmaril.Wasm.Component.Reference.Wasm.Execution.Memory.Lemmas.Defs

@[expose] public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto2.Kernel (writeSeg)
open Silmaril.Wasm.Verify.Kernel (writeL_eq)

set_option maxRecDepth 220000
set_option maxHeartbeats 900000

def reactorData0 : Data := (sqlite.data[0]?).get rfl
def reactorData1 : Data := (sqlite.data[1]?).get rfl

theorem reactorDataSegments : sqlite.data = [reactorData0, reactorData1] := rfl

theorem reactorDataModes :
    reactorData0.mode = .active ⟨0⟩ [.intConst .i32 1024] ∧
    reactorData1.mode = .active ⟨0⟩ [.intConst .i32 52400] := ⟨rfl, rfl⟩

theorem reactorDataSizes :
    reactorData0.bytes.size = 51370 ∧ reactorData1.bytes.size = 6924 := by decide +kernel

private theorem applyDataSegment {H : Type} {s : Store H} {f : Frame} {d : Data} {k : Nat}
    {ma da : Nat} {mem : MemInst} {offset : BitVec 32}
    (mode : d.mode = .active ⟨0⟩ [.intConst .i32 offset])
    (mappedMemory : s.mem? f ⟨0⟩ = some (ma, mem))
    (mappedData : s.data? f ⟨Fin.ofNat _ k⟩ = some (da, ⟨d.bytes⟩))
    (fits : offset.toNat + d.bytes.size ≤ mem.bytes.size)
    (noWrap : offset.toNat + d.bytes.size < 2 ^ 32)
    (nonempty : d.bytes.size ≠ 0) :
    initDataSeg? evalConst? s f k d =
      some ((s.setMem ma { mem with bytes := Memory.writeSlice mem.bytes offset.toNat d.bytes }).setData
        da ByteArray.empty) := by
  have sizeBound : d.bytes.size < 2 ^ 32 := by omega
  have count : (BitVec.ofNat 32 d.bytes.size).toNat = d.bytes.size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sizeBound]
  have sourceFits : (0#32).toNat + d.bytes.size ≤ d.bytes.size := by simp
  have sourceWrap : (0#32).toNat + d.bytes.size < 2 ^ 32 := by simpa using sizeBound
  have rangeRun := Silmaril.Proofs.Wasm.Auto2.Kernel.memoryInitLoop_fast
    (a := .i32) (x := ⟨0⟩) (y := ⟨Fin.ofNat _ k⟩) (di := ⟨d.bytes⟩)
    d.bytes.size s mem offset 0 (BitVec.ofNat 32 d.bytes.size)
    count mappedMemory mappedData fits sourceFits noWrap sourceWrap
  have size : d.bytes.data.toList.length = d.bytes.size := by simp [ByteArray.size_data]
  have all : d.bytes.data.toList.take d.bytes.size = d.bytes.data.toList := by
    rw [← size, List.take_length]
  have write : writeSeg mem offset.toNat d.bytes.data.toList =
      Memory.writeSlice mem.bytes offset.toNat d.bytes := by
    unfold writeSeg Memory.writeSlice
    rw [writeL_eq _ _ _ (by simpa only [size, ByteArray.size_data, Array.length_toList] using fits),
      Memory.spliceL_eq]
  rw [ite_eq_right nonempty] at rangeRun
  change memoryInitLoop s f ⟨0⟩ ⟨Fin.ofNat _ k⟩ .i32 offset 0 (BitVec.ofNat 32 d.bytes.size) =
      some (s.setMem ma ⟨mem.type, writeSeg mem offset.toNat (d.bytes.data.toList.take d.bytes.size)⟩) at rangeRun
  rw [all, write] at rangeRun
  unfold initDataSeg?
  rw [mode]
  change (match memoryInitLoop s f ⟨0⟩ ⟨Fin.ofNat _ k⟩ .i32 offset 0 (BitVec.ofNat 32 d.bytes.size) with
    | none => none
    | some next => dataDrop? next f ⟨Fin.ofNat _ k⟩) = _
  rw [rangeRun]
  let updated := s.setMem ma { mem with bytes := Memory.writeSlice mem.bytes offset.toNat d.bytes }
  change (s.data? f ⟨Fin.ofNat _ k⟩).map (fun (address, _) => updated.setData address .empty) = _
  rw [mappedData]
  rfl

def reactorDataMemory (bytes : ByteArray) : ByteArray :=
  Memory.writeSlice (Memory.writeSlice bytes 1024 reactorData0.bytes) 52400 reactorData1.bytes

private theorem dataEntry {H : Type} {s : Store H} {f : Frame} {index : DataIdx}
    {addr : Nat} {data : DataInst} (mapped : s.data? f index = some (addr, data)) :
    f.module.datas[index.toNat]? = some addr ∧ s.datas[addr]? = some data := by
  change (f.module.datas[index.toNat]?.bind fun a => s.datas[a]?.bind fun d => some (a, d)) =
    some (addr, data) at mapped
  obtain ⟨a, slot, resolved⟩ := Option.bind_eq_some_iff.mp mapped
  obtain ⟨d, inst, equality⟩ := Option.bind_eq_some_iff.mp resolved
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj equality)
  exact ⟨slot, inst⟩

private theorem copiedSize (memory payload : ByteArray) (offset : Nat)
    (fits : offset + payload.size ≤ memory.size) :
    (Memory.writeSlice memory offset payload).size = memory.size :=
  Memory.writeBytes_size memory payload _ offset (by simp [Memory.writeBytes, fits])

/-- Both ordered data writes of the original reactor, followed by dropping their inputs. -/
theorem reactorDataApplied {H : Type} {s : Store H} {f : Frame} {ma da0 da1 : Nat} {mem : MemInst}
    (mapped : s.mem? f ⟨0⟩ = some (ma, mem))
    (first : s.data? f ⟨0⟩ = some (da0, ⟨reactorData0.bytes⟩))
    (second : s.data? f ⟨1⟩ = some (da1, ⟨reactorData1.bytes⟩))
    (bound : 59324 ≤ mem.bytes.size) :
    initData? evalConst? s f sqlite =
      some (((s.setMem ma { mem with bytes := reactorDataMemory mem.bytes }).setData da0 .empty).setData
        da1 .empty, f) := by
  obtain ⟨size0, size1⟩ := reactorDataSizes
  obtain ⟨mode0, mode1⟩ := reactorDataModes
  let mem0 := { mem with bytes := Memory.writeSlice mem.bytes 1024 reactorData0.bytes }
  let mid := (s.setMem ma mem0).setData da0 .empty
  have fit0 : (1024#32).toNat + reactorData0.bytes.size ≤ mem.bytes.size := by
    change 1024 + reactorData0.bytes.size ≤ mem.bytes.size
    omega
  have run0 : initDataSeg? evalConst? s f 0 reactorData0 = some mid :=
    applyDataSegment mode0 mapped first fit0 (by rw [size0]; decide) (by omega)
  have mapped0 : mid.mem? f ⟨0⟩ = some (ma, mem0) :=
    Silmaril.Proofs.Wasm.Auto2.Kernel.mem?_setMem mapped mem0
  obtain ⟨_, old0⟩ := dataEntry first
  obtain ⟨slot1, old1⟩ := dataEntry second
  change f.module.datas[1]? = some da1 at slot1
  have separate : da0 ≠ da1 := by
    intro same
    subst da1
    have values := Option.some.inj (old0.symm.trans old1)
    have counts := congrArg (fun data : DataInst => data.bytes.size) values
    change reactorData0.bytes.size = reactorData1.bytes.size at counts
    omega
  have mapped1 : mid.data? f ⟨1⟩ = some (da1, ⟨reactorData1.bytes⟩) := by
    change (f.module.datas[1]?.bind fun a =>
      (s.datas.modify da0 (fun _ => ⟨ByteArray.empty⟩))[a]?.bind fun data => some (a, data)) = _
    rw [slot1, Option.bind_some, List.getElem?_modify_ne _ _ separate, old1]
    rfl
  have afterSize : mem0.bytes.size = mem.bytes.size := copiedSize _ _ 1024 fit0
  have fit1 : (52400#32).toNat + reactorData1.bytes.size ≤ mem0.bytes.size := by
    change 52400 + reactorData1.bytes.size ≤ mem0.bytes.size
    omega
  have run1 := applyDataSegment (k := 1) mode1 mapped0 mapped1 fit1 (by rw [size1]; decide) (by omega)
  let final := { mem with bytes := reactorDataMemory mem.bytes }
  have mergedStore : (mid.setMem ma final).setData da1 .empty =
      ((s.setMem ma final).setData da0 .empty).setData da1 .empty := by
    simp only [mid, Store.setMem, Store.setData, List.set_set]
  have finalRun : initDataSeg? evalConst? mid f 1 reactorData1 =
      some (((s.setMem ma final).setData da0 .empty).setData da1 .empty) := by
    change initDataSeg? evalConst? mid f 1 reactorData1 = some ((mid.setMem ma final).setData da1 .empty) at run1
    rwa [mergedStore] at run1
  unfold initData?
  rw [reactorDataSegments]
  change (initDataList? evalConst? s f [(0, reactorData0), (1, reactorData1)]).map (·, f) = _
  simp only [initDataList?, run0, finalRun]
  rfl

theorem reactorDataMemorySize (bytes : ByteArray) (bound : 59324 ≤ bytes.size) :
    (reactorDataMemory bytes).size = bytes.size := by
  obtain ⟨size0, size1⟩ := reactorDataSizes
  let mid := Memory.writeSlice bytes 1024 reactorData0.bytes
  have midSize : mid.size = bytes.size := copiedSize bytes reactorData0.bytes 1024 (by omega)
  exact (copiedSize mid reactorData1.bytes 52400 (by omega)).trans midSize

/-- Above the final data endpoint, both writes retain the original read result. -/
theorem reactorDataReadAfterEnd (bytes : ByteArray) (start len : Nat)
    (bound : 59324 ≤ bytes.size) (after : 59324 ≤ start) :
    Memory.readBytes (reactorDataMemory bytes) start len = Memory.readBytes bytes start len := by
  obtain ⟨size0, size1⟩ := reactorDataSizes
  let mid := Memory.writeSlice bytes 1024 reactorData0.bytes
  have beforeFits : 1024 + reactorData0.bytes.size ≤ bytes.size := by omega
  have first : Memory.writeBytes bytes 1024 reactorData0.bytes = some mid := by
    unfold Memory.writeBytes
    rw [ite_eq_left beforeFits]
  have sizeMid := Memory.writeBytes_size _ _ _ _ first
  have afterFits : 52400 + reactorData1.bytes.size ≤ mid.size := by omega
  have second : Memory.writeBytes mid 52400 reactorData1.bytes = some (reactorDataMemory bytes) := by
    change Memory.writeBytes mid 52400 reactorData1.bytes =
      some (Memory.writeSlice mid 52400 reactorData1.bytes)
    unfold Memory.writeBytes
    rw [ite_eq_left afterFits]
  exact (Memory.readBytes_writeBytes_disjoint _ _ _ 52400 start len second
    (Or.inr (by omega))).trans
    (Memory.readBytes_writeBytes_disjoint _ _ _ 1024 start len first (Or.inr (by omega)))


end SqliteWasm
