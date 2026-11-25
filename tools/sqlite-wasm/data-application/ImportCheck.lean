module

import SqliteWasm.DataApplication

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core SqliteWasm

example {H : Type} {s : Store H} {f : Frame} {m : Module} {ma da0 da1 : Nat} {mem : MemInst}
    (decoded : Binary.Core.decode? originalBytes.toByteArray = some m)
    (memory : s.mem? f ⟨0⟩ = some (ma, mem))
    (first : s.data? f ⟨0⟩ = some (da0, ⟨reactorData0.bytes⟩))
    (second : s.data? f ⟨1⟩ = some (da1, ⟨reactorData1.bytes⟩))
    (bound : 59324 ≤ mem.bytes.size) :
    initData? evalConst? s f m =
      some (((s.setMem ma { mem with bytes := reactorDataMemory mem.bytes }).setData da0 .empty).setData
        da1 .empty, f) := by
  have pinned : m = sqlite := Option.some.inj (decoded.symm.trans originalDecode)
  subst m
  exact reactorDataApplied memory first second bound

example (bytes : ByteArray) (bound : 59324 ≤ bytes.size) :
    (reactorDataMemory bytes).size = bytes.size := reactorDataMemorySize bytes bound

example (bytes : ByteArray) (bound : 59324 ≤ bytes.size) :
    Memory.load (reactorDataMemory bytes) 59328 4 = Memory.load bytes 59328 4 := by
  unfold Memory.load
  rw [reactorDataReadAfterEnd bytes 59328 4 bound (by decide)]

example (bytes : ByteArray) (bound : 59324 ≤ bytes.size) :
    Memory.load (reactorDataMemory bytes) 59892 4 = Memory.load bytes 59892 4 := by
  unfold Memory.load
  rw [reactorDataReadAfterEnd bytes 59892 4 bound (by decide)]

#print axioms reactorDataSegments
#print axioms reactorDataModes
#print axioms reactorDataSizes
#print axioms reactorDataApplied
#print axioms reactorDataMemorySize
#print axioms reactorDataReadAfterEnd
