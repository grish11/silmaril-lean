module

public import SqliteWasm.DataApplication

@[expose] public section

namespace SqliteWasm

open Silmaril.Wasm.Execution

def reactorZeroMemory : ByteArray := ⟨Array.replicate 131072 0⟩

private theorem loadZeroMemory (size offset : Nat) (bound : offset + 4 ≤ size) :
    Memory.load ⟨Array.replicate size 0⟩ offset 4 = some 0 := by
  have sizeBytes : (⟨Array.replicate size 0⟩ : ByteArray).size = size := by
    change (Array.replicate size (0 : UInt8)).size = size
    exact Array.size_replicate
  have extract : (⟨Array.replicate size 0⟩ : ByteArray).extract offset (offset + 4) =
      ⟨Array.replicate 4 0⟩ := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    change (Array.replicate size (0 : UInt8)).extract offset (offset + 4) =
      Array.replicate 4 0
    rw [Array.extract_replicate, Nat.min_eq_left bound, Nat.add_sub_cancel_left]
  unfold Memory.load Memory.readBytes
  rw [sizeBytes, ite_eq_left bound, extract]
  rfl

theorem reactorInitialReads :
    (reactorDataMemory reactorZeroMemory).size = 131072 ∧
    Memory.load (reactorDataMemory reactorZeroMemory) 59328 4 = some 0 ∧
    Memory.load (reactorDataMemory reactorZeroMemory) 59892 4 = some 0 := by
  have size : reactorZeroMemory.size = 131072 := by
    change (Array.replicate 131072 (0 : UInt8)).size = 131072
    exact Array.size_replicate
  have enough : 59324 ≤ reactorZeroMemory.size := by omega
  refine ⟨(reactorDataMemorySize reactorZeroMemory enough).trans size, ?_, ?_⟩
  · have before := loadZeroMemory 131072 59328 (by decide)
    change Memory.load reactorZeroMemory 59328 4 = some 0 at before
    unfold Memory.load at before ⊢
    rwa [reactorDataReadAfterEnd reactorZeroMemory 59328 4 enough (by decide)]
  · have before := loadZeroMemory 131072 59892 (by decide)
    change Memory.load reactorZeroMemory 59892 4 = some 0 at before
    unfold Memory.load at before ⊢
    rwa [reactorDataReadAfterEnd reactorZeroMemory 59892 4 enough (by decide)]

#print axioms reactorInitialReads

end SqliteWasm
