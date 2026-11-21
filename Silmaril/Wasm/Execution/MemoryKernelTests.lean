module

public import Silmaril.Wasm.Execution.Memory

/-! # Kernel tests of `Memory.writeSlice` (`decide +kernel`)

* agreement with `ByteArray.copySlice` on small arrays, including a write that reaches past the
  end (`copySlice` truncates, so does `writeSlice`), a write that starts past the end, and an
  empty write (`writeSlice_eq` proves this in general);
* `writeBytes` refuses out-of-bounds writes and keeps the size;
* 64 KiB memories: writes near the start and near the end, read back with `get!`. These are
  the cases that exceeded the kernel's recursion depth with `copySlice`.
-/

namespace Silmaril.Wasm.Execution.Memory.KernelTests

def small : ByteArray := ⟨#[1, 2, 3, 4, 5]⟩

example : writeSlice small 1 ⟨#[9, 8]⟩ = (⟨#[9, 8]⟩ : ByteArray).copySlice 0 small 1 2 := by
  decide +kernel
example : writeSlice small 4 ⟨#[9, 8]⟩ = (⟨#[9, 8]⟩ : ByteArray).copySlice 0 small 4 2 := by
  decide +kernel
example : writeSlice small 7 ⟨#[9]⟩ = (⟨#[9]⟩ : ByteArray).copySlice 0 small 7 1 := by
  decide +kernel
example : writeSlice small 2 .empty = ByteArray.empty.copySlice 0 small 2 0 := by
  decide +kernel
example : (writeSlice small 1 ⟨#[9, 8]⟩).data.toList = [1, 9, 8, 4, 5] := by decide +kernel

example : writeBytes small 4 ⟨#[9, 8]⟩ = none := by decide +kernel
example : (writeBytes small 3 ⟨#[9, 8]⟩).map ByteArray.size = some 5 := by decide +kernel

/-- One Wasm page. -/
def page : ByteArray := ⟨Array.replicate pageSize 0⟩

example : (writeBytes page 1 ⟨#[104, 105, 33]⟩).map (·.get! 3) = some 33 := by decide +kernel
example : (writeBytes page 65530 ⟨#[1, 2, 3]⟩).map (·.get! 65531) = some 2 := by decide +kernel
example : (writeBytes page 65534 ⟨#[1, 2, 3]⟩) = none := by decide +kernel
example : ((writeBytes page 1024 ⟨#[7]⟩).bind (load · 1024 1)).map BitVec.toNat = some 7 := by
  decide +kernel

end Silmaril.Wasm.Execution.Memory.KernelTests
