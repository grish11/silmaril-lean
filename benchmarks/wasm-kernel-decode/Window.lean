module

public import Silmaril.Prelude.Bytes.Thms
public import Silmaril.Wasm.Binary.Core.Decode

@[expose] public section

namespace WasmKernelBench

open Silmaril Silmaril.Wasm.Binary.Core

/-- Check an exact span at a supplied offset. This does not recognize a Wasm section. -/
def checkWindow (source : KBytes) (offset : Nat) (expected : KBytes) : Bool :=
  if offset + expected.len ≤ source.len then
    (source.slice offset expected.len).sameBytes 4096 expected
  else false

theorem materialized_size (source : KBytes) (wf : source.wf = true) :
    source.toByteArray.size = source.len := KBytes.length_toList source wf

theorem materialized_extract (source : KBytes) (wf : source.wf = true) {offset width : Nat}
    (bounds : offset + width ≤ source.len) :
    source.toByteArray.extract offset (offset + width) =
      (source.slice offset width).toByteArray := by
  apply ByteArray.ext (Array.ext' ?_)
  simp [KBytes.toByteArray, List.extract, KBytes.toList_slice source offset width wf bounds]

/-- A checked span supplies exactly the decoder's raw-byte result and next cursor. The caller
must separately link the offset and expected length to the format's semantic framing. -/
theorem checkWindow_sound (source expected : KBytes) (offset : Nat)
    (sourceWf : source.wf = true) (expectedWf : expected.wf = true)
    (checked : checkWindow source offset expected = true) :
    (Decode.readBytes expected.len).run ⟨source.toByteArray, offset⟩ =
      .ok (expected.toByteArray, ⟨source.toByteArray, offset + expected.len⟩) := by
  have bounds : offset + expected.len ≤ source.len := by
    by_contra outside
    simp [checkWindow, outside] at checked
  have bytesEq := KBytes.toList_eq_of_sameBytes 4096 (source.slice offset expected.len) expected
    (KBytes.wf_slice source offset expected.len sourceWf bounds) expectedWf
    (by simpa [checkWindow, bounds] using checked)
  have extracted := materialized_extract source sourceWf bounds
  have byteBounds : offset + expected.len ≤ source.toByteArray.size :=
    materialized_size source sourceWf ▸ bounds
  simp only [Decode.readBytes, StateT.run_bind, StateT.run_get, pure_bind]
  simp only [byteBounds, ite_true, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
    Decode.extractForKernel_eq, extracted]
  exact congrArg (fun (payload : ByteArray) =>
    Except.ok (payload, Decode.Cursor.mk source.toByteArray (offset + expected.len)))
    (ByteArray.ext (Array.ext' bytesEq))

end WasmKernelBench
