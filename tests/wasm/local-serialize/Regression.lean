module

import Silmaril.Wasm.Binary.Core.LocalSerialize.Thms

open Silmaril.Wasm (LocalIdx)
open Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core.LocalSerialize
open Silmaril.Wasm.Binary.Core.Decode (DecodeM maxLocals readIdx Cursor)

private def small : Shape := ⟨1, 0, by decide +kernel⟩
private def atCap : Shape := ⟨50000, 49999, Fits.of_bounds (by decide +kernel) (by decide)⟩

example : Core.decode? (encode small) = some (raw small) := decode_encode small
example : Core.decode? (encode atCap) = some (raw atCap) := decode_encode atCap
example : (encode atCap).size = 40 := by decide +kernel
example : ¬ Fits 50001 49999 := by decide +kernel
example : ¬ Fits 50000 50000 := by decide +kernel
example : ¬ Fits 0 0 := by decide +kernel

example (shape : Shape) : shape.localIndex.toNat ≤ 49999 := by
  have cap := shape.localIndex_lt_decoderCap
  unfold maxLocals at cap
  omega

private def readIndex (bytes : List UInt8) : Option Nat :=
  match (readIdx : DecodeM LocalIdx).run' (Cursor.mk bytes.toByteArray 0) with
  | .ok index => some index.toNat
  | .error _ => none

example : readIndex [0xff, 0xff, 0xff, 0xff, 0x0f] = some (2 ^ 32 - 1) := by decide +kernel
example : readIndex [0x80, 0x80, 0x80, 0x80, 0x10] = none := by decide +kernel
example : readIndex [0x80, 0x80, 0x80, 0x80, 0x80, 0] = none := by decide +kernel

private def illTyped : ByteArray :=
  (bytesBeforeCode ++ [10, 8, 1, 6, 1, 1, 0x7f, 0x20, 1, 0x0b]).toByteArray

private def wrongSectionSize : ByteArray :=
  (bytesBeforeCode ++ [10, 7, 1, 6, 1, 1, 0x7f, 0x20, 0, 0x0b]).toByteArray

private def padded : ByteArray :=
  (bytesBeforeCode ++ [10, 0x88, 0, 1, 6, 1, 1, 0x7f, 0x20, 0, 0x0b]).toByteArray

example : (Core.decode? illTyped).isSome = true := by decide +kernel
example : (decodeIntrinsic? illTyped).isSome = false := by decide +kernel
example : (Core.decode? wrongSectionSize).isSome = false := by decide +kernel
example : (decodeShape? padded).map (fun shape => (shape.locals, shape.index)) = some (1, 0) := by decide +kernel
example : padded ≠ encode small := by decide +kernel

#print axioms raw_sound
#print axioms decode_encode
#print axioms RawModule.roundtrip
#print axioms IntrinsicModule.roundtrip
#print axioms decodeIntrinsic_sound
#print axioms decodeIntrinsic_roundtrip
