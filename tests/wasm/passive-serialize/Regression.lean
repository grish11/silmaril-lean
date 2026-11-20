module

import Silmaril.Wasm.Binary.Core.PassiveSerialize.Thms

open Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core.PassiveSerialize
open Silmaril.Wasm.Tools.Meta (encU32)

private def sample : Payload := ⟨⟨#[0, 0xff, 0x80]⟩, ⟨by decide, by
  change sectionSize 3 < _
  rw [sectionSize, encU32.eq_def]
  decide⟩⟩

private def empty : Payload := ⟨ByteArray.empty, ⟨by decide, by
  change sectionSize 0 < _
  rw [sectionSize, encU32.eq_def]
  decide⟩⟩

example : (encode empty).data.toList = [0, 0x61, 0x73, 0x6d, 1, 0, 0, 0, 11, 3, 1, 1, 0] := by
  rw [encode, List.toList_data_toByteArray]
  rw [show empty.val.size = 0 from rfl, show empty.val.data.toList = [] from rfl]
  have size : sectionSize 0 = 3 := by rw [sectionSize, encU32.eq_def]; decide
  rw [size, encU32.eq_def 3, encU32.eq_def 0]
  decide

example : Core.decode? (encode sample) = some (raw sample.val) := decode_encode sample

example : IntrinsicModule.roundtrip (.ofPayload sample) = decode_encode sample := rfl

example : decodePayload? (List.toByteArray (magic ++ version)) = none := rfl
example : decodePayload? (List.toByteArray (magic ++ version ++ [11, 3, 1, 1, 1])) = none := rfl

example : sectionSize 124 = 127 := by rw [sectionSize, encU32.eq_def]; decide
example : sectionSize 125 = 128 := by rw [sectionSize, encU32.eq_def]; decide
example : sectionSize 127 = 130 := by rw [sectionSize, encU32.eq_def]; decide
example : sectionSize 128 = 132 := by
  rw [sectionSize, encU32.eq_def, ite_eq_right (by decide : ¬ 128 < 128), encU32.eq_def]
  decide

private theorem large_size {length : Nat} (lower : 2 ^ 28 ≤ length) (upper : length < 2 ^ 32) :
    sectionSize length = length + 7 := by
  have width1 : ¬ length < 128 := by omega
  have width2 : ¬ length / 128 < 128 := by omega
  have width3 : ¬ length / 128 / 128 < 128 := by omega
  have width4 : ¬ length / 128 / 128 / 128 < 128 := by omega
  have width5 : length / 128 / 128 / 128 / 128 < 128 := by omega
  rw [sectionSize, encU32.eq_def, ite_eq_right width1, encU32.eq_def, ite_eq_right width2, encU32.eq_def,
    ite_eq_right width3, encU32.eq_def, ite_eq_right width4, encU32.eq_def, ite_eq_left width5]
  simp
  omega

example : Fits (2 ^ 32 - 8) := ⟨by decide, by rw [large_size (by decide) (by decide)]; decide⟩
example (reject : Fits (2 ^ 32 - 7)) : False := by
  have overflow := reject.body
  rw [large_size (by decide) (by decide)] at overflow
  omega
example (reject : Fits (2 ^ 32)) : False := (by decide : ¬ (2 ^ 32 : Nat) < 2 ^ 32) reject.payload

#print axioms raw_sound
#print axioms decode_encode
#print axioms RawModule.roundtrip
#print axioms IntrinsicModule.roundtrip
#print axioms decodePayload_sound
#print axioms decodeIntrinsic_roundtrip
