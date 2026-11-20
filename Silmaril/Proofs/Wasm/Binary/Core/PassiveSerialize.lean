module

public import Silmaril.Wasm.Binary.Core.PassiveSerialize.Defs
import Silmaril.Wasm.Binary.Packed.Passive.Thms
import Silmaril.Wasm.Tools.Meta.Leb.Thms
public import Silmaril.Wasm.Validation.Intrinsic.Thms

public section

namespace Silmaril.Proofs.Wasm.Binary.Core.PassiveSerialize

open Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core.Decode
open Silmaril.Wasm.Binary.Core.PassiveSerialize
open Silmaril.Wasm.Tools.Meta (encU32 mul_split128 toNat_toUInt8_of_lt)

private theorem bind_at {α β : Type} {reader : DecodeM α} {nextReader : α → DecodeM β}
    {start next : Cursor} {value : α} (ok : reader.run start = .ok (value, next)) :
    (reader >>= nextReader).run start = (nextReader value).run next := by
  rw [StateT.run_bind, ok]
  rfl

theorem byte_at {bytes : ByteArray} {pos : Nat} {byte : UInt8} {tail : List UInt8}
    (rest : (Cursor.mk bytes pos).rest = byte :: tail) :
    readByte.run ⟨bytes, pos⟩ = .ok (byte, ⟨bytes, pos + 1⟩) := by
  have len := congrArg List.length rest
  simp [Cursor.rest] at len
  have bound : pos < bytes.size := by omega
  have eq := congrArg (·[0]?) rest
  simp only [Cursor.rest, List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at eq
  have atPos : bytes[pos] = byte := by
    rw [List.getElem?_eq_getElem (by simpa using bound)] at eq
    simpa [ByteArray.getElem_eq_getElem_data] using Option.some.inj eq
  simp [readByte, StateT.run_bind, StateT.run_get, StateT.run_set, bound, atPos]
  rfl

private theorem after_byte {bytes : ByteArray} {pos : Nat} {byte : UInt8} {tail : List UInt8}
    (rest : (Cursor.mk bytes pos).rest = byte :: tail) : (Cursor.mk bytes (pos + 1)).rest = tail := by
  simp only [Cursor.rest] at rest ⊢
  rw [← List.drop_drop, rest]
  rfl

private theorem go_at (fuel : Nat) {bytes : ByteArray} {pos shift number : Nat} {tail : List UInt8}
    (bound : number < 128 ^ fuel) (positive : 0 < fuel)
    (rest : (Cursor.mk bytes pos).rest = encU32 number ++ tail) :
    (readU.go shift fuel).run ⟨bytes, pos⟩ =
      .ok (number * 2 ^ shift, ⟨bytes, pos + (encU32 number).length⟩) := by
  induction fuel generalizing pos shift number with
  | zero => omega
  | succ fuel ih =>
    rw [readU.go]
    by_cases small : number < 128
    · rw [encU32, ite_eq_left small] at rest ⊢
      rw [bind_at (byte_at rest)]
      simp [toNat_toUInt8_of_lt (show number < 256 by omega), small, Nat.mod_eq_of_lt small,
        StateT.run_pure]
      rfl
    · rw [encU32, ite_eq_right small] at rest ⊢
      have byteEq := toNat_toUInt8_of_lt (show number % 128 + 128 < 256 by omega)
      have cont : ¬ number % 128 + 128 < 128 := by omega
      have reduced : number / 128 < 128 ^ fuel := by
        apply Nat.div_lt_of_lt_mul
        rwa [Nat.mul_comm 128, ← Nat.pow_succ]
      have nonzero : 0 < fuel := by
        by_contra h
        have : fuel = 0 := by omega
        simp [this] at bound
        omega
      rw [bind_at (byte_at rest)]
      simp only [byteEq, cont, ↓reduceIte, bind_at (ih reduced nonzero (after_byte rest))]
      simp only [StateT.run_pure, List.length_cons]
      have val : (number % 128 + 128) % 128 * 2 ^ shift + number / 128 * 2 ^ (shift + 7) =
          number * 2 ^ shift := by
        rw [show (number % 128 + 128) % 128 = number % 128 by omega,
          mul_split128 number (2 ^ shift), Nat.pow_add]
      rw [val, Nat.add_assoc, Nat.add_comm 1]
      rfl

theorem u32_at {bytes : ByteArray} {pos number : Nat} {tail : List UInt8}
    (bound : number < 2 ^ 32) (rest : (Cursor.mk bytes pos).rest = encU32 number ++ tail) :
    (readU 32).run ⟨bytes, pos⟩ = .ok (number, ⟨bytes, pos + (encU32 number).length⟩) := by
  unfold readU
  rw [bind_at (go_at 5 (by omega) (by decide) rest)]
  rw [show number * 2 ^ 0 = number by simp, ite_eq_left bound]
  rfl

private theorem rest_at (pre tail : List UInt8) :
    (Cursor.mk (pre ++ tail).toByteArray pre.length).rest = tail := by
  simp [Cursor.rest]

theorem bytes_at {bytes : ByteArray} {pos : Nat} {part tail : List UInt8}
    (rest : (Cursor.mk bytes pos).rest = part ++ tail) (bound : pos ≤ bytes.size) :
    (readBytes part.length).run ⟨bytes, pos⟩ = .ok (part.toByteArray, ⟨bytes, pos + part.length⟩) := by
  have len := congrArg List.length rest
  simp [Cursor.rest] at len
  have fits : pos + part.length ≤ bytes.size := by omega
  simp only [readBytes, StateT.run_bind, StateT.run_get, pure_bind, fits, ↓reduceIte,
    StateT.run_set, StateT.run_pure]
  have eq : extractForKernel bytes pos (pos + part.length) = part.toByteArray := by
    apply ByteArray.ext (Array.ext' ?_)
    simp [extractForKernel, List.extract_eq_take_drop]
    rw [show bytes.data.toList.drop pos = part ++ tail from rest, List.take_left]
  rw [eq]
  rfl

theorem decode_encode (payload : Payload) : Core.decode? (encode payload) = some (raw payload.val) := by
  let hdr := magic ++ version
  let sizeBytes := encU32 (sectionSize payload.val.size)
  let lenBytes := encU32 payload.val.size
  let bytes := encode payload
  let start := 9 + sizeBytes.length
  let payloadStart := start + 1 + 1 + lenBytes.length
  have sizeEq : bytes.size = payloadStart + payload.val.size := by
    simp [bytes, encode, payloadStart, start, sizeBytes, lenBytes, magic, version,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    omega
  have headerRest : (Cursor.mk bytes 0).rest = hdr ++ ([11] ++ (sizeBytes ++ ([1] ++ ([1] ++
      (lenBytes ++ payload.val.data.toList))))) := by simp [Cursor.rest, bytes, encode, hdr, sizeBytes, lenBytes]
  have header := bytes_at headerRest (Nat.zero_le _)
  have headerOk : readHeader.run ⟨bytes, 0⟩ = .ok ((), ⟨bytes, 8⟩) := by
    unfold readHeader
    rw [bind_at (show (readBytes 8).run ⟨bytes, 0⟩ = .ok (hdr.toByteArray, ⟨bytes, 8⟩) from header)]
    simp [hdr, StateT.run_pure]
    rfl
  have idRest : (Cursor.mk bytes 8).rest = 11 :: (sizeBytes ++ (1 :: 1 ::
      (lenBytes ++ payload.val.data.toList))) := rest_at hdr _
  have sizeOk := u32_at payload.property.body (after_byte idRest)
  have countRest : (Cursor.mk bytes start).rest = [1] ++ ([1] ++ (lenBytes ++ payload.val.data.toList)) := by
    have fact := rest_at (hdr ++ [11] ++ sizeBytes) ([1] ++ ([1] ++ (lenBytes ++ payload.val.data.toList)))
    have offset : (hdr ++ [11] ++ sizeBytes).length = start := by
      simp [start, show hdr.length = 8 from rfl]
      omega
    rw [offset] at fact
    simpa only [bytes, encode, hdr, sizeBytes, lenBytes, List.append_assoc] using fact
  have encOne : encU32 1 = [1] := by rw [encU32]; rfl
  have count := u32_at (number := 1) (by decide) (by rw [encOne]; exact countRest)
  have modeRest : (Cursor.mk bytes (start + 1)).rest = [1] ++ (lenBytes ++ payload.val.data.toList) :=
    after_byte countRest
  have mode := u32_at (number := 1) (by decide) (by rw [encOne]; exact modeRest)
  have lenRest : (Cursor.mk bytes (start + 1 + 1)).rest = lenBytes ++ payload.val.data.toList :=
    after_byte modeRest
  have len := u32_at payload.property.payload lenRest
  have payloadRest : (Cursor.mk bytes payloadStart).rest = payload.val.data.toList := by
    have fact := rest_at (hdr ++ [11] ++ sizeBytes ++ [1] ++ [1] ++ lenBytes) payload.val.data.toList
    have offset : (hdr ++ [11] ++ sizeBytes ++ [1] ++ [1] ++ lenBytes).length = payloadStart := by
      simp [payloadStart, start, show hdr.length = 8 from rfl]
      omega
    rw [offset] at fact
    simpa only [bytes, encode, hdr, sizeBytes, lenBytes, List.append_assoc] using fact
  have body := bytes_at (tail := []) (by simpa using payloadRest) (by rw [sizeEq]; omega)
  have bodyOk : (readBytes payload.val.size).run ⟨bytes, payloadStart⟩ =
      .ok (payload.val, ⟨bytes, bytes.size⟩) := by
    have round : payload.val.data.toList.toByteArray = payload.val := by
      apply ByteArray.ext (Array.ext' ?_)
      simp
    simpa [sizeEq, round] using body
  have sizeVal : sectionSize payload.val.size = bytes.size - start := by
    rw [sizeEq]; simp only [sectionSize, payloadStart, lenBytes]; omega
  exact Packed.decodePassive_of_reads headerOk (byte_at idRest) (by rw [sizeEq]; dsimp [payloadStart, start]; omega)
    (by rw [← sizeVal]; exact sizeOk) (by simpa only [encOne, List.length_cons, List.length_nil] using count)
    (by rw [sizeEq]; dsimp [payloadStart]; omega)
    (by simpa only [encOne, List.length_cons, List.length_nil] using mode) len sizeEq.symm bodyOk

theorem decodePayload_encode (payload : Payload) : decodePayload? (encode payload) = some payload := by
  have guard : payload.val.size < 2 ^ 32 ∧ sectionSize payload.val.size < 2 ^ 32 :=
    ⟨payload.property.payload, payload.property.body⟩
  have accepted : accept? (raw payload.val) = some ⟨payload, rfl⟩ := by
    unfold raw
    rw [accept?, dite_eq_left guard]
    exact congrArg some (Subtype.ext (Subtype.ext rfl))
  unfold decodePayload?
  rw [decode_encode]
  change ((accept? (raw payload.val)).bind fun accepted => some accepted.val) = _
  rw [accepted]
  rfl

theorem decodePayload_sound {source : ByteArray} {payload : Payload}
    (ok : decodePayload? source = some payload) : Core.decode? source = some (raw payload.val) := by
  obtain ⟨mod, decoded, accepted⟩ := Option.bind_eq_some_iff.mp ok
  obtain ⟨checked, _, eq⟩ := Option.bind_eq_some_iff.mp accepted
  cases Option.some.inj eq
  rw [decoded, checked.property]

theorem raw_extract {mod : Wasm.Module} (fits : serializable mod) : raw (extract mod fits).val = mod := by
  obtain ⟨payload, rfl⟩ := fits
  rfl

theorem decodeIntrinsic_roundtrip (mod : IntrinsicModule) :
    (decodeIntrinsic? mod.encode).map
      (fun decoded => (Quot.mk _ decoded.val : Wasm.Validation.Intrinsic.Module.Erasure iface)) =
      some (Quot.mk _ mod.val) := by
  unfold decodeIntrinsic? IntrinsicModule.encode
  rw [decodePayload_encode]
  exact congrArg some (Quot.sound (raw_extract mod.property))

end Silmaril.Proofs.Wasm.Binary.Core.PassiveSerialize
