module

public import Silmaril.Wasm.Binary.Packed.Passive.Defs
public import Silmaril.Wasm.Binary.Packed.Thms

@[expose] public section

namespace Silmaril.Proofs.Wasm.Binary.Packed.Passive

open Silmaril.Wasm Silmaril.Wasm.Binary
open Silmaril.Wasm.Binary.Packed (Agrees PassivePlan)
open Core.Decode

private theorem bind_at {α β : Type} {action : DecodeM α} {tail : α → DecodeM β}
    {start next : Core.Decode.Cursor} {value : α} (success : action.run start = .ok (value, next)) :
    (action >>= tail).run start = (tail value).run next := by
  rw [StateT.run_bind, success]
  rfl

private theorem remain_at (bytes : ByteArray) (pos : Nat) :
    remaining.run ⟨bytes, pos⟩ = .ok (bytes.size - pos, ⟨bytes, pos⟩) := rfl

private theorem count_at {bytes : ByteArray} {start next value : Nat}
    (encoded : (readU 32).run ⟨bytes, start⟩ = .ok (value, ⟨bytes, next⟩))
    (guard : value ≤ bytes.size - next) :
    readCount.run ⟨bytes, start⟩ = .ok (value, ⟨bytes, next⟩) := by
  unfold readCount
  rw [bind_at encoded, bind_at (remain_at bytes next), ite_eq_left guard]
  rfl

private theorem section_at {bytes payload : ByteArray} {start afterCount afterMode payloadStart width : Nat}
    (count : readCount.run ⟨bytes, start⟩ = .ok (1, ⟨bytes, afterCount⟩))
    (mode : (readU 32).run ⟨bytes, afterCount⟩ = .ok (1, ⟨bytes, afterMode⟩))
    (length : readCount.run ⟨bytes, afterMode⟩ = .ok (width, ⟨bytes, payloadStart⟩))
    (body : (readBytes width).run ⟨bytes, payloadStart⟩ = .ok (payload, ⟨bytes, bytes.size⟩)) :
    (readSectionBody 11 {}).run ⟨bytes, start⟩ =
      .ok ({ data := [⟨payload, .passive⟩] }, ⟨bytes, bytes.size⟩) := by
  have dataAt : readData.run ⟨bytes, afterCount⟩ = .ok (⟨payload, .passive⟩, ⟨bytes, bytes.size⟩) := by
    unfold readData
    rw [bind_at mode]
    change (readData.readByteVec >>= fun data => pure (⟨data, .passive⟩ : Wasm.Data)).run _ = _
    unfold readData.readByteVec
    rw [bind_assoc, bind_at length, bind_at body]
    rfl
  have vec : (readVec readData).run ⟨bytes, start⟩ = .ok ([⟨payload, .passive⟩], ⟨bytes, bytes.size⟩) := by
    unfold readVec
    rw [bind_at count, readVec.go, bind_at dataAt]
    rfl
  change (readVec readData >>= fun data => pure ({ data := data } : Sections)).run _ = _
  rw [bind_at vec]
  rfl

private theorem end_at (bytes : ByteArray) (fuel rank : Nat) (sections : Sections) :
    (readModule.go fuel rank sections).run ⟨bytes, bytes.size⟩ = .ok (sections, ⟨bytes, bytes.size⟩) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    unfold readModule.go
    rw [bind_at (remain_at bytes bytes.size), Nat.sub_self]
    rfl

private theorem full {bytes payload : ByteArray} {start : Nat}
    (header : readHeader.run ⟨bytes, 0⟩ = .ok ((), ⟨bytes, 8⟩))
    (id : readByte.run ⟨bytes, 8⟩ = .ok (11, ⟨bytes, 9⟩))
    (present : 8 < bytes.size)
    (size : (readU 32).run ⟨bytes, 9⟩ = .ok (bytes.size - start, ⟨bytes, start⟩))
    (body : (readSectionBody 11 {}).run ⟨bytes, start⟩ =
      .ok ({ data := [⟨payload, .passive⟩] }, ⟨bytes, bytes.size⟩)) :
    Core.decode? bytes = some { data := [⟨payload, .passive⟩] } := by
  have sectionStep (fuel : Nat) : (readModule.go (fuel + 1) 0 {}).run ⟨bytes, 8⟩ =
      .ok ({ data := [⟨payload, .passive⟩] }, ⟨bytes, bytes.size⟩) := by
    unfold readModule.go
    rw [bind_at (remain_at bytes 8)]
    simp only [show (bytes.size - 8 == 0) = false by simp; omega, Bool.false_eq_true, ↓reduceIte]
    rw [bind_at id, bind_at size, bind_at (remain_at bytes start)]
    simp only [Nat.le_refl, show ((11 : UInt8).toNat == 0) = false from rfl, Bool.false_eq_true,
      show 0 < sectionRank (UInt8.toNat 11) by decide, ↓reduceIte]
    rw [show UInt8.toNat (11 : UInt8) = 11 from rfl]
    rw [bind_at body, bind_at (remain_at bytes bytes.size)]
    simp only [Nat.sub_self, Nat.sub_zero, beq_self_eq_true, ↓reduceIte]
    exact end_at bytes fuel 13 _
  have loop : (readModule.go bytes.size 0 {}).run ⟨bytes, 8⟩ =
      .ok ({ data := [⟨payload, .passive⟩] }, ⟨bytes, bytes.size⟩) := by
    obtain ⟨fuel, eq⟩ : ∃ fuel, bytes.size = fuel + 1 := ⟨bytes.size - 1, by omega⟩
    simpa only [eq] using sectionStep fuel
  have read : readModule.run ⟨bytes, 0⟩ = .ok ({ data := [⟨payload, .passive⟩] }, ⟨bytes, bytes.size⟩) := by
    unfold readModule
    rw [bind_at header, bind_at (rfl : (get : DecodeM Core.Decode.Cursor).run ⟨bytes, 8⟩ = .ok _)]
    rw [bind_at loop, bind_at (remain_at bytes bytes.size)]
    simp only [Nat.sub_self]
    rfl
  unfold Core.decode? decodeModule StateT.run'
  change (match Prod.fst <$> readModule.run ⟨bytes, 0⟩ with
    | .ok result => some result
    | .error _ => none) = _
  rw [read]
  rfl

private theorem observe {α β : Type} {packed : Binary.Packed.Reader α} {ref : DecodeM β}
    {project : α → β} {cursor finish : Binary.Packed.Cursor} {value : α}
    (agrees : Agrees project packed ref) (ok : packed.run cursor = .ok (value, finish)) :
    ref.run cursor.spec = .ok (project value, finish.spec) :=
  (agrees cursor).symm.trans (congrArg (Except.map _) ok)

theorem sound {plan : PassivePlan} {source payload : KBytes} {wf : source.wf = true}
    (payloadWf : payload.wf = true) (checked : plan.Verified source wf payload) :
    Core.decode? source.toByteArray = some { data := [⟨payload.toByteArray, .passive⟩] } := by
  have lengthEq : source.toByteArray.size = source.len := source.length_toList wf
  have header := observe Binary.Packed.readHeader_agrees checked.header
  have identifier := observe Binary.Packed.readByte_agrees checked.id
  have size := observe (Binary.Packed.readU_agrees 32) checked.size
  have count := observe (Binary.Packed.readU_agrees 32) checked.count
  have mode := observe (Binary.Packed.readU_agrees 32) checked.mode
  have length := observe (Binary.Packed.readU_agrees 32) checked.length
  have countFits : 1 ≤ source.toByteArray.size - plan.afterCount := by
    rw [lengthEq]
    exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt checked.countFits)
  have lengthFits : payload.len ≤ source.toByteArray.size - plan.payloadStart := by
    rw [lengthEq, ← checked.consumesInput]
    omega
  have fits : plan.payloadStart + payload.len ≤ source.len := checked.consumesInput.le
  have extracted := KBytes.toList_eq_of_sameBytes 4096 (source.slice plan.payloadStart payload.len) payload
    (source.wf_slice _ _ wf fits) payloadWf checked.payloadMatches
  have sliceAt : (readBytes payload.len).run ⟨source.toByteArray, plan.payloadStart⟩ =
      .ok (payload.toByteArray, ⟨source.toByteArray, source.toByteArray.size⟩) := by
    simp only [readBytes, StateT.run_bind, StateT.run_get, pure_bind, Nat.le_refl, ↓reduceIte,
      StateT.run_set, StateT.run_pure, Core.Decode.extractForKernel_eq, checked.consumesInput, lengthEq]
    apply congrArg (fun bytes => Except.ok (bytes, (⟨source.toByteArray, source.len⟩ : Core.Decode.Cursor)))
    apply ByteArray.ext (Array.ext' ?_)
    change _ = payload.toList
    rw [← extracted, KBytes.toList_slice _ _ _ wf fits]
    simp [KBytes.toByteArray, List.extract, ← checked.consumesInput]
  have shape := section_at (count_at count countFits) mode (count_at length lengthFits) sliceAt
  exact full header identifier (lengthEq ▸ checked.sectionPresent) (lengthEq ▸ size) shape

end Silmaril.Proofs.Wasm.Binary.Packed.Passive
