module

public import Silmaril.Wasm.Binary.Packed.Defs

@[expose] public section

namespace Silmaril.Proofs.Wasm.Binary.Packed

open Silmaril.Wasm.Binary.Packed
open Silmaril.Wasm.Binary

private theorem bind_agrees {α β γ δ : Type} {project : α → β} {out : γ → δ}
    {packed : Reader α} {ref : Core.Decode.DecodeM β}
    {next : α → Reader γ} {nextRef : β → Core.Decode.DecodeM δ}
    (step : Agrees project packed ref) (tail : ∀ value, Agrees out (next value) (nextRef (project value))) :
    Agrees out (packed >>= next) (ref >>= nextRef) := by
  intro cursor
  simp only [StateT.run_bind]
  have eq := step cursor
  cases run : packed.run cursor with
  | error err =>
    rw [run] at eq
    rw [← eq]
    rfl
  | ok value =>
    rcases value with ⟨value, position⟩
    rw [run] at eq
    rw [← eq]
    exact tail value position

private theorem pure_agrees {α β : Type} (project : α → β) (value : α) :
    Agrees project (pure value) (pure (project value)) := fun _ => rfl

private theorem throw_agrees {α β : Type} (project : α → β) (msg : String) :
    Agrees project (throw msg) (throw msg) := fun _ => rfl

private theorem error_agrees {α β : Type} (project : α → β) (msg : String) :
    Agrees project (decodeError msg) (Core.Decode.decodeError msg) := fun _ => rfl

theorem size (cursor : Cursor) : cursor.spec.bytes.size = cursor.source.len :=
  cursor.source.length_toList cursor.wf

theorem readByte_agrees : Agrees id readByte Core.Decode.readByte := by
  intro cursor
  have same : cursor.source.toList.length = cursor.spec.bytes.size := rfl
  have pos : cursor.spec.pos = cursor.pos := rfl
  simp only [readByte, Core.Decode.readByte, StateT.run_bind, StateT.run_get, pure_bind,
    KBytes.get?_eq _ cursor.wf, pos]
  by_cases bound : cursor.pos < cursor.spec.bytes.size
  · rw [dite_eq_left bound, List.getElem?_eq_getElem (same ▸ bound)]
    rfl
  · rw [dite_eq_right bound, List.getElem?_eq_none (by rw [same]; omega)]
    rfl

theorem remaining_agrees : Agrees id remaining Core.Decode.remaining := by
  intro cursor
  change Except.ok (cursor.source.len - cursor.pos, cursor.spec) =
    Except.ok (cursor.spec.bytes.size - cursor.pos, cursor.spec)
  rw [size]

theorem readSlice_agrees (width : Nat) :
    Agrees (fun payload => payload.source.toByteArray) (readSlice width) (Core.Decode.readBytes width) := by
  intro cursor
  have pos : cursor.spec.pos = cursor.pos := rfl
  simp only [readSlice, Core.Decode.readBytes, StateT.run_bind, StateT.run_get, pure_bind, size, pos]
  by_cases bound : cursor.pos + width ≤ cursor.source.len
  · rw [dite_eq_left bound, ite_eq_left bound]
    have extracted : (cursor.source.slice cursor.pos width).toByteArray =
        Core.Decode.extractForKernel cursor.spec.bytes cursor.pos (cursor.pos + width) := by
      rw [Core.Decode.extractForKernel_eq]
      apply ByteArray.ext (Array.ext' ?_)
      simp [Cursor.spec, KBytes.toByteArray, List.extract,
        KBytes.toList_slice _ _ _ cursor.wf bound]
    change Except.ok ((cursor.source.slice cursor.pos width).toByteArray, _) = Except.ok (_, _)
    rw [extracted]
    rfl
  · rw [dite_eq_right bound, ite_eq_right bound]
    exact error_agrees (fun payload : Cursor => payload.source.toByteArray) _ cursor

private theorem readU_go_agrees (fuel shift : Nat) :
    Agrees id (readU.go shift fuel) (Core.Decode.readU.go shift fuel) := by
  induction fuel generalizing shift with
  | zero => exact throw_agrees id _
  | succ fuel ih =>
    unfold readU.go Core.Decode.readU.go
    apply bind_agrees readByte_agrees
    intro byte
    change Agrees id (if byte.toNat < 0x80 then _ else _) (if byte.toNat < 0x80 then _ else _)
    split
    · exact pure_agrees id _
    · exact bind_agrees (ih _) (fun value => pure_agrees id (_ + value))

theorem readU_agrees (bits : Nat) : Agrees id (readU bits) (Core.Decode.readU bits) := by
  unfold readU Core.Decode.readU
  apply bind_agrees (readU_go_agrees _ _)
  intro value
  simp only [id_eq]
  split
  · exact pure_agrees id _
  · exact throw_agrees id _

private theorem readS_go_agrees (fuel shift : Nat) (acc : Int) :
    Agrees id (readS.go shift fuel acc) (Core.Decode.readS.go shift fuel acc) := by
  induction fuel generalizing shift acc with
  | zero => exact throw_agrees id _
  | succ fuel ih =>
    unfold readS.go Core.Decode.readS.go
    apply bind_agrees readByte_agrees
    intro byte
    simp only [id_eq]
    split
    · split <;> exact pure_agrees id _
    · exact ih _ _

theorem readS_agrees (bits : Nat) : Agrees id (readS bits) (Core.Decode.readS bits) := by
  unfold readS Core.Decode.readS
  apply bind_agrees (readS_go_agrees _ _ _)
  intro value
  simp only [id_eq]
  split
  · exact pure_agrees id _
  · exact throw_agrees id _

theorem readHeader_agrees : Agrees id readHeader Core.Decode.readHeader := by
  unfold readHeader Core.Decode.readHeader
  apply bind_agrees (readSlice_agrees 8)
  intro payload
  change Agrees id (if payload.source.toList == _ then _ else _)
    (if payload.source.toList == _ then _ else _)
  split
  · exact pure_agrees id _
  · exact error_agrees id _

private theorem prefix_agrees : Agrees id (sectionPrefix readByte (readU 32) remaining decodeError)
    (sectionPrefix Core.Decode.readByte (Core.Decode.readU 32) Core.Decode.remaining Core.Decode.decodeError) := by
  unfold sectionPrefix
  apply bind_agrees readByte_agrees
  intro byte
  apply bind_agrees (readU_agrees 32)
  intro width
  apply bind_agrees remaining_agrees
  intro left
  change Agrees id (if width ≤ left then _ else _) (if width ≤ left then _ else _)
  split
  · exact pure_agrees id _
  · exact bind_agrees (error_agrees id _) (fun _ => pure_agrees id _)

theorem readSection_agrees :
    Agrees (fun (id, payload) => (id, payload.source.toByteArray)) readSection readSectionSpec := by
  unfold readSection readSectionSpec
  apply bind_agrees prefix_agrees
  rintro ⟨id, width⟩
  exact bind_agrees (readSlice_agrees width) (fun payload =>
    pure_agrees (fun (id, payload) => (id, payload.source.toByteArray)) (id, payload))

private theorem scanEnvelope_agrees : Agrees id readExtent readExtentSpec := by
  unfold readExtent readExtentSpec
  apply bind_agrees readSection_agrees
  rintro ⟨id, payload⟩
  change Agrees _ (pure (id, payload.source.len)) (pure (id, payload.source.toByteArray.size))
  rw [show payload.source.toByteArray.size = payload.source.len from size payload]
  exact pure_agrees _ _

private theorem scanGo_agrees (fuel rank : Nat) :
    Agrees id (scan.go readExtent remaining decodeError fuel rank)
      (scan.go readExtentSpec Core.Decode.remaining Core.Decode.decodeError fuel rank) := by
  induction fuel generalizing rank with
  | zero =>
    unfold scan.go
    apply bind_agrees remaining_agrees
    intro left
    simp only [id_eq]
    split
    · exact pure_agrees id _
    · exact error_agrees id _
  | succ fuel ih =>
    unfold scan.go
    apply bind_agrees remaining_agrees
    intro left
    simp only [id_eq]
    split
    · exact pure_agrees id _
    · apply bind_agrees scanEnvelope_agrees
      intro frame
      simp only [id_eq]
      split
      · exact bind_agrees (ih rank) (fun frames => pure_agrees id (frame :: frames))
      · split
        · exact bind_agrees (ih _) (fun frames => pure_agrees id (frame :: frames))
        · exact error_agrees id _

theorem scanFrames_agrees : Agrees id scanFrames scanFramesSpec := by
  unfold scanFrames scanFramesSpec scan
  exact bind_agrees readHeader_agrees (fun _ =>
    bind_agrees remaining_agrees (fun fuel => scanGo_agrees fuel 0))

end Silmaril.Proofs.Wasm.Binary.Packed
