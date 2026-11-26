module

public import Silmaril.Formats.Arrow.BinaryView.Column.Writer.Defs
import Silmaril.Formats.Arrow.Writer.Thms
import Silmaril.Prelude.Bytes.Write.Thms
import Init.Data.List.Nat.TakeDrop
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.BinaryView.Column.Writer

open Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.BinaryView.Column.Writer

private theorem fold_join (pieces : List KBytes) (wf : ∀ b ∈ pieces, b.wf = true) :
    (pieces.foldr (· ++ ·) KBytes.empty).wf = true ∧
      (pieces.foldr (· ++ ·) KBytes.empty).toList = pieces.flatMap KBytes.toList := by
  induction pieces with
  | nil => exact ⟨rfl, rfl⟩
  | cons first rest ih =>
    obtain ⟨tailWf, tailBytes⟩ := ih (fun b h => wf b (List.mem_cons_of_mem _ h))
    exact ⟨KBytes.wf_append (wf first (by simp)) tailWf,
      by simp [KBytes.toList_append, tailBytes]⟩

private theorem joinAux_spec (fuel : Nat) (pieces : List KBytes)
    (wf : ∀ b ∈ pieces, b.wf = true) :
    (joinAux fuel pieces).wf = true ∧ (joinAux fuel pieces).toList = pieces.flatMap KBytes.toList := by
  induction fuel generalizing pieces with
  | zero => exact fold_join pieces wf
  | succ fuel ih =>
    match pieces with
    | [] => exact ⟨rfl, rfl⟩
    | [first] => exact ⟨wf first (by simp), by simp [joinAux]⟩
    | first :: second :: rest =>
      let pieces := first :: second :: rest
      let mid := pieces.length / 2
      obtain ⟨leftWf, leftBytes⟩ := ih (pieces.take mid) (fun b h => wf b (List.mem_of_mem_take h))
      obtain ⟨rightWf, rightBytes⟩ := ih (pieces.drop mid) (fun b h => wf b (List.mem_of_mem_drop h))
      change (joinAux fuel (pieces.take mid) ++ joinAux fuel (pieces.drop mid)).wf = true ∧
        (joinAux fuel (pieces.take mid) ++ joinAux fuel (pieces.drop mid)).toList = pieces.flatMap KBytes.toList
      refine ⟨KBytes.wf_append leftWf rightWf, ?_⟩
      rw [KBytes.toList_append, leftBytes, rightBytes, ← List.flatMap_append, List.take_append_drop]

theorem join_spec (pieces : List KBytes) (wf : ∀ b ∈ pieces, b.wf = true) :
    (join pieces).wf = true ∧ (join pieces).toList = pieces.flatMap KBytes.toList ∧
      (join pieces).len = (pieces.map KBytes.len).sum := by
  obtain ⟨joined, bytes⟩ := joinAux_spec (pieces.length.log2 + 1) pieces wf
  refine ⟨joined, bytes, ?_⟩
  change (joinAux (pieces.length.log2 + 1) pieces).len = _
  rw [← KBytes.length_toList _ joined, bytes, List.length_flatMap]
  congr 1
  exact List.map_congr_left (fun b member => KBytes.length_toList b (wf b member))

/-- A byte piece at a given offset in a carrier. The witness is independent of
the shape of either byte tree. -/
def Window (source piece : KBytes) (offset : Nat) : Prop :=
  ∃ front tail, source.toList = front ++ piece.toList ++ tail ∧ front.length = offset

theorem Window.fromSlice (source : KBytes) (wf : source.wf = true) (offset width : Nat)
    (fits : offset + width ≤ source.len) : Window source (source.slice offset width) offset := by
  have len := KBytes.length_toList source wf
  refine ⟨source.toList.take offset, source.toList.drop (offset + width), ?_, by simp; omega⟩
  rw [KBytes.toList_slice _ _ _ wf fits, List.append_assoc, ← List.drop_drop (i := width),
    List.take_append_drop, List.take_append_drop]

theorem Window.bounds {source piece : KBytes} {offset : Nat} (window : Window source piece offset)
    (sourceWf : source.wf = true) (pieceWf : piece.wf = true) : offset + piece.len ≤ source.len := by
  obtain ⟨front, tail, bytes, off⟩ := window
  have whole := congrArg List.length bytes
  simp only [List.length_append, KBytes.length_toList _ sourceWf, KBytes.length_toList _ pieceWf, off] at whole
  omega

theorem Window.bytes {source piece : KBytes} {offset : Nat} (window : Window source piece offset)
    (sourceWf : source.wf = true) (pieceWf : piece.wf = true) :
    (source.slice offset piece.len).toList = piece.toList := by
  rw [KBytes.toList_slice _ _ _ sourceWf (window.bounds sourceWf pieceWf)]
  obtain ⟨front, tail, bytes, off⟩ := window
  rw [bytes, ← off, List.append_assoc, List.drop_append_length,
    ← KBytes.length_toList piece pieceWf, List.take_append_length]

theorem Window.read {source piece : KBytes} {offset : Nat} (window : Window source piece offset)
    (sourceWf : source.wf = true) (pieceWf : piece.wf = true) :
    source.read offset piece.len = piece.read 0 piece.len := by
  have fits := window.bounds sourceWf pieceWf
  rw [KBytes.read_eq _ _ _ sourceWf fits, KBytes.read_eq _ _ _ pieceWf (by simp),
    ← KBytes.toList_slice _ _ _ sourceWf fits, window.bytes sourceWf pieceWf]
  simp [← KBytes.length_toList piece pieceWf]

theorem Window.trans {source piece part : KBytes} {base offset : Nat}
    (outer : Window source piece base) (inner : Window piece part offset) :
    Window source part (base + offset) := by
  obtain ⟨front, tail, whole, off⟩ := outer
  obtain ⟨pre, post, center, start⟩ := inner
  exact ⟨front ++ pre, post ++ tail, by simp [whole, center, List.append_assoc], by simp [off, start]⟩

private theorem leftWindow (left right : KBytes) : Window (left ++ right) left 0 :=
  ⟨[], right.toList, rfl, rfl⟩

private theorem rightWindow (left right : KBytes) (wf : left.wf = true) :
    Window (left ++ right) right left.len :=
  ⟨left.toList, [], by simp [KBytes.toList_append], KBytes.length_toList left wf⟩

theorem join_window {pieces : List KBytes} (wf : ∀ b ∈ pieces, b.wf = true) {index : Nat}
    (bound : index < pieces.length) : Window (join pieces) pieces[index] ((pieces.take index).map KBytes.len).sum := by
  have frontWf (b) (mem : b ∈ pieces.take index) := wf b (List.mem_of_mem_take mem)
  have front := join_spec (pieces.take index) frontWf
  refine ⟨(pieces.take index).flatMap KBytes.toList, (pieces.drop (index + 1)).flatMap KBytes.toList, ?_, ?_⟩
  · rw [(join_spec pieces wf).2.1, List.append_assoc, ← List.flatMap_cons, ← List.flatMap_append,
      ← List.drop_eq_getElem_cons bound, List.take_append_drop]
  · rw [← front.2.1, KBytes.length_toList _ front.1, front.2.2]

theorem raw_wf {value : Option KBytes} (valid : (value.map KBytes.wf).getD true = true) :
    (value.getD KBytes.empty).wf = true := by
  cases value with
  | none => rfl
  | some => exact valid

theorem raw_length (value : Option KBytes) : (value.getD KBytes.empty).len = valueSize KBytes.len value := by
  cases value <;> rfl

theorem longPart_length (value : Option KBytes) : (longPart value).len = longSize (valueSize KBytes.len value) := by
  simp only [longPart, longSize]
  rw [← raw_length]
  split <;> rfl

theorem longPart_wf {value : Option KBytes} (wf : (value.getD KBytes.empty).wf = true) :
    (longPart value).wf = true := by
  simp only [longPart]
  split <;> first | exact wf | rfl

theorem slot_length (offset : Nat) (value : Option KBytes) : (slot offset value).len = 16 := by
  simp only [slot]
  split
  · change 4 + ((value.getD KBytes.empty).len + (12 - (value.getD KBytes.empty).len)) = 16
    omega
  · change 4 + (((value.getD KBytes.empty).slice 0 4).len + (4 + 4)) = 16
    rw [KBytes.len_slice]

theorem slot_wf (offset : Nat) {value : Option KBytes}
    (wf : (value.getD KBytes.empty).wf = true) : (slot offset value).wf = true := by
  simp only [slot]
  split
  · exact KBytes.wf_append rfl (KBytes.wf_append wf rfl)
  · exact KBytes.wf_append rfl (KBytes.wf_append (KBytes.wf_slice _ _ _ wf (by omega))
      (KBytes.wf_append rfl rfl))

theorem slots_length (offset : Nat) (values : List (Option KBytes)) : (slots offset values).length = values.length := by
  induction values generalizing offset <;> simp [slots, *]

theorem slots_lengths (offset : Nat) (values : List (Option KBytes)) :
    (slots offset values).map KBytes.len = List.replicate values.length 16 := by
  induction values generalizing offset <;> simp [slots, slot_length, List.replicate_succ, *]

theorem slots_wf (offset : Nat) (values : List (Option KBytes))
    (wf : ∀ value ∈ values, (value.getD KBytes.empty).wf = true) :
    ∀ piece ∈ slots offset values, piece.wf = true := by
  induction values generalizing offset with
  | nil => simp [slots]
  | cons value rest ih =>
    intro piece member
    rcases List.mem_cons.mp member with same | tail
    · subst piece
      exact slot_wf _ (wf value (by simp))
    · exact ih _ (fun v h => wf v (List.mem_cons_of_mem _ h)) _ tail

theorem slots_at (offset : Nat) (values : List (Option KBytes)) (index : Nat)
    (bound : index < values.length) :
    (slots offset values)[index]'(by rw [slots_length]; exact bound) =
      slot (offset + longBytes KBytes.len (values.take index)) values[index] := by
  induction values generalizing offset index with
  | nil => simp at bound
  | cons value rest ih =>
    cases index with
    | zero => simp [slots, longBytes]
    | succ index =>
      simp only [slots, List.getElem_cons_succ]
      rw [ih _ _ (by simpa using bound)]
      simp [List.take_succ_cons, longBytes, longPart_length, Nat.add_assoc]

theorem views_window (values : List (Option KBytes)) (wf : ∀ v ∈ values, (v.getD KBytes.empty).wf = true)
    (index : Nat) (bound : index < values.length) :
    Window (join (slots 0 values)) (slot (longBytes KBytes.len (values.take index)) values[index]) (16 * index) := by
  have valid := slots_wf 0 values wf
  have inSlots : index < (slots 0 values).length := by rwa [slots_length]
  have window := join_window valid inSlots
  rw [slots_at, Nat.zero_add, List.map_take, slots_lengths, List.take_replicate,
    List.sum_replicate_nat, Nat.min_eq_left (Nat.le_of_lt bound), Nat.mul_comm] at window
  exact window

theorem long_window (values : List (Option KBytes)) (wf : ∀ v ∈ values, (v.getD KBytes.empty).wf = true)
    (index : Nat) (bound : index < values.length) :
    Window (join (values.map longPart)) (longPart values[index]) (longBytes KBytes.len (values.take index)) := by
  have valid (b) (member : b ∈ values.map longPart) : b.wf = true := by
    obtain ⟨value, hv, rfl⟩ := List.mem_map.mp member
    exact longPart_wf (wf value hv)
  have window := join_window valid (index := index) (by rw [List.length_map]; exact bound)
  simpa [← List.map_take, List.map_map, Function.comp_def, longPart_length, longBytes] using window

theorem data_spec (values : List (Option KBytes)) (wf : ∀ v ∈ values, (v.getD KBytes.empty).wf = true) :
    let data := join (values.map longPart)
    data.wf = true ∧ data.toList = values.flatMap (KBytes.toList ∘ longPart) ∧
      data.len = longBytes KBytes.len values := by
  have allParts (piece) (mem : piece ∈ values.map longPart) : piece.wf = true := by
    obtain ⟨value, member, rfl⟩ := List.mem_map.mp mem
    exact longPart_wf (wf value member)
  simpa [List.flatMap_map, List.map_map, Function.comp_def, longPart_length, longBytes]
    using join_spec (values.map longPart) allParts

private theorem readWord {value : Nat} (fit : value < 2^32) :
    (KBytes.leaf 4 value).read 0 4 = value := by
  simp only [KBytes.read, Nat.mul_zero, Nat.shiftRight_zero]
  exact Nat.mod_eq_of_lt fit

theorem encoded_slot (values : List (Option KBytes))
    (sources : ∀ v ∈ values, (v.getD KBytes.empty).wf = true)
    (signed : longBytes KBytes.len values < 2^31) (index : Nat) (bound : index < values.length) :
    SlotEncoding (encode values).buffers index (longBytes KBytes.len (values.take index)) values[index] := by
  let value := values[index]
  let raw := value.getD KBytes.empty
  let view := join (slots 0 values)
  let data := join (values.map longPart)
  let offset := longBytes KBytes.len (values.take index)
  let start := 16 * index
  let lengthWord := KBytes.leaf 4 raw.len
  let padding := KBytes.leaf (12 - raw.len) 0
  let firstBytes := raw.slice 0 4
  let bufferWord := KBytes.leaf 4 0
  let offsetWord := KBytes.leaf 4 offset
  have rawWf : raw.wf = true := sources _ (List.getElem_mem bound)
  have viewWf := (join_spec _ (slots_wf 0 values sources)).1
  have selected := views_window values sources index bound
  have sourceData := data_spec values sources
  have dataWf : data.wf = true := sourceData.1
  have dataLen : data.len = longBytes KBytes.len values := sourceData.2.2
  have rawWin : Window data (longPart value) offset := long_window values sources index bound
  have external (large : 12 < raw.len) : Window data raw offset := by
    have part : longPart value = raw := by
      change (if 12 < raw.len then raw else KBytes.empty) = raw
      rw [ite_eq_left large]
    rwa [part] at rawWin
  have lengthWin : Window (slot offset value) lengthWord 0 := by
    simp only [slot, lengthWord, raw]
    split <;> exact leftWindow _ _
  have lengthRead := (selected.trans lengthWin).read viewWf (by rfl)
  have lengthFit : raw.len < 2^31 := by
    by_cases small : raw.len ≤ 12
    · omega
    · have bounds := (external (by omega)).bounds dataWf rawWf
      omega
  change Body.validAt (Arrow.Writer.emitBitmap values) index = some value.isSome ∧
    view.read start 4 = raw.len ∧ raw.len < 2^31 ∧
    if raw.len ≤ 12 then
      view.read (start + 4 + raw.len) (12 - raw.len) = 0 ∧
      (view.slice (start + 4) raw.len).toList = raw.toList
    else
      view.read (start + 8) 4 = 0 ∧ view.read (start + 12) 4 = offset ∧ offset < 2^31 ∧
      ∃ carrier, (if data.len = 0 then (#[] : Array KBytes) else #[data])[0]? = some carrier ∧
        carrier.wf = true ∧ offset + raw.len ≤ carrier.len ∧
        view.read (start + 4) 4 = carrier.read offset 4 ∧
        (carrier.slice offset raw.len).toList = raw.toList
  refine ⟨Arrow.Writer.emitBitmap_valid values index bound, ?_, lengthFit, ?_⟩
  · change view.read (start + 0) 4 = (KBytes.leaf 4 raw.len).read 0 4 at lengthRead
    rwa [Nat.add_zero, readWord (by omega)] at lengthRead
  by_cases small : raw.len ≤ 12
  · rw [ite_eq_left small]
    have inside : Window (slot offset value) (raw ++ padding) 4 := by
      simp only [slot, ite_eq_left (show (value.getD KBytes.empty).len ≤ 12 from small)]
      exact rightWindow lengthWord (raw ++ padding) (by rfl)
    have inlineBytes := selected.trans (inside.trans (leftWindow raw padding))
    have paddingBytes := selected.trans (inside.trans (rightWindow raw padding rawWf))
    have zeros := paddingBytes.read viewWf (by rfl)
    refine ⟨?_, ?_⟩
    · change view.read (start + (4 + raw.len)) (12 - raw.len) = padding.read 0 (12 - raw.len) at zeros
      simpa only [padding, KBytes.read, Nat.zero_shiftRight, Nat.zero_mod, Nat.add_assoc] using zeros
    · have bytes := inlineBytes.bytes viewWf rawWf
      change (view.slice (start + (4 + 0)) raw.len).toList = raw.toList at bytes
      exact bytes
  · rw [ite_eq_right small]
    have firstWf : firstBytes.wf = true := KBytes.wf_slice _ _ _ rawWf (by omega)
    have inside : Window (slot offset value) (firstBytes ++ (bufferWord ++ offsetWord)) 4 := by
      simp only [slot, ite_eq_right (show ¬ (value.getD KBytes.empty).len ≤ 12 from small)]
      exact rightWindow lengthWord (firstBytes ++ (bufferWord ++ offsetWord)) (by rfl)
    have afterPrefix := inside.trans (rightWindow firstBytes (bufferWord ++ offsetWord) firstWf)
    have prefixWin := selected.trans (inside.trans (leftWindow firstBytes (bufferWord ++ offsetWord)))
    have indexWin := selected.trans (afterPrefix.trans (leftWindow bufferWord offsetWord))
    have offsetWin := selected.trans (afterPrefix.trans (rightWindow bufferWord offsetWord (by rfl)))
    have payloadWin := external (by omega)
    have within := payloadWin.bounds dataWf rawWf
    have dataNonempty : data.len ≠ 0 := by omega
    have offsetFit : offset < 2^31 := by omega
    have headSize : firstBytes.len = 4 := KBytes.len_slice _ _ _
    refine ⟨?_, ?_, offsetFit, data, ?_, dataWf, within, ?_, payloadWin.bytes dataWf rawWf⟩
    · have word := indexWin.read viewWf (by rfl)
      change view.read (start + ((4 + firstBytes.len) + 0)) 4 = (KBytes.leaf 4 0).read 0 4 at word
      rwa [headSize, readWord (by decide)] at word
    · have word := offsetWin.read viewWf (by rfl)
      change view.read (start + ((4 + firstBytes.len) + 4)) 4 = (KBytes.leaf 4 offset).read 0 4 at word
      rwa [headSize, readWord (by omega)] at word
    · simp [dataNonempty]
    · have rawPrefix := Window.fromSlice raw rawWf 0 4 (by omega)
      have inData := (payloadWin.trans rawPrefix).read dataWf firstWf
      have inView := prefixWin.read viewWf firstWf
      change data.read (offset + 0) firstBytes.len = firstBytes.read 0 firstBytes.len at inData
      change view.read (start + (4 + 0)) firstBytes.len = firstBytes.read 0 firstBytes.len at inView
      rw [headSize, Nat.add_zero] at inData
      rw [headSize] at inView
      exact inView.trans inData.symm

end Silmaril.Proofs.Formats.Arrow.BinaryView.Column.Writer
