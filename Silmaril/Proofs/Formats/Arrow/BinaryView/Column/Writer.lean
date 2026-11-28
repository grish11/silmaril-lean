module

public import Silmaril.Formats.Arrow.BinaryView.Column.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.BinaryView.Column.Writer.Layout
import Silmaril.Formats.Arrow.Writer.Thms
import Silmaril.Prelude.Bytes.Thms
import Init.Data.List.Nat.Sum
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.BinaryView.Column.Writer

open Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.BinaryView.Column
open Silmaril.Formats.Arrow.BinaryView.Column.Writer

private structure InputBounds {α : Type} (limits : BinaryView.Column.Limits) (nullable : Bool)
    (length : α → Nat) (values : List (Option α)) : Prop where
  rows : values.length ≤ limits.rows
  nulls : nullable = true ∨ values.countP Option.isNone = 0
  value : ∀ value ∈ values, valueSize length value ≤ limits.valueBytes
  signed : longBytes length values < 2^31
  data : dataCount (longBytes length values) ≤ limits.dataBuffers
  buffers : bitmapBytes values.length + 16 * values.length + longBytes length values ≤ limits.bufferBytes
  output : (values.map (valueSize length)).sum ≤ limits.outputBytes

private theorem checked_bounds {α : Type} {limits : BinaryView.Column.Limits} {nullable : Bool} {length : α → Nat}
    {values : List (Option α)} (checked : checkInput limits nullable length values = .ok ()) :
    InputBounds limits nullable length values := by
  simp only [checkInput] at checked
  split at checked <;> try contradiction
  rename_i rows
  split at checked <;> try contradiction
  rename_i required
  split at checked <;> try contradiction
  rename_i valueLimit
  split at checked <;> try contradiction
  rename_i signed
  split at checked <;> try contradiction
  rename_i dataLimit
  split at checked <;> try contradiction
  rename_i bufferLimit
  split at checked <;> try contradiction
  rename_i outputLimit
  refine ⟨by omega, ?_, ?_, by omega, by omega, by omega, by omega⟩
  · by_cases admitted : nullable = true
    · exact .inl admitted
    · right
      have noNull : values.any Option.isNone = false := by
        cases nullable <;> cases found : values.any Option.isNone <;>
          simp_all only [Bool.not_false, Bool.true_and, Bool.false_and, Bool.not_eq_true]
      exact List.countP_eq_zero.mpr (List.any_eq_false.mp noNull)
  · intro x member
    have allSmall : values.any (fun value => decide (limits.valueBytes < valueSize length value)) = false :=
      Bool.eq_false_iff.mpr valueLimit
    have small := (List.any_eq_false.mp allSmall) x member
    simpa using small

private theorem encoded_layout {limits : BinaryView.Column.Limits} {nullable : Bool} {values : List (Option KBytes)}
    (bounds : InputBounds limits nullable KBytes.len values)
    (wf : ∀ value ∈ values, (value.getD KBytes.empty).wf = true) :
    Layout limits nullable values (encode values) := by
  let result := encode values
  let data := join (values.map longPart)
  have joined := data_spec values wf
  have dataWf : data.wf = true := joined.1
  have dataContents : data.toList = values.flatMap (KBytes.toList ∘ longPart) := joined.2.1
  have dataLen : data.len = longBytes KBytes.len values := joined.2.2
  have views := join_spec _ (slots_wf 0 values wf)
  have bitmapLength : result.buffers.validity.len = bitmapBytes values.length :=
    Arrow.Writer.emitBitmap_length values
  have viewsLength : result.buffers.payload.views.len = 16 * values.length := by
    change (join (slots 0 values)).len = _
    rw [views.2.2, slots_lengths, List.sum_replicate_nat, Nat.mul_comm]
  have count : result.buffers.payload.data.size = dataCount (longBytes KBytes.len values) := by
    change (if data.len = 0 then (#[] : Array KBytes) else #[data]).size = _
    rw [← dataLen]
    by_cases zero : data.len = 0 <;> simp [dataCount, zero]
  have size : result.buffers.byteCount =
      bitmapBytes values.length + 16 * values.length + longBytes KBytes.len values := by
    rw [Buffers.byteCount, bitmapLength, viewsLength, ← dataLen]
    change (if data.len = 0 then (#[] : Array KBytes) else #[data]).foldl
      (fun total bytes => total + bytes.len) (bitmapBytes values.length + 16 * values.length) = _
    by_cases zero : data.len = 0 <;> simp [zero]
  have exactData : result.buffers.payload.data.toList.flatMap KBytes.toList =
      values.flatMap (KBytes.toList ∘ longPart) := by
    change ((if data.len = 0 then (#[] : Array KBytes) else #[data]).toList.flatMap KBytes.toList) = _
    rw [← dataContents]
    by_cases zero : data.len = 0
    · have empty : data.toList = [] :=
        List.length_eq_zero_iff.mp ((KBytes.length_toList data dataWf).trans zero)
      simp [zero, empty]
    · simp [zero]
  have buffersWf : result.buffers.payload.data.all (·.wf) = true := by
    change (if data.len = 0 then (#[] : Array KBytes) else #[data]).all KBytes.wf = true
    by_cases zero : data.len = 0 <;> simp [zero, dataWf]
  have bitmapWf : result.buffers.validity.wf = true := Arrow.Writer.emitWords_wf _ _
  have viewWf : result.buffers.payload.views.wf = true := views.1
  have bitmapFits : Body.BitmapExtent result.buffers.validity values.length := by
    unfold Body.BitmapExtent
    rw [bitmapLength]
    right
    unfold bitmapBytes
    omega
  have nullsFit : values.countP Option.isNone ≤ values.length := List.countP_le_length
  refine ⟨rfl, ?_, rfl, bitmapLength, viewsLength, count, size, exactData, bounds.signed, bounds.value,
    bounds.output, encoded_slot values wf bounds.signed⟩
  refine ⟨bounds.rows, by rw [count]; exact bounds.data, by rw [size]; exact bounds.buffers,
    ⟨bitmapWf, viewWf, buffersWf⟩, bitmapFits, ?_, nullsFit, bounds.nulls⟩
  exact Nat.le_of_eq viewsLength.symm

theorem emitBinary_layout {limits : BinaryView.Column.Limits} {nullable : Bool} {values : List (Option KBytes)}
    {result : Emitted} (written : emitBinary limits nullable values = .ok result) :
    Layout limits nullable values result := by
  cases checked : checkInput limits nullable KBytes.len values with
  | error => simp [emitBinary, checked, bind, Except.bind] at written
  | ok success =>
    cases success
    cases source : values.all (fun value => (value.map KBytes.wf).getD true) with
    | false => simp [emitBinary, checked, source, bind, Except.bind] at written
    | true =>
      simp [emitBinary, checked, source, bind, Except.bind, pure, Except.pure] at written
      subst result
      exact encoded_layout (checked_bounds checked) (fun v mem => raw_wf (List.all_eq_true.mp source v mem))

private theorem utf8Length (text : String) : (utf8Bytes text).len = text.utf8ByteSize := by
  rw [utf8Bytes, Arrow.Writer.emitWords_length]
  simp only [Nat.one_mul, List.length_map, Array.length_toList]
  rfl

theorem utf8Octets (text : String) : (utf8Bytes text).toList = text.toByteArray.data.toList :=
  Arrow.Writer.emitBytes_bytes _

theorem utf8Bytes_valid (text : String) : String.fromUTF8? (utf8Bytes text).toByteArray = some text := by
  have bytes : (utf8Bytes text).toByteArray = text.toByteArray :=
    ByteArray.ext (Array.toList_inj.mp (utf8Octets text))
  simp [bytes, String.fromUTF8?, text.isValidUTF8]

private theorem utf8ValueSize (value : Option String) :
    valueSize KBytes.len (value.map utf8Bytes) = valueSize String.utf8ByteSize value := by
  cases value <;> simp [valueSize, utf8Length]

private theorem utf8LongBytes (values : List (Option String)) :
    longBytes KBytes.len (values.map (·.map utf8Bytes)) = longBytes String.utf8ByteSize values := by
  simp only [longBytes, List.map_map, Function.comp_def, utf8ValueSize]

private theorem noneMap {α β : Type} (f : α → β) (value : Option α) :
    (value.map f).isNone = value.isNone := by cases value <;> rfl

theorem emitUtf8_layout {limits : BinaryView.Column.Limits} {nullable : Bool} {values : List (Option String)}
    {result : Emitted} (written : emitUtf8 limits nullable values = .ok result) :
    Layout limits nullable (values.map (·.map utf8Bytes)) result := by
  cases checked : checkInput limits nullable String.utf8ByteSize values with
  | error => simp [emitUtf8, checked, bind, Except.bind] at written
  | ok success =>
    cases success
    simp [emitUtf8, checked, bind, Except.bind, pure, Except.pure] at written
    subst result
    have bounds := checked_bounds checked
    apply encoded_layout
    · refine ⟨by simpa using bounds.rows, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [List.countP_map, Function.comp_def, noneMap] using bounds.nulls
      · intro bytes member
        obtain ⟨value, inValues, rfl⟩ := List.mem_map.mp member
        rw [utf8ValueSize]
        exact bounds.value value inValues
      · simpa only [utf8LongBytes] using bounds.signed
      · simpa only [utf8LongBytes] using bounds.data
      · simpa only [List.length_map, utf8LongBytes] using bounds.buffers
      · simpa only [List.map_map, Function.comp_def, utf8ValueSize] using bounds.output
    · intro bytes member
      obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
      cases value with
      | none => rfl
      | some => exact Arrow.Writer.emitWords_wf _ _

end Silmaril.Proofs.Formats.Arrow.BinaryView.Column.Writer
