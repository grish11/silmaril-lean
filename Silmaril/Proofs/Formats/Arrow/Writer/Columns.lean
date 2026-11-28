module

public import Silmaril.Formats.Arrow.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.Writer.Buffers
import Silmaril.Proofs.Formats.Arrow.Writer.Bitmap
import Silmaril.Prelude.Bytes.Thms
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Scan.Lemmas
import Init.Data.SInt.Lemmas
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.Writer

open Silmaril.Formats.Arrow Silmaril.Formats.Arrow.Writer

private theorem partLen (slot : Option String) :
    (utf8Part slot).length = (slot.map String.utf8ByteSize).getD 0 := by
  cases slot <;> simp [utf8Part, ← ByteArray.size_data, ← String.size_toByteArray]

theorem utf8ByteCount_length (values : List (Option String)) :
    (values.flatMap utf8Part).length = utf8ByteCount values := by
  simp [List.length_flatMap, partLen, utf8ByteCount]

private theorem offsets_length (start : Nat) (values : List (Option String)) :
    (utf8OffsetWords start values).length = values.length + 1 :=
  List.length_scanl

theorem emit_sizes (values : ColumnValues) :
    (values.emit.map KBytes.len) = values.bufferSizes := by
  cases values <;>
    simp [ColumnValues.emit, ColumnValues.encode, ColumnValues.bufferSizes, bufferParts,
      emitBitmap_length, emitWords_length, offsets_length, partLen, utf8ByteCount]

theorem emit_wf (values : ColumnValues) :
    ∀ bytes ∈ values.emit, bytes.wf = true := by
  cases values <;>
    simp [ColumnValues.emit, ColumnValues.encode, bufferParts, emitBitmap, emitWords_wf]

private theorem offsets_window (start : Nat) (values : List (Option String))
    (index : Nat) (bound : index < values.length) :
    ∃ lo hi,
      (utf8OffsetWords start values)[index]? = some lo ∧
      (utf8OffsetWords start values)[index + 1]? = some hi ∧
      start ≤ lo ∧ lo ≤ hi ∧ hi ≤ start + (values.flatMap utf8Part).length ∧
      (((values.flatMap utf8Part).drop (lo - start)).take (hi - lo)) = utf8Part values[index] := by
  induction values generalizing start index with
  | nil => simp at bound
  | cons slot values ih =>
    let span := (utf8Part slot).length
    have spanEq : (slot.map String.utf8ByteSize).getD 0 = span := (partLen slot).symm
    cases index with
    | zero =>
      refine ⟨start, start + span, ?_, ?_, Nat.le_refl _, Nat.le_add_right _ _, ?_, ?_⟩
      · simp [utf8OffsetWords]
      · cases values <;> simp [utf8OffsetWords, spanEq]
      · simp [span]
      · simp [span]
    | succ index =>
      obtain ⟨lo, hi, atLo, atHi, lower, order, upper, atBytes⟩ :=
        ih (start + span) index (by simpa using bound)
      refine ⟨lo, hi, ?_, ?_, by omega, order, ?_, ?_⟩
      · simpa [utf8OffsetWords, spanEq] using atLo
      · simpa [utf8OffsetWords, spanEq] using atHi
      · simp only [List.flatMap_cons, List.length_append]
        change hi ≤ start + (span + _)
        omega
      · have split : lo - start = (utf8Part slot).length + (lo - (start + span)) := by
          change lo - start = span + _
          omega
        simp only [List.flatMap_cons, List.getElem_cons_succ]
        rw [split, ← List.drop_drop, List.drop_append_length]
        exact atBytes

private theorem readOffset {start : Nat} {values : List (Option String)} {index result : Nat}
    (get : (utf8OffsetWords start values)[index]? = some result) (small : result < 2^31) :
    Body.offsetAt (emitWords 4 (utf8OffsetWords start values)) index = some result := by
  obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp get
  rw [Body.offsetAt, readLE_emitWords _ _ _ bound, eq, Nat.mod_eq_of_lt (by omega)]
  simp [small]

private theorem cellsOfIndices (buffers : Body.ColumnBuffers) (indices : List Nat) (values : Column)
    (sameLength : indices.length = values.length)
    (valid : ∀ index, (bound : index < indices.length) →
      Body.CellWire buffers indices[index] (values[index]'(sameLength ▸ bound))) :
    Body.CellsWire buffers indices values := by
  induction indices generalizing values with
  | nil =>
    cases values with
    | nil => trivial
    | cons _ _ =>
      simp only [List.length_nil, List.length_cons] at sameLength
      omega
  | cons index indices ih =>
    cases values with
    | nil => simp at sameLength
    | cons value values =>
      exact ⟨valid 0 (by simp), ih values (by simpa using sameLength) (fun i h =>
        valid (i + 1) (by simp; omega))⟩

private theorem observedCells {α : Type} (buffers : Body.ColumnBuffers)
    (values : List (Option α)) (lift : α → Value)
    (valid : ∀ index, (bound : index < values.length) →
      Body.CellWire buffers index (values[index].map lift)) :
    Body.CellsWire buffers (List.range values.length) (values.map (Option.map lift)) := by
  apply cellsOfIndices buffers _ _ (by simp)
  intro index bound
  simpa using valid index (by simpa using bound)

private theorem bitmapExtent {α : Type} (values : List (Option α)) :
    Body.BitmapExtent (emitBitmap values) values.length := by
  unfold Body.BitmapExtent
  rw [emitBitmap_length]
  right
  omega

private theorem nullCount_map {α β : Type} (values : List (Option α)) (lift : α → β) :
    (values.map (Option.map lift)).countP Option.isNone = values.countP Option.isNone := by
  rw [List.countP_map]
  congr
  funext value
  cases value <;> rfl

private theorem int32Wire (values : List (Option Int32)) :
    Body.ColumnWire (NamedColumn.node ⟨"", true, .int32 values⟩)
      (ColumnValues.encode (.int32 values)) (ColumnValues.observe (.int32 values)) := by
  refine ⟨bitmapExtent values, ?_, ?_, nullCount_map values Value.int32⟩
  · simp [ColumnValues.encode, Body.PayloadExtent, NamedColumn.node, ColumnValues.length, emitWords_length]
  · apply observedCells
    intro index bound
    let words := values.map fun value => (value.getD 0).toUInt32.toNat
    let word := (values[index].getD 0).toUInt32.toNat
    refine ⟨values[index].isSome, emitBitmap_valid values index bound, word, ?_, ?_⟩
    · have fits : word < 256^4 := (values[index].getD 0).toUInt32.toNat_lt
      rw [readLE_emitWords 4 words index (by simpa [words] using bound)]
      simp [words, word, Nat.mod_eq_of_lt fits]
    · cases atSlot : values[index] with
      | none => rfl
      | some value =>
        simp [word, atSlot, ← UInt32.toInt32_ofNat']

private theorem utf8Wire (values : List (Option String)) (small : utf8ByteCount values < 2^31) :
    Body.ColumnWire (NamedColumn.node ⟨"", true, .utf8 values⟩)
      (ColumnValues.encode (.utf8 values)) (ColumnValues.observe (.utf8 values)) := by
  let encoded := emitWords 1 ((values.flatMap utf8Part).map UInt8.toNat)
  have encodedLen : encoded.len = (values.flatMap utf8Part).length := by
    simp [encoded, emitWords_length]
  have first : Body.offsetAt (emitWords 4 (utf8OffsetWords 0 values)) 0 = some 0 :=
    readOffset (by cases values <;> simp [utf8OffsetWords]) (by decide)
  refine ⟨bitmapExtent values, ?_, ?_, nullCount_map values Value.utf8⟩
  · simp [ColumnValues.encode, Body.PayloadExtent, NamedColumn.node, ColumnValues.length,
      emitWords_length, offsets_length, first]
  · apply observedCells
    intro index bound
    obtain ⟨lo, hi, atLo, atHi, _, increasing, upper, slice⟩ := offsets_window 0 values index bound
    have hiSmall : hi < 2^31 := by
      rw [← utf8ByteCount_length] at small
      omega
    have hiFits : hi ≤ encoded.len := by rw [encodedLen]; omega
    refine ⟨values[index].isSome, emitBitmap_valid values index bound, lo, hi,
      readOffset atLo (by omega), readOffset atHi hiSmall, increasing, hiFits, ?_⟩
    cases value : values[index] with
    | none => rfl
    | some text =>
      have bounds : lo + (hi - lo) ≤ encoded.len := by omega
      have bytes : (encoded.slice lo (hi - lo)).toByteArray = text.toByteArray := by
        apply ByteArray.ext
        apply Array.toList_inj.mp
        change (encoded.slice lo (hi - lo)).toList = text.toByteArray.data.toList
        rw [KBytes.toList_slice _ _ _ (emitWords_wf _ _) bounds, emitBytes_bytes]
        simpa [utf8Part, value] using slice
      change ∃ s, String.fromUTF8? (encoded.slice lo (hi - lo)).toByteArray = some s ∧
        some (Value.utf8 text) = some (Value.utf8 s)
      exact ⟨text, by simp [bytes, String.fromUTF8?, text.isValidUTF8], rfl⟩

/-- Each independently emitted physical column satisfies the reader's slot,
extent, and null-count relation. -/
theorem emitColumn_wire (column : NamedColumn)
    (small : ∀ values, column.values = .utf8 values → utf8ByteCount values < 2^31) :
    Body.ColumnWire column.node column.values.encode column.values.observe := by
  rcases column with ⟨name, nullable, values⟩
  cases values with
  | int32 values => exact int32Wire values
  | utf8 values => exact utf8Wire values (small values rfl)

end Silmaril.Proofs.Formats.Arrow.Writer
