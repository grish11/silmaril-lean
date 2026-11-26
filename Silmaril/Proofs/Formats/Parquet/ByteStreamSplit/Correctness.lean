module

public import Silmaril.Formats.Parquet.ByteStreamSplit.Defs
import Init.Data.ByteArray.Lemmas
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.ByteStreamSplit

open Silmaril.Formats Silmaril.Formats.Parquet.ByteStreamSplit

private theorem getByte_toList (source : Bytes) {offset : Nat} (bound : offset < source.length) :
    source.toList[offset]? = some (source.data[offset]'bound) := by
  have inList : offset < source.toList.length := by simpa using bound
  rw [getElem?_def, dite_eq_left inList]
  simp only [Bytes.toList, Array.getElem_toList]
  rfl

private theorem transpose_order {width count : Nat} {source : Bytes}
    (sized : source.length = width * count) :
    LaneOrder width count source (Internal.transpose width count source sized) := by
  refine ⟨List.length_ofFn, ?_, ?_⟩
  · intro row rowBound
    simp only [Internal.transpose, List.getElem_ofFn, List.length_ofFn]
  · intro row rowBound lane laneBound
    have rowFits : row < count := by simpa [Internal.transpose] using rowBound
    have offsetFits : lane * count + row < source.length := by
      rw [sized]
      exact Internal.index_lt rowFits laneBound
    simp only [Internal.transpose, List.getElem_ofFn, List.getElem?_ofFn, dite_eq_left laneBound]
    exact (getByte_toList source offsetFits).symm

private theorem sameWords {width count : Nat} {source : Bytes} {left right : List (List UInt8)}
    (lhs : LaneOrder width count source left) (rhs : LaneOrder width count source right) :
    left = right := by
  apply List.ext_getElem (lhs.wordCount.trans rhs.wordCount.symm)
  intro row leftRow rightRow
  have leftWidth := lhs.wordWidth row leftRow
  have rightWidth := rhs.wordWidth row rightRow
  apply List.ext_getElem (leftWidth.trans rightWidth.symm)
  intro lane leftLane rightLane
  have same := (lhs.octet row leftRow lane (leftWidth ▸ leftLane)).trans
    (rhs.octet row rightRow lane (rightWidth ▸ rightLane)).symm
  rw [getElem?_pos (left[row]) lane leftLane, getElem?_pos (right[row]) lane rightLane] at same
  exact Option.some.inj same

private theorem decodeWords_transpose {limits : Limits} {width count : Nat} {source : Bytes}
    (h : Admission limits width count source) :
    decodeWords limits width count source = .ok (Internal.transpose width count source h.extent) := by
  have widthValid : ¬ (width = 0 ∨ signedSizeLimit ≤ width) := by
    have positive := h.widthPositive
    have repr := h.widthFits
    omega
  have countValid : ¬ (signedSizeLimit ≤ count ∨ limits.values < count) := by
    have repr := h.countFits
    have cap := h.valueLimit
    omega
  rw [decodeWords, ite_eq_right widthValid, ite_eq_right (Nat.not_lt_of_ge h.widthLimit),
    ite_eq_right countValid, ite_eq_right (Nat.not_lt_of_ge h.byteLimit), dite_eq_left h.extent]

public theorem decodeWords_ok_iff {limits : Limits} {width count : Nat} {source : Bytes}
    {words : List (List UInt8)} :
    decodeWords limits width count source = .ok words ↔
      Admission limits width count source ∧ LaneOrder width count source words := by
  constructor
  · intro h
    unfold decodeWords at h
    split at h
    · contradiction
    · rename_i validWidth
      split at h
      · contradiction
      · rename_i widthCap
        split at h
        · contradiction
        · rename_i countCap
          split at h
          · contradiction
          · rename_i byteCap
            split at h
            · rename_i sized
              cases h
              exact ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega, sized⟩,
                transpose_order sized⟩
            · split at h <;> contradiction
  · rintro ⟨admitted, order⟩
    rw [decodeWords_transpose admitted, sameWords (transpose_order admitted.extent) order]

public theorem decode_sound {kind : Kind} {limits : Limits} {count : Nat} {source : Bytes}
    {values : List kind.Value} (h : decode kind limits count source = .ok values) :
    ∃ words, Admission limits kind.width count source ∧ LaneOrder kind.width count source words ∧
      values = words.map kind.readWord ∧ values.length = count := by
  cases checked : decodeWords limits kind.width count source with
  | error error => simp [decode, checked, Except.map] at h
  | ok words =>
    have same : words.map kind.readWord = values := by simpa [decode, checked, Except.map] using h
    obtain ⟨admitted, order⟩ := decodeWords_ok_iff.mp checked
    exact ⟨words, admitted, order, same.symm, by simp [← same, order.wordCount]⟩

end Silmaril.Proofs.Formats.Parquet.ByteStreamSplit
