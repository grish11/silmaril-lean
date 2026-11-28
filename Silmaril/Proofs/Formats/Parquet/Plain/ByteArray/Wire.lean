module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Defs
import Silmaril.Prelude.Bytes.Digits.Thms
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.Plain.ByteArray

open Silmaril.Formats Silmaril.Formats.Parquet.Plain.ByteArray

private theorem valueWire_length (value : Bytes) :
    (valueWire value).length = 4 + value.length := by
  simp [valueWire, KBytes.length_unpack]

@[simp] private theorem wire_cons (value : Bytes) (values : List Bytes) :
    wire (value :: values) = valueWire value ++ wire values := rfl

private theorem wire_length (values : List Bytes) : (wire values).length = encodedSize values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp [wire_cons, valueWire_length, ih, encodedSize]

private theorem readOne_ok_iff {valueLimit remaining : Nat} {source suffix : List UInt8}
    {value : Bytes} (extent : source.length = remaining) :
    Internal.readOne valueLimit remaining source = .ok (value, suffix) ↔
      source = valueWire value ++ suffix ∧ value.length < lengthLimit ∧ value.length ≤ valueLimit := by
  subst remaining
  constructor
  · intro h
    simp only [Internal.readOne] at h
    split at h
    · contradiction
    · rename_i header
      split at h
      · contradiction
      · rename_i repr
        split at h
        · contradiction
        · rename_i cap
          split at h
          · contradiction
          · rename_i body
            cases h
            have wordLength : (source.take 4).length = 4 := by
              simp only [List.length_take]
              omega
            have word : KBytes.unpack 4 (KBytes.leVal (source.take 4)) = source.take 4 := by
              simpa only [wordLength] using KBytes.unpack_leVal (source.take 4)
            have valueLength : (Bytes.ofList
                ((source.drop 4).take (KBytes.leVal (source.take 4)))).length =
                KBytes.leVal (source.take 4) := by
              simp only [Bytes.length_ofList, List.length_take, List.length_drop]
              omega
            refine ⟨?_, by rw [valueLength]; omega, by rw [valueLength]; omega⟩
            rw [valueWire, valueLength, word, Bytes.toList_ofList, List.append_assoc,
              List.take_append_drop, List.take_append_drop]
  · rintro ⟨rfl, repr, cap⟩
    let word := KBytes.unpack 4 value.length
    have wordLength : word.length = 4 := KBytes.length_unpack 4 value.length
    have wordValue : KBytes.leVal word = value.length := by
      rw [show word = KBytes.unpack 4 value.length from rfl, KBytes.leVal_unpack]
      exact Nat.mod_eq_of_lt (by unfold lengthLimit at repr; omega)
    change Internal.readOne valueLimit (word ++ (value.toList ++ suffix)).length
      (word ++ (value.toList ++ suffix)) = .ok (value, suffix)
    simp [Internal.readOne, wordLength, wordValue, List.take_left' wordLength,
      List.drop_left' wordLength, Nat.not_le_of_lt repr, Nat.not_lt_of_ge cap,
      List.take_left' (Bytes.length_toList value), List.drop_left' (Bytes.length_toList value)]
    split
    · omega
    · split
      · omega
      · rfl

private theorem decodeLoop_sound {valueLimit count remaining : Nat} {source : List UInt8}
    {reversed output : List Bytes} (extent : source.length = remaining)
    (h : Internal.decodeLoop valueLimit count remaining source reversed = .ok output) :
    ∃ values, source = wire values ∧ values.length = count ∧
      (∀ value ∈ values, value.length < lengthLimit ∧ value.length ≤ valueLimit) ∧
      output = reversed.reverse ++ values := by
  induction count generalizing source remaining reversed with
  | zero =>
    unfold Internal.decodeLoop at h
    split at h
    · rename_i empty
      have sourceEmpty : source = [] := List.length_eq_zero_iff.mp (extent.trans empty)
      cases h
      exact ⟨[], sourceEmpty, rfl, by simp, by simp⟩
    · contradiction
  | succ count ih =>
    unfold Internal.decodeLoop at h
    cases read : Internal.readOne valueLimit remaining source with
    | error error => rw [read] at h; contradiction
    | ok pair =>
      obtain ⟨value, suffix⟩ := pair
      rw [read] at h
      obtain ⟨bytes, repr, cap⟩ := (readOne_ok_iff extent).mp read
      have tailExtent : suffix.length = remaining - (4 + value.length) := by
        rw [bytes, List.length_append, valueWire_length] at extent
        omega
      obtain ⟨values, tail, count, fits, outputEq⟩ := ih tailExtent h
      refine ⟨value :: values, by simp [bytes, tail], by simp [count], ?_, ?_⟩
      · intro item member
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨repr, cap⟩
        · exact fits item later
      · simpa [List.reverse_cons, List.append_assoc] using outputEq

private theorem decodeLoop_wire {cap : Nat} {values : List Bytes}
    (fits : ∀ value ∈ values, value.length < lengthLimit ∧ value.length ≤ cap)
    (reversed : List Bytes) :
    Internal.decodeLoop cap values.length (wire values).length (wire values) reversed =
      .ok (reversed.reverse ++ values) := by
  induction values generalizing reversed with
  | nil => simp [Internal.decodeLoop, wire]
  | cons value values ih =>
    have ⟨repr, limit⟩ := fits value (by simp)
    have step : Internal.readOne cap (wire (value :: values)).length (wire (value :: values)) =
        .ok (value, wire values) := (readOne_ok_iff rfl).mpr ⟨wire_cons .., repr, limit⟩
    have extent : (wire (value :: values)).length - (4 + value.length) = (wire values).length := by
      simp [valueWire_length]
    have tail := ih (fun item member => fits item (List.mem_cons_of_mem value member))
      (value :: reversed)
    rw [List.length_cons, Internal.decodeLoop, step]
    change Internal.decodeLoop cap values.length _ _ _ = _
    rw [extent]
    simpa [List.reverse_cons, List.append_assoc] using tail

public theorem decode_ok_iff {limits : Limits} {count : Nat} {source : Bytes} {values : List Bytes} :
    decode limits count source = .ok values ↔
      source.length ≤ limits.totalBytes ∧ source.toList = wire values ∧ values.length = count ∧
      ∀ value ∈ values, value.length < lengthLimit ∧ value.length ≤ limits.valueBytes := by
  constructor
  · intro h
    unfold decode at h
    split at h
    · contradiction
    · rename_i cap
      obtain ⟨values, bytes, count, fits, rfl⟩ := decodeLoop_sound (Bytes.length_toList source) h
      exact ⟨by omega, bytes, count, fits⟩
  · rintro ⟨cap, bytes, rfl, fits⟩
    rw [decode, ite_eq_right (Nat.not_lt_of_ge cap), ← Bytes.length_toList, bytes]
    simpa using decodeLoop_wire fits []

public theorem encode_ok_iff {limits : Limits} {values : List Bytes} {source : Bytes} :
    encode limits values = .ok source ↔
      encodedSize values ≤ limits.totalBytes ∧ source.toList = wire values ∧
      ∀ value ∈ values, value.length < lengthLimit ∧ value.length ≤ limits.valueBytes := by
  have repr : (values.any fun value => lengthLimit ≤ value.length) = false ↔
      ∀ value ∈ values, value.length < lengthLimit := by
    simp [List.any_eq_false]
  have cap : (values.any fun value => limits.valueBytes < value.length) = false ↔
      ∀ value ∈ values, value.length ≤ limits.valueBytes := by
    simp [List.any_eq_false]
  constructor
  · intro h
    unfold encode at h
    split at h
    · contradiction
    · rename_i hrepr
      split at h
      · contradiction
      · rename_i hcap
        split at h
        · contradiction
        · rename_i total
          cases h
          exact ⟨by omega, Bytes.toList_ofList _, fun value member =>
            ⟨repr.mp (by simpa using hrepr) value member,
              cap.mp (by simpa using hcap) value member⟩⟩
  · rintro ⟨total, bytes, fits⟩
    have hrepr := repr.mpr fun value member => (fits value member).1
    have hcap := cap.mpr fun value member => (fits value member).2
    simp [encode, hrepr, hcap, Nat.not_lt_of_ge total, ← bytes]

public theorem decode_size {limits : Limits} {count : Nat} {source : Bytes} {values : List Bytes}
    (h : decode limits count source = .ok values) : source.length = encodedSize values := by
  obtain ⟨_, bytes, _, _⟩ := decode_ok_iff.mp h
  rw [← Bytes.length_toList, bytes, wire_length]

public theorem decode_encode {limits : Limits} {values : List Bytes} {source : Bytes}
    (h : encode limits values = .ok source) : decode limits values.length source = .ok values := by
  obtain ⟨total, bytes, fits⟩ := encode_ok_iff.mp h
  refine decode_ok_iff.mpr ⟨?_, bytes, rfl, fits⟩
  rw [← Bytes.length_toList, bytes, wire_length]
  exact total

public theorem encode_decode {limits : Limits} {count : Nat} {source : Bytes} {values : List Bytes}
    (h : decode limits count source = .ok values) : encode limits values = .ok source := by
  obtain ⟨total, bytes, _, fits⟩ := decode_ok_iff.mp h
  exact encode_ok_iff.mpr ⟨decode_size h ▸ total, bytes, fits⟩

end Silmaril.Proofs.Formats.Parquet.Plain.ByteArray
