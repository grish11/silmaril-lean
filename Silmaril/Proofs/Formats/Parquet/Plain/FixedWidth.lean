module

public import Silmaril.Formats.Parquet.Plain.Defs
import Silmaril.Prelude.Bytes.Digits.Thms
import Init.Data.SInt.Lemmas
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.Plain

open Silmaril.Formats Silmaril.Formats.Parquet.Plain

private theorem decodeWords_flatten {α : Type} (readWord : List UInt8 → α) {width : Nat}
    {words : List (List UInt8)} (sized : ∀ word ∈ words, word.length = width) (acc : List α) :
    decodeWords width readWord words.length words.flatten acc = acc.reverse ++ words.map readWord := by
  induction words generalizing acc with
  | nil => simp [decodeWords]
  | cons word rest ih =>
    have hw := sized word (by simp)
    have hrest : ∀ w ∈ rest, List.length w = width := fun w h => sized w (by simp [h])
    simp only [List.length_cons, List.flatten_cons, decodeWords, List.take_left' hw,
      List.drop_left' hw]
    rw [ih hrest]
    simp [List.append_assoc]

private theorem decodeWords_split {α : Type} (readWord : List UInt8 → α)
    {width count : Nat} {input : List UInt8} (sized : input.length = count * width)
    (acc : List α) :
    ∃ words : List (List UInt8),
      input = words.flatten ∧ words.length = count ∧
      (∀ word ∈ words, word.length = width) ∧
      decodeWords width readWord count input acc = acc.reverse ++ words.map readWord := by
  induction count generalizing input acc with
  | zero =>
    have empty : input = [] := List.length_eq_zero_iff.mp (by simpa using sized)
    subst input
    exact ⟨[], by simp [decodeWords]⟩
  | succ count ih =>
    rw [Nat.succ_mul] at sized
    have htail : (input.drop width).length = count * width := by
      rw [List.length_drop, sized]
      omega
    obtain ⟨rest, hrest, hcount, hwidth, hdecode⟩ :=
      ih htail (readWord (input.take width) :: acc)
    refine ⟨input.take width :: rest, ?_, by simp [hcount], ?_, ?_⟩
    · simp only [List.flatten_cons, ← hrest, List.take_append_drop]
    · have hhead : (input.take width).length = width := by
        rw [List.length_take, Nat.min_eq_left (by omega)]
      simpa [List.forall_mem_cons, hhead] using hwidth
    · simp [decodeWords, hdecode, List.append_assoc]

private theorem flatten_length {width : Nat} {words : List (List UInt8)}
    (sized : ∀ word ∈ words, word.length = width) :
    words.flatten.length = words.length * width := by
  induction words with
  | nil => simp
  | cons word rest ih =>
    have hw := sized word (by simp)
    have hrest : ∀ w ∈ rest, List.length w = width := fun w h => sized w (by simp [h])
    simp [ih hrest, hw, Nat.succ_mul, Nat.add_comm]

public theorem decodeFixedWidth_ok_iff {α : Type} {width count : Nat}
    {readWord : List UInt8 → α} {source : Bytes} {values : List α} :
    decodeFixedWidth width count readWord source = .ok values ↔
      0 < width ∧ ∃ words : List (List UInt8),
        source.toList = words.flatten ∧ words.length = count ∧
        (∀ word ∈ words, word.length = width) ∧ values = words.map readWord := by
  constructor
  · intro h
    unfold decodeFixedWidth at h
    split at h
    · contradiction
    · rename_i positive
      split at h
      · contradiction
      · rename_i lower
        split at h
        · contradiction
        · rename_i upper
          have sized : source.toList.length = count * width := by
            rw [Bytes.length_toList]
            omega
          obtain ⟨words, octets, hcount, hwidth, hdecode⟩ := decodeWords_split readWord sized []
          rw [hdecode] at h
          exact ⟨by omega, words, octets, hcount, hwidth, (Except.ok.inj h).symm⟩
  · rintro ⟨positive, words, octets, rfl, sized, rfl⟩
    have hlen : source.length = words.length * width := by
      rw [← Bytes.length_toList, octets, flatten_length sized]
    simp [decodeFixedWidth, Nat.ne_of_gt positive, hlen, octets, decodeWords_flatten readWord sized]

private theorem decodeFixedWidth_encodeWords {α : Type} {width : Nat}
    {readWord : List UInt8 → α} {writeWord : α → List UInt8} {values : List α}
    (positive : 0 < width) (sized : ∀ value ∈ values, (writeWord value).length = width)
    (inverse : ∀ value ∈ values, readWord (writeWord value) = value) :
    decodeFixedWidth width values.length readWord (encodeWords writeWord values) = .ok values := by
  apply decodeFixedWidth_ok_iff.mpr
  refine ⟨positive, values.map writeWord, ?_, by simp, ?_, ?_⟩
  · simp [encodeWords, List.flatMap]
  · simpa using sized
  · rw [List.map_map]
    exact (List.map_congr_left (by simpa [Function.comp_def] using inverse) :
      values.map (readWord ∘ writeWord) = values.map id).trans (List.map_id values) |>.symm

private theorem readUInt32Word_writeUInt32Word (word : UInt32) :
    readUInt32Word (writeUInt32Word word) = word := by
  rw [readUInt32Word, writeUInt32Word, KBytes.leVal_unpack]
  have bound := word.toNat_lt
  rw [Nat.mod_eq_of_lt (by simpa using bound)]
  simp

private theorem readUInt64Word_writeUInt64Word (word : UInt64) :
    readUInt64Word (writeUInt64Word word) = word := by
  rw [readUInt64Word, writeUInt64Word, KBytes.leVal_unpack]
  have bound := word.toNat_lt
  rw [Nat.mod_eq_of_lt (by simpa using bound)]
  simp

public theorem decodeInt32_encodeInt32 (values : List Int32) :
    decodeInt32 values.length (encodeInt32 values) = .ok values := by
  apply decodeFixedWidth_encodeWords (width := 4) (by decide)
  · intro value _
    exact KBytes.length_unpack 4 value.toUInt32.toNat
  · intro value _
    simp [readUInt32Word_writeUInt32Word]

public theorem decodeInt64_encodeInt64 (values : List Int64) :
    decodeInt64 values.length (encodeInt64 values) = .ok values := by
  apply decodeFixedWidth_encodeWords (width := 8) (by decide)
  · intro value _
    exact KBytes.length_unpack 8 value.toUInt64.toNat
  · intro value _
    simp [readUInt64Word_writeUInt64Word]

public theorem decodeFloatBits_encodeFloatBits (values : List UInt32) :
    decodeFloatBits values.length (encodeFloatBits values) = .ok values := by
  exact decodeFixedWidth_encodeWords (by decide)
    (fun value _ => KBytes.length_unpack 4 value.toNat)
    (fun value _ => readUInt32Word_writeUInt32Word value)

public theorem decodeDoubleBits_encodeDoubleBits (values : List UInt64) :
    decodeDoubleBits values.length (encodeDoubleBits values) = .ok values := by
  exact decodeFixedWidth_encodeWords (by decide)
    (fun value _ => KBytes.length_unpack 8 value.toNat)
    (fun value _ => readUInt64Word_writeUInt64Word value)

public theorem decodeFixedLenBytes_encodeFixedLenBytes {width : Nat} {values : List Bytes}
    {source : Bytes} (encoded : encodeFixedLenBytes width values = .ok source) :
    decodeFixedLenBytes width values.length source = .ok values := by
  unfold encodeFixedLenBytes at encoded
  split at encoded
  · rename_i hw
    split at encoded
    · rename_i hs
      cases encoded
      rw [decodeFixedLenBytes, ite_eq_left hw.2]
      apply decodeFixedWidth_encodeWords hw.1
      · intro value hm
        have hsize := List.all_eq_true.mp hs value hm
        simpa using hsize
      · exact fun value _ => Bytes.ofList_toList value
    · contradiction
  · contradiction

end Silmaril.Proofs.Formats.Parquet.Plain
