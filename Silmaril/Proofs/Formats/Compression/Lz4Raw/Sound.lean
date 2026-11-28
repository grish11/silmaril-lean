module

public import Silmaril.Formats.Compression.Lz4Raw.Defs

public section

namespace Silmaril.Proofs.Formats.Compression.Lz4Raw

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Lz4Raw
open Silmaril.Formats.Compression.Lz4Raw.Internal

private theorem hasLength_sound {n : Nat} {bytes : List UInt8}
    (h : hasLength n bytes = true) : bytes.length = n := by
  induction n generalizing bytes with
  | zero => cases bytes <;> simp_all [hasLength]
  | succ n ih => cases bytes <;> simp_all [hasLength]

private theorem readExtension_sound {room acc total : Nat} {input rest : List UInt8}
    (h : readExtension room acc input = .ok (total, rest)) :
    ∃ ext extra, Extension ext extra ∧ input = ext ++ rest ∧ total = acc + extra ∧
      extra ≤ room := by
  induction input generalizing room acc with
  | nil => cases h
  | cons byte input ih =>
    simp only [readExtension] at h
    split at h
    · cases h
    · rename_i fits
      split at h
      · rename_i extend
        have eq : byte = 255 := UInt8.toNat_inj.mp extend
        obtain ⟨ext, extra, code, shape, value, bound⟩ := ih h
        refine ⟨255 :: ext, 255 + extra, .next code, ?_, ?_, ?_⟩
        · simp [eq, shape]
        · omega
        · omega
      · rename_i stop
        have byteBound := byte.toNat_lt_size
        change byte.toNat < 256 at byteBound
        cases h
        exact ⟨[byte], byte.toNat, .stop byte (by omega), rfl, rfl, by omega⟩

private theorem readLength_sound {nibble room length : Nat} {input rest : List UInt8}
    (nibbleBound : nibble < 16) (h : readLength nibble room input = .ok (length, rest)) :
    ∃ ext, LengthField nibble ext length ∧ input = ext ++ rest ∧ length ≤ room := by
  unfold readLength at h
  split at h
  · cases h
  · rename_i fits
    split at h
    · rename_i extend
      obtain ⟨ext, extra, code, shape, value, bound⟩ := readExtension_sound h
      subst nibble
      subst length
      exact ⟨ext, .long code, shape, by omega⟩
    · rename_i short
      cases h
      exact ⟨[], .short _ (by omega), rfl, by omega⟩

private theorem takeLiterals_sound {count : Nat} {input literals rest : List UInt8}
    (h : takeLiterals count input = .ok (literals, rest)) :
    literals.length = count ∧ input = literals ++ rest := by
  simp only [takeLiterals, List.splitAt_eq] at h
  split at h
  · rename_i length
    cases h
    exact ⟨length, (List.take_append_drop _ _).symm⟩
  · cases h

private theorem readBlock_sound {fuel room : Nat} {input : List UInt8}
    {rev : List MatchSequence} {result : Block} (h : readBlock fuel room input rev = .ok result) :
    ∃ block, Wire input block ∧ result = prependReversed rev block ∧ block.outputSize = room := by
  induction fuel generalizing room input rev with
  | zero => cases h
  | succ fuel ih =>
    cases input with
    | nil => cases h
    | cons token bytes =>
      have tokenBound := token.toNat_lt_size
      change token.toNat < 256 at tokenBound
      cases head : readLength (token.toNat / 16) room bytes with
      | error error => simp [readBlock, head, bind, Except.bind] at h
      | ok fields =>
        obtain ⟨litLen, afterLength⟩ := fields
        obtain ⟨litExt, litField, splitLength, litFits⟩ := readLength_sound (by omega) head
        cases body : takeLiterals litLen afterLength with
        | error error => simp [readBlock, head, body, bind, Except.bind] at h
        | ok parts =>
          obtain ⟨literals, rest⟩ := parts
          obtain ⟨litSize, splitLiterals⟩ := takeLiterals_sound body
          simp only [readBlock, head, body, bind, Except.bind] at h
          cases rest with
          | nil =>
            change (if litLen ≠ room then Except.error Error.outputSizeMismatch
              else if litLen = 0 ∧ token.toNat ≠ 0 then Except.error Error.invalidTail
              else Except.ok (prependReversed rev (.final literals))) = .ok result at h
            split at h
            · cases h
            · rename_i exactSize
              split at h
              · cases h
              · rename_i permitted
                cases h
                have source : bytes = litExt ++ literals := by simp [splitLength, splitLiterals]
                refine ⟨.final literals, ?_, rfl, ?_⟩
                · rw [source]
                  exact .final (by rwa [litSize]) (by omega)
                · simp only [Block.outputSize, litSize]
                  omega
          | cons lo rest =>
            cases rest with
            | nil => cases h
            | cons hi tail =>
              change (if room < litLen + 4 then .error .outputSizeMismatch else do
                let (matchCode, next) ← readLength (token.toNat % 16) (room - litLen - 4) tail
                let sequence : MatchSequence := ⟨literals, lo.toNat + 256 * hi.toNat, 4 + matchCode⟩
                readBlock fuel (room - litLen - sequence.length) next (sequence :: rev)) =
                  .ok result at h
              split at h
              · cases h
              · rename_i roomEnough
                cases copied : readLength (token.toNat % 16) (room - litLen - 4) tail with
                | error error => simp [copied, bind, Except.bind] at h
                | ok fields =>
                  obtain ⟨matchCode, next⟩ := fields
                  obtain ⟨matchExt, matchField, splitMatch, matchFits⟩ :=
                    readLength_sound (by omega) copied
                  simp only [copied, bind, Except.bind] at h
                  obtain ⟨block, shape, resultEq, outputEq⟩ := ih h
                  have source : bytes = litExt ++ literals ++ (lo :: hi :: (matchExt ++ next)) := by
                    simp only [splitLength, splitLiterals, splitMatch, List.append_assoc]
                  refine ⟨.more ⟨literals, lo.toNat + 256 * hi.toNat, 4 + matchCode⟩ block,
                    ?_, resultEq, ?_⟩
                  · rw [source]
                    exact .more (by rwa [litSize]) matchField shape
                  · simp only [Block.outputSize, litSize]
                    omega

theorem parse_sound {bounds : Bounds} {input : List UInt8} {block : Block}
    (h : parse bounds input = .ok block) :
    Wire input block ∧ input.length = bounds.compressedSize ∧
      bounds.compressedSize ≤ bounds.compressedLimit ∧
      block.outputSize = bounds.expectedSize ∧ bounds.expectedSize ≤ bounds.outputLimit := by
  unfold parse at h
  split at h
  · cases h
  · rename_i compressedFits
    split at h
    · cases h
    · rename_i outputFits
      split at h
      · rename_i len
        obtain ⟨parsed, wire, eq, size⟩ := readBlock_sound h
        change block = parsed at eq
        subst block
        exact ⟨wire, hasLength_sound len, by omega, size, by omega⟩
      · cases h

private theorem copyBack_length (offset count : Nat) (history : List UInt8) :
    (Deflate.copyBack offset history count).length = history.length + count := by
  induction count generalizing history with
  | zero => rfl
  | succ count ih => simp [Deflate.copyBack, ih, Nat.add_comm, Nat.add_left_comm]

theorem denotes_length {lastMatch : Option Nat} {history out : List UInt8} {block : Block}
    (h : Denotes lastMatch history block out) :
    out.length = history.length + block.outputSize := by
  induction h with
  | final => simp [Block.outputSize]
  | more _ _ _ ih => simp only [ih, Block.outputSize, copyBack_length, List.length_append, Nat.add_assoc]

private theorem expand_sound {lastMatch : Option Nat} {history out : Array UInt8}
    {block : Block} (h : expand lastMatch history block = .ok out) :
    Denotes lastMatch history.toList block out.toList := by
  induction block generalizing history lastMatch with
  | final literals =>
    simp only [expand] at h
    split at h
    · rename_i valid
      cases h
      simpa using (Denotes.final (history := history.toList) (literals := literals) valid)
    · cases h
  | more sequence rest ih =>
    simp only [expand] at h
    split at h
    · rename_i valid
      have lists : (history.appendList sequence.literals).toList =
          history.toList ++ sequence.literals := Array.toList_appendList
      have within := valid.2
      rw [← Array.length_toList, lists, List.length_append] at within
      have meaning := ih h
      rw [Deflate.copyBackArr_toList, lists] at meaning
      exact .more valid.1 within meaning
    · cases h

theorem decode_sound {bounds : Bounds} {input out : List UInt8}
    (h : decode bounds input = .ok out) :
    ∃ block, Wire input block ∧ Denotes none [] block out ∧
      input.length = bounds.compressedSize ∧ input.length ≤ bounds.compressedLimit ∧
      out.length = bounds.expectedSize ∧ out.length ≤ bounds.outputLimit := by
  cases parsed : parse bounds input with
  | error error => simp [decode, parsed, bind, Except.bind] at h
  | ok block =>
    simp only [decode, parsed, bind, Except.bind] at h
    cases expanded : expand none #[] block with
    | error error => simp [expanded] at h
    | ok outArray =>
      simp only [expanded, pure, Except.pure] at h
      cases h
      obtain ⟨wire, inputSize, compressedFits, size, outputFits⟩ := parse_sound parsed
      have meaning := expand_sound expanded
      have len : outArray.toList.length = bounds.expectedSize := by
        simpa [size] using denotes_length meaning
      exact ⟨block, wire, meaning, inputSize, inputSize ▸ compressedFits, len, len ▸ outputFits⟩

end Silmaril.Proofs.Formats.Compression.Lz4Raw
