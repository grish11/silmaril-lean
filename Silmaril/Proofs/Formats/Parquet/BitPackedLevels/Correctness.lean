module

public import Silmaril.Formats.Parquet.BitPackedLevels.Defs
import Init.Data.Nat.Bitwise.Lemmas
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.BitPackedLevels

open Silmaril.Formats Silmaril.Formats.Parquet.BitPackedLevels

private theorem readCode_eq (packed : Bytes) (width start acc : Nat) :
    Internal.readCode packed.data width start acc = acc * 2 ^ width + wireCode packed start width := by
  induction width generalizing start acc with
  | zero => simp [Internal.readCode, wireCode]
  | succ width ih =>
    simp only [Internal.readCode, wireCode, Nat.shiftRight_eq_div_pow]
    rw [ih]
    simp only [wireBit, Nat.pow_succ', Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
    ac_rfl

private theorem codes_length (packed : Bytes) (width count : Nat) :
    (Internal.codes packed width count).length = count := by simp [Internal.codes]

private theorem codes_at (packed : Bytes) (width count i : Nat)
    (hi : i < (Internal.codes packed width count).length) :
    (Internal.codes packed width count)[i] = wireCode packed (i * width) width := by
  simp only [Internal.codes, List.getElem_ofFn, readCode_eq, Nat.zero_mul, Nat.zero_add]

private theorem prefix_toList (source : Bytes) (size : Nat) :
    (Internal.takeBytes source size).toList = source.toList.take size := by
  simp [Internal.takeBytes, Bytes.toList]

private theorem suffix_toList (source : Bytes) (size : Nat) :
    (Internal.dropBytes source size).toList = source.toList.drop size := by
  simp [Internal.dropBytes, Bytes.toList, Bytes.length, ← ByteArray.size_data]
  rw [← Array.length_toList, ← List.length_drop, List.take_length]

private theorem unpack_source (source : Bytes) (size : Nat) :
    source = (Internal.takeBytes source size).append (Internal.dropBytes source size) := by
  apply Bytes.ext
  rw [Bytes.toList_append, prefix_toList, suffix_toList, List.take_append_drop]

private theorem prefix_size {source : Bytes} {size : Nat} (fits : size ≤ source.length) :
    (Internal.takeBytes source size).length = size := by
  change size ≤ source.data.size at fits
  simp [Internal.takeBytes, Bytes.length, Nat.min_eq_left fits]

public theorem readPrefix_ok_iff {maxLevel count : Nat} {limits : Limits}
    {source rest : Bytes} {levels : List Nat} :
    readPrefix maxLevel count limits source = .ok (levels, rest) ↔
      maxLevel < signedLimit ∧ count < signedLimit ∧ count ≤ limits.levels ∧
      byteCount maxLevel count ≤ limits.bytes ∧
      ∃ packed, source = packed.append rest ∧ Wire maxLevel count packed levels := by
  by_cases maxFits : maxLevel < signedLimit
  · by_cases countFits : count < signedLimit ∧ count ≤ limits.levels
    · have countOK : ¬(signedLimit ≤ count ∨ limits.levels < count) := by omega
      by_cases cap : byteCount maxLevel count ≤ limits.bytes
      · by_cases fits : byteCount maxLevel count ≤ source.length
        · simp only [readPrefix, ite_eq_right (Nat.not_le.mpr maxFits), ite_eq_right countOK,
            ite_eq_right (Nat.not_lt.mpr cap), ite_eq_right (Nat.not_lt.mpr fits)]
          constructor
          · intro read
            split at read
            · rename_i bounded
              cases read
              refine ⟨maxFits, countFits.1, countFits.2, cap, _, unpack_source _ _,
                prefix_size fits, codes_length _ _ _, codes_at _ _ _, ?_⟩
              intro level member
              simpa using List.all_eq_true.mp bounded level member
            · contradiction
          · rintro ⟨_, _, _, _, packed, whole, wire⟩
            have first : Internal.takeBytes source (byteCount maxLevel count) = packed := by
              apply Bytes.ext
              rw [prefix_toList, whole, Bytes.toList_append, ← wire.extent,
                ← Bytes.length_toList packed, List.take_append_length]
            have next : Internal.dropBytes source (byteCount maxLevel count) = rest := by
              apply Bytes.ext
              rw [suffix_toList, whole, Bytes.toList_append, ← wire.extent,
                ← Bytes.length_toList packed, List.drop_append_length]
            have ordered : Internal.codes packed (bitWidth maxLevel) count = levels := by
              apply List.ext_getElem
              · rw [codes_length, wire.countFits]
              · intro i left right
                rw [codes_at _ _ _ i left, wire.order i right]
            have bounded : levels.all (fun level => level ≤ maxLevel) = true :=
              List.all_eq_true.mpr (fun level member => by simpa using wire.bounds level member)
            simp only [first, next, ordered, bounded, ite_true]
        · constructor
          · simp [readPrefix, Nat.not_le.mpr maxFits, countOK, Nat.not_lt.mpr cap, Nat.lt_of_not_ge fits]
          · rintro ⟨_, _, _, _, packed, whole, wire⟩
            have extent : byteCount maxLevel count ≤ source.length := by
              rw [whole, Bytes.length_append, wire.extent]
              exact Nat.le_add_right _ _
            exact (fits extent).elim
      · simp [readPrefix, Nat.not_le.mpr maxFits, countOK, Nat.lt_of_not_ge cap, cap]
    · have countBad : signedLimit ≤ count ∨ limits.levels < count := by omega
      constructor
      · simp [readPrefix, Nat.not_le.mpr maxFits, countBad]
      · rintro ⟨_, below, within, _⟩
        exact (countFits ⟨below, within⟩).elim
  · simp [readPrefix, Nat.le_of_not_gt maxFits, maxFits]

private theorem wireCode_lt (packed : Bytes) (start width : Nat) :
    wireCode packed start width < 2 ^ width := by
  induction width generalizing start with
  | zero => simp [wireCode]
  | succ width ih =>
    have tail := ih (start + 1)
    have digit : wireBit packed start < 2 := Nat.mod_lt _ (by decide)
    have split : wireBit packed start = 0 ∨ wireBit packed start = 1 := by omega
    rcases split with h | h <;>
      simp only [wireCode, h, Nat.pow_succ', Nat.zero_mul, Nat.one_mul, Nat.zero_add] <;> omega

/-- The j-th bit of a field, counted from its high end, is the corresponding
physical bit of the packed bytes. -/
public theorem wireCode_testBit (packed : Bytes) (start width j : Nat) (within : j < width) :
    (wireCode packed start width).testBit (width - 1 - j) =
      decide (wireBit packed (start + j) = 1) := by
  induction width generalizing start j with
  | zero => omega
  | succ width ih =>
    simp only [wireCode, Nat.succ_sub_one, Nat.mul_comm (wireBit packed start)]
    rw [Nat.testBit_two_pow_mul_add _ (wireCode_lt packed (start + 1) width)]
    cases j with
    | zero =>
      simp [Nat.testBit_eq_decide_div_mod_eq, wireBit]
      rfl
    | succ j =>
      have shift : width - (j + 1) < width := by omega
      simp only [ite_eq_left shift]
      have index : width - (j + 1) = width - 1 - j := by omega
      rw [index, ih (start + 1) j (by omega : j < width)]
      simp [Nat.add_assoc, Nat.add_comm 1 j]

public theorem position_in_extent {maxLevel count : Nat} {packed : Bytes} {levels : List Nat}
    (wire : Wire maxLevel count packed levels) {i j : Nat} (hi : i < count)
    (hj : j < bitWidth maxLevel) : (i * bitWidth maxLevel + j) / 8 < packed.length := by
  have next := Nat.mul_le_mul_right (bitWidth maxLevel) (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at next
  rw [wire.extent, byteCount]
  omega

public theorem readPrefix_zero {count : Nat} {limits : Limits} {source : Bytes}
    (countFits : count < signedLimit) (cap : count ≤ limits.levels) :
    readPrefix 0 count limits source = .ok (List.replicate count 0, source) := by
  apply readPrefix_ok_iff.mpr
  refine ⟨by decide, countFits, cap, by simp [byteCount, bitWidth], .empty,
    (Bytes.empty_append source).symm, ?_⟩
  exact ⟨by simp [byteCount, bitWidth], by simp, by simp [bitWidth, wireCode],
    by simp⟩

public theorem readExact_ok_iff {maxLevel count : Nat} {limits : Limits}
    {source : Bytes} {levels : List Nat} :
    readExact maxLevel count limits source = .ok levels ↔
      readPrefix maxLevel count limits source = .ok (levels, .empty) := by
  cases read : readPrefix maxLevel count limits source with
  | error error => simp [readExact, read, Bind.bind, Except.bind]
  | ok result =>
    obtain ⟨values, rest⟩ := result
    by_cases empty : rest.length = 0
    · have restEmpty : rest = .empty := by
        apply Bytes.ext
        simpa using List.eq_nil_of_length_eq_zero (by simpa using empty : rest.toList.length = 0)
      subst rest
      simp [readExact, read, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · have restNonempty : rest ≠ .empty := by
        intro h
        exact empty (by simp [h])
      simp [readExact, read, Bind.bind, Except.bind, throw, empty, restNonempty]

end Silmaril.Proofs.Formats.Parquet.BitPackedLevels
