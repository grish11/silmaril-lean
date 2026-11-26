module

public import Silmaril.Formats.Parquet.FlatPage.Defs
import Silmaril.Formats.Parquet.Hybrid.Thms
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.FlatPage

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.FlatPage

public theorem splitV1Optional_ok_iff {byteLimit : Nat} {source : Bytes} {sections : Sections} :
    splitV1Optional byteLimit source = .ok sections ↔
      ∃ lengthBytes : List UInt8, lengthBytes.length = 4 ∧
        KBytes.leVal lengthBytes = sections.definitions.length ∧
        sections.definitions.length ≤ byteLimit ∧
        source.toList = lengthBytes ++ sections.definitions.toList ++ sections.scalars.toList := by
  constructor
  · intro h
    simp only [splitV1Optional] at h
    split at h
    · contradiction
    · rename_i hasLength
      split at h
      · contradiction
      · rename_i sized
        split at h
        · contradiction
        · rename_i fits
          cases h
          have prefixSize : (source.toList.take 4).length = 4 := by
            simp only [List.length_take, Bytes.length_toList]
            omega
          have definitionSize :
              ((source.toList.drop 4).take (KBytes.leVal (source.toList.take 4))).length =
                KBytes.leVal (source.toList.take 4) := by
            simp only [List.length_take, List.length_drop, Bytes.length_toList]
            omega
          refine ⟨source.toList.take 4, prefixSize, by simpa using definitionSize.symm, ?_, ?_⟩
          · rw [Bytes.length_ofList, definitionSize]
            omega
          · simp only [Bytes.toList_ofList, List.append_assoc, List.take_append_drop]
  · rintro ⟨lengthBytes, prefixSize, size, cap, bytes⟩
    have length : source.length = 4 + sections.definitions.length + sections.scalars.length := by
      rw [← Bytes.length_toList, bytes]
      simp [prefixSize, Nat.add_assoc]
    have hb : ¬ source.length < 4 := by omega
    have endFits : ¬ source.length < 4 + sections.definitions.length := by omega
    have hn : ¬ byteLimit < sections.definitions.length := by omega
    have first : source.toList.take 4 = lengthBytes := by
      rw [bytes, List.append_assoc, List.take_left' prefixSize]
    have tail : source.toList.drop 4 = sections.definitions.toList ++ sections.scalars.toList := by
      rw [bytes, List.append_assoc, List.drop_left' prefixSize]
    have takeDef :
        (sections.definitions.toList ++ sections.scalars.toList).take sections.definitions.length =
          sections.definitions.toList := List.take_left' (Bytes.length_toList _)
    have dropDef :
        (sections.definitions.toList ++ sections.scalars.toList).drop sections.definitions.length =
          sections.scalars.toList := List.drop_left' (Bytes.length_toList _)
    simp only [splitV1Optional, ite_eq_right hb, first, size, ite_eq_right hn, ite_eq_right endFits,
      tail, takeDef, dropDef, Bytes.ofList_toList]

public theorem splitV2_ok_iff {layout : Layout} {byteLimit repetitionBytes definitionBytes : Nat}
    {definitions scalars : Bytes} {sections : Sections} :
    split layout byteLimit (.v2 repetitionBytes definitionBytes definitions scalars) = .ok sections ↔
      repetitionBytes = 0 ∧ definitionBytes = definitions.length ∧
      definitionBytes < Hybrid.runLimit ∧ definitionBytes ≤ byteLimit ∧
      sections = ⟨definitions, scalars⟩ := by
  constructor
  · intro h
    simp only [split] at h
    split at h
    · contradiction
    · rename_i rep
      split at h
      · contradiction
      · rename_i defs
        split at h
        · contradiction
        · rename_i cap
          cases h
          exact ⟨by omega, by omega, by omega, by omega, rfl⟩
  · rintro ⟨rfl, size, bounded, cap, rfl⟩
    have defs : ¬ (definitionBytes ≠ definitions.length ∨ Hybrid.runLimit ≤ definitionBytes) := by omega
    simp [split, defs, Nat.not_lt_of_ge cap]

private theorem bytes_empty_iff (bytes : Bytes) : bytes.length = 0 ↔ bytes = .empty := by
  constructor
  · intro h
    apply Bytes.ext
    exact List.length_eq_zero_iff.mp (by simpa using h)
  · rintro rfl
    rfl

public theorem readMask_ok_iff {layout : Layout} {slots : Nat} {limits : Hybrid.Limits}
    {definitions : Bytes} {mask : List Bool} :
    readMask layout slots limits definitions = .ok mask ↔
      slots < Hybrid.runLimit ∧ slots ≤ limits.values ∧ definitions.length ≤ limits.bytes ∧
        MaskWire layout slots definitions mask := by
  by_cases count : Hybrid.runLimit ≤ slots ∨ limits.values < slots
  · simp only [readMask, ite_eq_left count, reduceCtorEq, false_iff]
    exact fun h => by omega
  · by_cases cap : limits.bytes < definitions.length
    · simp [readMask, count, cap, Nat.not_le_of_gt cap]
    · have hslots : slots < Hybrid.runLimit := by omega
      have hvalues : slots ≤ limits.values := by omega
      have hbytes : definitions.length ≤ limits.bytes := by omega
      have wire {levels : List Nat} : Hybrid.decode 1 slots limits definitions = .ok levels ↔
          Hybrid.Wire 1 slots definitions.toList levels := by
        simpa [hslots, hvalues, hbytes] using
          (Hybrid.decode_ok_iff (width := 1) (expected := slots) (limits := limits)
            (source := definitions) (values := levels))
      cases layout with
      | required =>
        by_cases empty : definitions.length = 0 <;>
          simp [readMask, count, cap, hslots, hvalues, hbytes, empty, MaskWire,
            ← bytes_empty_iff, eq_comm]
      | optional =>
        simp only [readMask, ite_eq_right count, ite_eq_right cap, hslots, hvalues, hbytes,
          true_and, MaskWire]
        constructor
        · intro h
          cases hr : Hybrid.decode 1 slots limits definitions with
          | error e => simp [hr] at h
          | ok levels =>
            simp only [hr, Except.ok.injEq] at h
            exact ⟨levels, wire.mp hr, h.symm⟩
        · rintro ⟨levels, hw, rfl⟩
          rw [wire.mpr hw]

public theorem readMask_length {layout : Layout} {slots : Nat} {limits : Hybrid.Limits}
    {definitions : Bytes} {mask : List Bool}
    (h : readMask layout slots limits definitions = .ok mask) : mask.length = slots := by
  obtain ⟨hslots, hvalues, hbytes, maskWire⟩ := readMask_ok_iff.mp h
  cases layout with
  | required =>
    obtain ⟨_, rfl⟩ := maskWire
    simp
  | optional =>
    obtain ⟨levels, wire, rfl⟩ := maskWire
    have parsed : Hybrid.decode 1 slots limits definitions = .ok levels :=
      Hybrid.decode_ok_iff.mpr ⟨by decide, hslots, hvalues, hbytes, wire⟩
    rw [List.length_map, Hybrid.decode_length parsed]

end Silmaril.Proofs.Formats.Parquet.FlatPage
