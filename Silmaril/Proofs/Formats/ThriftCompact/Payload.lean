module

public import Silmaril.Formats.ThriftCompact.Defs
import Init.Data.ByteArray.Lemmas
import Init.Omega

namespace Silmaril.Proofs.Formats.ThriftCompact

open Silmaril.Formats Silmaril.Formats.ThriftCompact

public theorem readFixed_ok_iff {count offset next : Nat} {source payload : Bytes} :
    readFixed count source offset = .ok (payload, next) ↔
      next = offset + count ∧
      source.slice? offset (some next) = some payload := by
  unfold readFixed
  have sliced (bounded : offset + count ≤ source.length) :
      source.slice? offset (some (offset + count)) =
        some ⟨source.data.extract offset (offset + count)⟩ := by
    apply Bytes.slice?_eq_some_iff.mpr
    refine ⟨by simp, bounded, Bytes.ext ?_⟩
    rw [Bytes.toList_ofList]
    simp [Bytes.toList, ByteArray.data_extract]
  by_cases bounded : offset + count ≤ source.length
  · rw [ite_eq_left bounded]
    constructor
    · intro h
      cases h
      exact ⟨rfl, sliced bounded⟩
    · rintro ⟨rfl, h⟩
      rw [sliced bounded] at h
      cases h
      rfl
  · simp only [ite_eq_right bounded, reduceCtorEq, false_iff]
    rintro ⟨rfl, h⟩
    exact bounded (Bytes.slice?_eq_some_iff.mp h).2.1

private theorem readLength_ok_iff {mode : VarintMode} {limit offset count next : Nat}
    {source : Bytes} :
    readLength mode limit source offset = .ok (count, next) ↔
      readVarint .i32 mode source offset = .ok (count, next) ∧ count < 2 ^ 31 ∧ count ≤ limit := by
  cases h : readVarint .i32 mode source offset with
  | error e => simp [readLength, h]
  | ok result =>
    obtain ⟨value, endOffset⟩ := result
    constructor
    · intro hread
      simp only [readLength, h] at hread
      split at hread
      · rename_i width
        split at hread
        · rename_i cap
          cases hread
          exact ⟨rfl, width, cap⟩
        · contradiction
      · contradiction
    · rintro ⟨heq, width, cap⟩
      cases heq
      simp [readLength, h, width, cap]

public theorem readBinary_ok_iff {mode : VarintMode} {limit offset next : Nat}
    {source payload : Bytes} :
    readBinary mode limit source offset = .ok (payload, next) ↔
      ∃ count payloadOffset,
        readVarint .i32 mode source offset = .ok (count, payloadOffset) ∧
        count < 2 ^ 31 ∧ count ≤ limit ∧ next = payloadOffset + count ∧
        source.slice? payloadOffset (some next) = some payload := by
  constructor
  · intro h
    cases hlen : readLength mode limit source offset with
    | error e => simp [readBinary, hlen, bind, Except.bind] at h
    | ok result =>
      obtain ⟨count, payloadOffset⟩ := result
      simp only [readBinary, hlen, bind, Except.bind] at h
      obtain ⟨hvar, width, cap⟩ := readLength_ok_iff.mp hlen
      exact ⟨count, payloadOffset, hvar, width, cap, readFixed_ok_iff.mp h⟩
  · rintro ⟨count, payloadOffset, hvar, width, cap, hend, hslice⟩
    simp only [readBinary, readLength_ok_iff.mpr ⟨hvar, width, cap⟩, bind, Except.bind]
    exact readFixed_ok_iff.mpr ⟨hend, hslice⟩

end Silmaril.Proofs.Formats.ThriftCompact
