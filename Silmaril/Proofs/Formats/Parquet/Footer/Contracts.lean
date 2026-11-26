module

public import Silmaril.Formats.Parquet.Footer.Defs
import Init.Data.ByteArray.Lemmas
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.Footer

open Silmaril.Formats Silmaril.Formats.Parquet.Footer

public theorem locate_ok_iff {limit : Nat} {file : Bytes} {span : Span} :
    locate limit file = .ok span ↔ Framed limit file span := by
  constructor
  · intro h
    simp only [locate] at h
    split at h
    · contradiction
    · rename_i fileSize
      split at h
      · contradiction
      · rename_i leading
        split at h
        · contradiction
        · rename_i trailing
          split at h
          · contradiction
          · rename_i count
            split at h
            · contradiction
            · rename_i cap
              cases h
              refine ⟨of_not_not leading, of_not_not trailing, ?_, ?_, ?_, ?_, by omega⟩
              · change 4 ≤ file.length - 8 - footerLength file
                omega
              · change file.length - 8 - footerLength file < file.length - 8
                omega
              · change file.length - 8 + 8 = file.length
                omega
              · change file.length - 8 - (file.length - 8 - footerLength file) = footerLength file
                omega
  · rintro ⟨leading, trailing, start, ordered, stop, length, cap⟩
    have fileSize : ¬ file.length < 12 := by omega
    have count : ¬ (footerLength file = 0 ∨ file.length - 8 - 4 < footerLength file) := by omega
    have bound : ¬ limit < footerLength file := by omega
    have spanEq : (⟨file.length - 8 - footerLength file, file.length - 8⟩ : Span) = span := by
      cases span with
      | mk first last =>
        change 4 ≤ first at start
        change first < last at ordered
        change last + 8 = file.length at stop
        change last - first = footerLength file at length
        congr <;> omega
    simp [locate, fileSize, leading, trailing, count, bound, spanEq]

public theorem framed_slice {limit : Nat} {file : Bytes} {span : Span}
    (h : Framed limit file span) :
    file.slice? span.start (some span.stop) = some (fileBytes file span.start span.stop) := by
  obtain ⟨_, _, _, ordered, stop, _, _⟩ := h
  apply Bytes.slice?_eq_some_iff.mpr
  refine ⟨by simp; omega, by simp; omega, Bytes.ext ?_⟩
  rw [Bytes.toList_ofList]
  simp [fileBytes, Bytes.toList, ByteArray.data_extract]

public theorem readMetadata_ok_iff {limits : Limits} {source : Bytes} {metadata : Metadata} :
    readMetadata limits source = .ok metadata ↔
      readMetadataPrefix ⟨source, limits.compact, limits.varintMode⟩ 0 = .ok (metadata, source.length) := by
  cases h : readMetadataPrefix ⟨source, limits.compact, limits.varintMode⟩ 0 with
  | error e => simp [readMetadata, h, Except.mapError, bind, Except.bind]
  | ok result =>
    obtain ⟨value, next⟩ := result
    by_cases endOfSlice : next = source.length
    · simp [readMetadata, h, Except.mapError, bind, Except.bind, pure, Except.pure, endOfSlice]
    · simp [readMetadata, h, Except.mapError, bind, Except.bind, endOfSlice]

public theorem readFooter_ok_iff {limits : Limits} {file : Bytes} {span : Span} {metadata : Metadata} :
    readFooter limits file = .ok (span, metadata) ↔
      Framed limits.maxFooterBytes file span ∧ ∃ payload : Bytes,
        file.slice? span.start (some span.stop) = some payload ∧
        readMetadataPrefix ⟨payload, limits.compact, limits.varintMode⟩ 0 =
          .ok (metadata, footerLength file) := by
  constructor
  · intro success
    cases loc : locate limits.maxFooterBytes file with
    | error error => simp [readFooter, loc, Except.mapError, bind, Except.bind] at success
    | ok found =>
      cases parsed : readMetadata limits (fileBytes file found.start found.stop) with
      | error error => simp [readFooter, loc, parsed, Except.mapError, bind, Except.bind] at success
      | ok value =>
        have eq : (found, value) = (span, metadata) := by
          simpa [readFooter, loc, parsed, Except.mapError, bind, Except.bind, pure, Except.pure] using success
        cases eq
        have framed := locate_ok_iff.mp loc
        have slice := framed_slice framed
        have length := (Bytes.length_of_slice? slice).trans framed.width
        exact ⟨framed, _, slice, length ▸ readMetadata_ok_iff.mp parsed⟩
  · rintro ⟨framed, payload, slice, parsed⟩
    have loc := locate_ok_iff.mpr framed
    have length := (Bytes.length_of_slice? slice).trans framed.width
    rw [framed_slice framed] at slice
    cases slice
    have success := readMetadata_ok_iff.mpr (length.symm ▸ parsed)
    simp [readFooter, loc, success, Except.mapError, bind, Except.bind, pure, Except.pure]

public theorem checkDataSpan_some_iff {footerStart : Nat} {offset size : Int} {span : Span} :
    checkDataSpan footerStart offset size = some span ↔
      (span.start : Int) = offset ∧ (span.stop : Int) = offset + size ∧
      4 ≤ span.start ∧ span.start < span.stop ∧ span.stop ≤ footerStart := by
  unfold checkDataSpan
  split
  · rename_i h
    constructor
    · intro equal
      cases equal
      change (offset.toNat : Int) = offset ∧ ((offset + size).toNat : Int) = offset + size ∧
        4 ≤ offset.toNat ∧ offset.toNat < (offset + size).toNat ∧ (offset + size).toNat ≤ footerStart
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    · rintro ⟨start, stop, _, _, _⟩
      have startEq : offset.toNat = span.start := by omega
      have stopEq : (offset + size).toNat = span.stop := by omega
      cases span
      simp_all
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    rintro ⟨start, stop, lower, positive, upper⟩
    exact h ⟨by omega, by omega, by omega⟩

end Silmaril.Proofs.Formats.Parquet.Footer
