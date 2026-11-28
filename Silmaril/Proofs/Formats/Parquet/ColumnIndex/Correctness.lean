module

public import Silmaril.Formats.Parquet.ColumnIndex.Defs
import all Silmaril.Formats.Parquet.ColumnIndex.Defs
import Silmaril.Formats.Parquet.Footer.Thms
import Silmaril.Formats.Parquet.OffsetIndex.Thms
import Silmaril.Formats.ThriftCompact.Traversal.Thms
import Init.Data.ByteArray.Lemmas
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.ColumnIndex

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ColumnIndex
open ThriftCompact

public theorem readExact_ok_iff {limits : Limits} {bytes : Bytes} {raw : Raw} :
    readExact limits bytes = .ok raw ↔ readPrefix limits bytes = .ok (raw, bytes.length) := by
  cases parsed : readPrefix limits bytes with
  | error error => simp [readExact, parsed, bind, Except.bind]
  | ok value =>
    obtain ⟨found, next⟩ := value
    by_cases extent : next = bytes.length <;>
      simp [readExact, parsed, extent, bind, Except.bind, pure, Except.pure, throw]

public theorem readPrefix_stop {limits : Limits} {bytes : Bytes} {raw : Raw} {next : Nat}
    (h : readPrefix limits bytes = .ok (raw, next)) :
    ∃ stop, next = stop + 1 ∧ bytes.data[stop]? = some 0 := by
  let compact := limits.offsetIndex.compact
  let cap := min compact.maxCollectionSize limits.maxEntries
  let reader : Traversal.Reader := ⟨bytes, { compact with maxCollectionSize := cap }, limits.offsetIndex.varintMode⟩
  by_cases over : bytes.length > limits.maxIndexBytes
  · simp [readPrefix, over, throw] at h
  simp only [readPrefix, ite_eq_right over] at h
  change ((Traversal.readStruct reader 0).mapError Error.compact >>= _) = _ at h
  cases parsed : Traversal.readStruct reader 0 with
  | error error => simp [parsed, Except.mapError, bind, Except.bind] at h
  | ok pair =>
    obtain ⟨fields, endOffset⟩ := pair
    simp only [parsed, Except.mapError, bind, Except.bind] at h
    cases projected : project reader fields with
    | error error => rw [projected] at h; cases h
    | ok found =>
      rw [projected] at h
      simp [pure, Except.pure] at h
      rw [← h.2]
      exact Traversal.readStruct_stop parsed

private theorem checkCounts_sound {counts : Option (List Int)} {pages : List OffsetIndex.Entry}
    {flags : List Bool} (h : checkCounts counts pages flags = .ok ()) :
    ∀ values, counts = some values → values.length = pages.length ∧
      ∀ entry ∈ values.zip (pages.zip flags), ValidNullCount entry.1 entry.2.1 entry.2.2 := by
  intro values present
  subst counts
  simp only [checkCounts] at h
  split at h
  · cases h
  rename_i cardinality
  split at h
  · rename_i valid
    exact ⟨not_not.mp cardinality, fun entry member =>
      of_decide_eq_true (List.all_eq_true.mp valid entry member)⟩
  · cases h

public theorem checkShape_sound {raw : Raw} {pages : List OffsetIndex.Entry}
    (h : checkShape raw pages = .ok ()) : Aligned raw pages := by
  unfold checkShape at h
  dsimp only at h
  split at h
  · cases h
  rename_i flags
  split at h
  · cases h
  rename_i lower
  split at h
  · cases h
  rename_i upper
  split at h
  · cases h
  rename_i widths
  have valid : raw.claims.all (fun claim => decide claim.ValidWidth) = true := by simpa using widths
  exact ⟨not_not.mp flags, not_not.mp lower, not_not.mp upper,
    by simpa [List.all_eq_true] using valid, checkCounts_sound h⟩

private theorem validateAt_sound {limits : Limits} {snapshot : Snapshot.Checked}
    {column : Footer.ColumnChunk} {index : OffsetIndex.Index} {offset size : Int} {result : Index}
    (h : validateAt limits snapshot column index offset size = .ok result) :
    ∃ (chunk : Footer.Span) (bytes : Bytes),
      Footer.checkDataSpan snapshot.footer.start offset size = some result.span ∧
      Page.columnSpan snapshot.footer.start column.metadata = some chunk ∧
      chunk.stop ≤ result.span.start ∧
      (result.span.stop ≤ index.span.start ∨ index.span.stop ≤ result.span.start) ∧
      bytes.length ≤ limits.maxIndexBytes ∧
      snapshot.bytes.slice? result.span.start (some result.span.stop) = some bytes ∧
      readPrefix limits bytes = .ok (result.raw, bytes.length) ∧
      result.offsetIndex = index ∧ Aligned result.raw index.pages := by
  unfold validateAt at h
  split at h
  · cases h
  rename_i byteCap
  split at h
  · rename_i span spanEq
    split at h
    · rename_i chunk chunkEq
      split at h
      · cases h
      rename_i afterChunk
      split at h
      · cases h
      rename_i separated
      split at h
      · cases h
      rename_i bounded
      let bytes := Footer.fileBytes snapshot.bytes span.start span.stop
      change (do
        let raw ← readExact limits bytes
        let _ ← checkShape raw index.pages
        pure (⟨span, index, raw⟩ : Index)) = .ok result at h
      cases exactRead : readExact limits bytes with
      | error error => rw [exactRead] at h; cases h
      | ok raw =>
        cases shaped : checkShape raw index.pages with
        | error error => simp [exactRead, shaped, bind, Except.bind] at h
        | ok _ =>
          simp [exactRead, shaped, bind, Except.bind, pure, Except.pure] at h
          subst result
          have advertised := Footer.checkDataSpan_some_iff.mp spanEq
          have sliceEq : snapshot.bytes.slice? span.start (some span.stop) = some bytes := by
            apply Bytes.slice?_eq_some_iff.mpr
            refine ⟨by simpa using Nat.le_of_lt advertised.2.2.2.1, by simpa using Nat.le_of_not_gt bounded,
              Bytes.ext ?_⟩
            rw [Bytes.toList_ofList]
            simp [bytes, Footer.fileBytes, Bytes.toList, ByteArray.data_extract]
          have length := Bytes.length_of_slice? sliceEq
          simp only [Option.getD_some] at length
          have cap : bytes.length ≤ limits.maxIndexBytes := by
            have start := advertised.1
            have stop := advertised.2.1
            omega
          exact ⟨chunk, bytes, spanEq, chunkEq, Nat.le_of_not_gt afterChunk, not_not.mp separated, cap,
            sliceEq, readExact_ok_iff.mp exactRead, rfl, checkShape_sound shaped⟩
    · cases h
  · cases h

public theorem validate_present {limits : Limits} {snapshot : Snapshot.Checked} {g c : Nat} {result : Index}
    (h : validate limits snapshot g c = .ok (some result)) :
    ∃ group column chunk offsetBytes bytes, Evidence limits snapshot g c result group column chunk offsetBytes bytes := by
  unfold validate at h
  split at h
  · rename_i group groupAt
    split at h
    · rename_i column columnAt
      split at h
      · simp [pure, Except.pure] at h
      · rename_i offset size offsetEq sizeEq
        cases offsets : OffsetIndex.validate limits.offsetIndex snapshot g c with
        | error error => simp [offsets, Except.mapError, bind, Except.bind] at h
        | ok pairedOffset =>
          cases pairedOffset with
          | none => simp [offsets, Except.mapError, bind, Except.bind, throw] at h
          | some index =>
            simp only [offsets, Except.mapError, bind, Except.bind] at h
            change Except.map some (validateAt limits snapshot column index offset size) = .ok (some result) at h
            cases indexed : validateAt limits snapshot column index offset size with
            | error error => simp [indexed, Except.map] at h
            | ok paired =>
              simp [indexed, Except.map] at h
              subst result
              obtain ⟨chunk, bytes, reference, chunkEq, afterChunk, separated, cap, sliced, parsed, resultOffset, shape⟩ :=
                validateAt_sound indexed
              obtain ⟨offGroup, offColumn, offChunk, offsetBytes, evidence⟩ := OffsetIndex.validate_present offsets
              have sameGroup := Option.some.inj (groupAt.symm.trans evidence.selected.groupAt)
              subst offGroup
              have sameColumn := Option.some.inj (columnAt.symm.trans evidence.selected.columnAt)
              subst offColumn
              have sameChunk := Option.some.inj (chunkEq.symm.trans evidence.columnSpan)
              subst offChunk
              obtain ⟨startEq, stopEq, lower, nonempty, upper⟩ := Footer.checkDataSpan_some_iff.mp reference
              have widthEq : (↑(paired.span.stop - paired.span.start) : Int) = size := by omega
              exact ⟨group, column, chunk, offsetBytes, bytes, resultOffset.symm ▸ evidence,
                offsetEq.trans (congrArg some startEq.symm), sizeEq.trans (congrArg some widthEq.symm),
                ⟨lower, nonempty, upper⟩, afterChunk, by simpa [resultOffset] using separated,
                cap, sliced, parsed, by simpa [resultOffset] using shape⟩
      · cases h
    · cases h
  · cases h

public theorem validate_absent_iff {limits : Limits} {snapshot : Snapshot.Checked} {g c : Nat} :
    validate limits snapshot g c = .ok none ↔ ∃ group column,
      snapshot.groupAt g = some group ∧ group.columns[c]? = some column ∧
        column.columnIndexOffset = none ∧ column.columnIndexLength = none := by
  cases atGroup : snapshot.groupAt g with
  | none => simp [validate, atGroup]
  | some group =>
    cases atColumn : group.columns[c]? with
    | none => simp [validate, atGroup, atColumn]
    | some column =>
      cases offset : column.columnIndexOffset <;> cases size : column.columnIndexLength <;>
        simp [validate, atGroup, atColumn, offset, size, pure, Except.pure, throw]
      cases OffsetIndex.validate limits.offsetIndex snapshot g c with
      | error error => simp [Except.mapError, bind, Except.bind]
      | ok index =>
        cases index <;> simp [Except.mapError, bind, Except.bind]

public theorem pages_aligned {index : Index} (aligned : Aligned index.raw index.offsetIndex.pages) :
    index.pages.map Prod.fst = index.offsetIndex.pages ∧ index.pages.map Prod.snd = index.raw.claims := by
  have length : index.raw.claims.length = index.offsetIndex.pages.length := by
    simp [Raw.claims, aligned.flags, aligned.lower, aligned.upper]
  exact ⟨List.map_fst_zip (Nat.le_of_eq length.symm), List.map_snd_zip (Nat.le_of_eq length)⟩

public theorem readFile_ok_iff {limits : Limits} {source : Bytes} {g c : Nat} {result : Option Index} :
    readFile limits source g c = .ok result ↔ source.length ≤ limits.offsetIndex.maxFileBytes ∧
      ∃ snapshot, Snapshot.check (Failure := Unit) limits.offsetIndex.snapshot source = .ok snapshot ∧
        validate limits snapshot g c = .ok result := by
  by_cases size : source.length ≤ limits.offsetIndex.maxFileBytes
  · cases checked : Snapshot.check (Failure := Unit) limits.offsetIndex.snapshot source <;>
      simp [readFile, Nat.not_lt_of_ge size, size, checked, Except.mapError, bind, Except.bind]
  · simp [readFile, Nat.lt_of_not_ge size, size, throw]

end Silmaril.Proofs.Formats.Parquet.ColumnIndex
