module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Defs
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Timestamp.Page.Thms
import Silmaril.Formats.Parquet.Timestamp.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Timestamp.Leaf

private theorem leafFields_inj {left right : Footer.SchemaElement}
    (same : Internal.leafFields left = Internal.leafFields right) : left = right := by
  cases left
  cases right
  simpa [Internal.leafFields] using same

theorem bindWith_sound {profile : Timestamp.AnnotationProfile} {limits : Footer.Limits} {snapshot : Snapshot.Checked} {ordinal : Nat} {bound : Bound}
    (accepted : Timestamp.Leaf.bindWith profile limits snapshot ordinal = .ok bound) :
    bound.snapshot = snapshot ∧ bound.ordinal = ordinal ∧ ordinal ≠ 0 ∧
      Internal.isFlat snapshot.metadata.schema = true ∧
      snapshot.metadata.schema[ordinal]? = some bound.binding.leaf ∧
      Timestamp.readMetadataWith profile limits ordinal (Internal.metadataBytes snapshot) = .ok bound.binding ∧
      Timestamp.Page.leafLevels? bound.binding.leaf = some bound.levels := by
  have observed := bindWith_observation profile limits snapshot ordinal
  rw [accepted] at observed
  cases flat : Internal.isFlat snapshot.metadata.schema with
  | false => simp [Internal.bindSelectionWith, flat, Bind.bind, Except.bind, Except.map] at observed
  | true =>
    cases leafRead : snapshot.metadata.schema[ordinal]? with
    | none => simp [Internal.bindSelectionWith, flat, leafRead, Except.map] at observed
    | some leaf =>
      cases annotation : Timestamp.readMetadataWith profile limits ordinal (Internal.metadataBytes snapshot) with
      | error =>
        simp [Internal.bindSelectionWith, flat, leafRead, annotation, Bind.bind, Except.bind,
          Except.mapError, Except.map] at observed
      | ok binding =>
        by_cases same : Internal.leafFields leaf = Internal.leafFields binding.leaf
        · cases levelsRead : Timestamp.Page.leafLevels? binding.leaf with
          | none =>
            simp [Internal.bindSelectionWith, flat, leafRead, annotation, same, levelsRead, Bind.bind,
              Except.bind, Except.mapError, Except.map] at observed
          | some levels =>
            have nonroot := (Timestamp.readMetadataWith_selects annotation).2.1.1
            simp [Internal.bindSelectionWith, flat, leafRead, annotation, same, levelsRead, Bind.bind,
              Except.bind, Except.mapError, Except.map, pure, Except.pure] at observed
            obtain ⟨snapshotEq, ordinalEq, bindingEq, levelsEq⟩ := observed
            refine ⟨snapshotEq, ordinalEq, nonroot, rfl, ?_, ?_, ?_⟩
            · rw [bindingEq]
              exact congrArg some (leafFields_inj same)
            · simp [bindingEq]
            · simp [bindingEq, levelsEq, levelsRead]
        · simp [Internal.bindSelectionWith, flat, leafRead, annotation, same, Bind.bind, Except.bind,
            Except.mapError, Except.map] at observed

theorem openLeafWith_sound {profile : Timestamp.AnnotationProfile} {limits : Snapshot.Limits} {source : Bytes} {ordinal : Nat} {bound : Bound}
    (accepted : openLeafWith profile limits source ordinal = .ok bound) :
    Snapshot.check (Failure := Unit) limits source = .ok bound.snapshot ∧
      Timestamp.Leaf.bindWith profile limits.footer bound.snapshot ordinal = .ok bound := by
  cases checked : Snapshot.check (Failure := Unit) limits source with
  | error => simp [openLeafWith, checked, Bind.bind, Except.bind, Except.mapError] at accepted
  | ok snapshot =>
    have boundRead : Timestamp.Leaf.bindWith profile limits.footer snapshot ordinal = .ok bound := by
      simpa [openLeafWith, checked, Bind.bind, Except.bind, Except.mapError] using accepted
    simp [(bindWith_sound boundRead).1, boundRead]

theorem selectChunk_sound {limits : Limits} {bound : Bound} {index : Nat} {chunk : Chunk}
    (selected : selectChunk limits bound index = .ok chunk) :
    bound.snapshot.groupAt index = some chunk.group ∧
      chunk.group.columns[bound.ordinal - 1]? = some chunk.column ∧
      chunk.column.metadata.pathInSchema = [bound.binding.leaf.name] ∧
      chunk.column.metadata.physicalType = .int64 ∧
      chunk.column.metadata.numValues = chunk.group.numRows ∧
      chunk.column.metadata.codec = 0 ∧
      chunk.group.numRows.toNat ≤ limits.maxRows ∧
      Parquet.Page.columnSpan bound.snapshot.footer.start chunk.column.metadata = some chunk.span ∧
      Internal.disjoint bound.snapshot index (bound.ordinal - 1) chunk.span = true := by
  cases groupRead : bound.snapshot.groupAt index with
  | none => simp [selectChunk, groupRead] at selected
  | some group =>
    cases columnRead : group.columns[bound.ordinal - 1]? with
    | none => simp [selectChunk, groupRead, columnRead] at selected
    | some column =>
      cases spanRead : Parquet.Page.columnSpan bound.snapshot.footer.start column.metadata with
      | none =>
        simp [selectChunk, groupRead, columnRead, spanRead, Bind.bind, Except.bind] at selected
        split_ifs at selected
      | some span =>
        cases separate : Internal.disjoint bound.snapshot index (bound.ordinal - 1) span <;>
          simp [selectChunk, groupRead, columnRead, spanRead, separate, Bind.bind, Except.bind,
            pure, Except.pure] at selected <;>
          split_ifs at selected
        rename_i selectedPath selectedType capped counted codec _
        have result := Except.ok.inj selected
        subst chunk
        have withinRows : group.numRows.toNat ≤ limits.maxRows := by omega
        exact ⟨rfl, columnRead, selectedPath, selectedType, counted, codec, withinRows, spanRead, separate⟩

private theorem decodeFrame_sound {limits : ScalarPage.Limits} {bound : Bound} {codec : Int}
    {frame : Parquet.Page.Frame} {index : Nat} {slots : Slots bound}
    (decoded : Internal.decodeFrame limits bound codec frame index = .ok slots) :
    ∃ raw, PhysicalFrame limits bound codec frame raw ∧
      slots = raw.map (Option.map bound.binding.descriptor.decode) ∧
      slots.length = Internal.pageSlots frame := by
  cases checksum : frame.value.crc with
  | some crc => simp [Internal.decodeFrame, checksum] at decoded
  | none =>
    have size : ¬ limits.compressedBytes < frame.value.compressedSize := by
      intro tooLarge
      simp [Internal.decodeFrame, checksum, tooLarge] at decoded
    have read : Timestamp.Page.decode bound.binding bound.levels codec frame.value limits
        (Internal.body bound frame) = .ok slots := by
      cases result : Timestamp.Page.decode bound.binding bound.levels codec frame.value limits
          (Internal.body bound frame) <;> simp_all [Internal.decodeFrame, Except.mapError]
    obtain ⟨params, raw, parameters, physical, mapped⟩ := Timestamp.Page.decode_eq_ok_iff.mp read
    have count := Timestamp.Page.decode_counts read
    refine ⟨raw, ⟨checksum, params, parameters, physical⟩, mapped, ?_⟩
    cases kind : frame.value.kind <;> simp_all [Internal.pageSlots]

private theorem decodeFrames_sound (limits : ScalarPage.Limits) (bound : Bound) (codec : Int)
    (frames : List Parquet.Page.Frame) (index : Nat) (pages : List (Slots bound))
    (decoded : (frames.zipIdx index).mapM (fun (frame, pageIndex) =>
      Internal.decodeFrame limits bound codec frame pageIndex) = .ok pages) :
    ∃ raw, List.Forall₂ (PhysicalFrame limits bound codec) frames raw ∧
      pages.flatten = raw.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      pages.flatten.length = (frames.map Internal.pageSlots).sum := by
  induction frames generalizing index pages with
  | nil =>
    have empty : [] = pages := by simpa [pure, Except.pure] using decoded
    subst pages
    exact ⟨[], .nil, rfl, rfl⟩
  | cons frame rest ih =>
    cases first : Internal.decodeFrame limits bound codec frame index with
    | error =>
      simp [first, Bind.bind, Except.bind] at decoded
    | ok slots =>
      cases remaining : (rest.zipIdx (index + 1)).mapM (fun (next, pageIndex) =>
          Internal.decodeFrame limits bound codec next pageIndex) with
      | error => simp [first, remaining, Bind.bind, Except.bind] at decoded
      | ok tail =>
        have ordered : slots :: tail = pages := by
          simpa [first, remaining, Bind.bind, Except.bind, pure, Except.pure] using decoded
        subst pages
        obtain ⟨raw, physical, mapped, count⟩ := decodeFrame_sound first
        obtain ⟨rawTail, physicalTail, mappedTail, countTail⟩ := ih _ _ remaining
        exact ⟨raw :: rawTail, .cons physical physicalTail,
          by simp [mapped, mappedTail], by simp [count, countTail]⟩

theorem readGroup_sound {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (accepted : readGroup limits bound index = .ok slots) :
    ∃ chunk frames raw,
      selectChunk limits bound index = .ok chunk ∧
      Parquet.Page.readChunk limits.framing bound.snapshot.bytes chunk.span = .ok frames ∧
      Parquet.Page.Chain chunk.span chunk.span.start chunk.span.stop frames ∧
      List.Forall₂ (PhysicalFrame limits.page bound chunk.column.metadata.codec) frames raw ∧
      slots = raw.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.length = chunk.group.numRows.toNat := by
  cases selected : selectChunk limits bound index with
  | error => simp [readGroup, selected, Bind.bind, Except.bind] at accepted
  | ok chunk =>
    cases framed : Parquet.Page.readChunk limits.framing bound.snapshot.bytes chunk.span with
    | error => simp [readGroup, selected, framed, Bind.bind, Except.bind, Except.mapError] at accepted
    | ok frames =>
      by_cases count : (frames.map Internal.pageSlots).sum = chunk.group.numRows.toNat
      · cases decoded : frames.zipIdx.mapM (fun (frame, pageIndex) =>
            Internal.decodeFrame limits.page bound chunk.column.metadata.codec frame pageIndex) with
        | error =>
          simp [readGroup, selected, framed, count, decoded, Bind.bind, Except.bind,
            Except.mapError] at accepted
        | ok pages =>
          have ordered : pages.flatten = slots := by
            simpa [readGroup, selected, framed, count, decoded, Bind.bind, Except.bind,
              Except.mapError, pure, Except.pure] using accepted
          obtain ⟨raw, physical, mapped, total⟩ := decodeFrames_sound _ _ _ _ _ _ decoded
          exact ⟨chunk, frames, raw, rfl, framed, (Parquet.Page.readChunk_chain framed).2.2,
            physical, ordered.symm.trans mapped, (congrArg List.length ordered.symm).trans (total.trans count)⟩
      · simp [readGroup, selected, framed, count, Bind.bind, Except.bind, Except.mapError] at accepted

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf
