module

public import Silmaril.Formats.Arrow.FileReader.FooterOnly.Defs
import Silmaril.Formats.Arrow.FileReader.Thms
import Silmaril.Prelude.Bytes.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Arrow.FileReader.FooterOnly

open Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.FileReader.FooterOnly

theorem readIndex_exact {limits : Limits} {input : KBytes} {index : Index input}
    (read : readIndex limits input = .ok index) :
    FileReader.readFooterSpan limits input = .ok index.span ∧
      readFileFooter limits (input.slice index.span.start index.span.length) = .ok index.footer ∧
      readEnvelope limits input (index.span.start - 8) = .ok .eos ∧
      checkFirstRecord limits input index.footer.blocks = .ok () := by
  cases spanRead : FileReader.readFooterSpan limits input with
  | error => simp [readIndex, spanRead, Bind.bind, Except.bind] at read
  | ok span =>
    cases footerRead : readFileFooter limits (input.slice span.start span.length) with
    | error => simp [readIndex, spanRead, footerRead, Bind.bind, Except.bind] at read
    | ok footer =>
      by_cases fits : FileReader.BlocksFit span.start 8 footer.blocks
      · cases endRead : readEnvelope limits input (span.start - 8) with
        | error => simp [readIndex, spanRead, footerRead, fits, endRead, Bind.bind, Except.bind] at read
        | ok envelope =>
          cases envelope with
          | metadata =>
            simp [readIndex, spanRead, footerRead, fits, endRead, Bind.bind, Except.bind, throw] at read
          | eos =>
            cases firstRead : checkFirstRecord limits input footer.blocks with
            | error =>
              simp [readIndex, spanRead, footerRead, fits, endRead, firstRead, Bind.bind, Except.bind] at read
            | ok result =>
              cases result
              have same : (⟨span, footer, fits⟩ : Index input) = index := by
                simpa [readIndex, spanRead, footerRead, fits, endRead, firstRead, Bind.bind, Except.bind,
                  Pure.pure, Except.pure] using read
              subst index
              exact ⟨rfl, footerRead, endRead, firstRead⟩
      · simp [readIndex, spanRead, footerRead, fits, Bind.bind, Except.bind, throw] at read

theorem readIndex_schema_only {limits : Limits} {input : KBytes} {index : Index input}
    (read : readIndex limits input = .ok index) (empty : index.footer.blocks = []) :
    index.span.start = 16 ∧ readEnvelope limits input 8 = .ok .eos := by
  have fits := index.fits
  rw [empty] at fits
  have start : index.span.start = 16 := fits.symm
  exact ⟨start, by simpa only [start] using (readIndex_exact read).2.2.1⟩

theorem readIndex_firstRecord {limits : Limits} {input : KBytes} {index : Index input}
    {block : FileBlock} {rest : List FileBlock} (read : readIndex limits input = .ok index)
    (first : index.footer.blocks = block :: rest) :
    block.offset = 8 ∧
      readEnvelope limits input 8 = .ok (.metadata (block.metadataLength - 8)) ∧
      ∃ record, readMessage limits (input.slice 16 (block.metadataLength - 8)) =
        .ok ⟨.recordBatch record, block.bodyLength⟩ := by
  have fits := index.fits
  rw [first] at fits
  have checked := (readIndex_exact read).2.2.2
  rw [first] at checked
  refine ⟨fits.1, ?_⟩
  cases envelopeRead : readEnvelope limits input 8 with
  | error => simp [checkFirstRecord, envelopeRead, Bind.bind, Except.bind] at checked
  | ok envelope =>
    cases envelope with
    | eos => simp [checkFirstRecord, envelopeRead, Bind.bind, Except.bind, throw] at checked
    | metadata size =>
      by_cases width : 8 + size = block.metadataLength
      · cases messageRead : readMessage limits (input.slice 16 size) with
        | error => simp [checkFirstRecord, envelopeRead, width, messageRead, Bind.bind,
            Except.bind] at checked
        | ok message =>
          obtain ⟨header, length⟩ := message
          cases header with
          | schema => simp [checkFirstRecord, envelopeRead, width, messageRead,
              Bind.bind, Except.bind, throw] at checked
          | recordBatch batch =>
            by_cases body : length = block.bodyLength
            · have metadataSize : block.metadataLength - 8 = size := by omega
              exact ⟨by rw [metadataSize], batch, by rw [metadataSize, messageRead, body]⟩
            · simp [checkFirstRecord, envelopeRead, width, messageRead, body,
                Bind.bind, Except.bind, throw] at checked
      · simp [checkFirstRecord, envelopeRead, width, Bind.bind, Except.bind, throw] at checked

theorem readBatchAt_exact {input : KBytes} (index : Index input) {limits : Limits} {n : Nat}
    {frame : BatchFrame index.footer.fields} (read : index.readBatchAt limits n = .ok (some frame)) :
    ∃ block, index.footer.blocks[n]? = some block ∧
      8 ≤ block.offset ∧ block.endOffset ≤ index.span.start ∧
      readEnvelope limits input block.offset = .ok (.metadata (block.metadataLength - 8)) ∧
      (input.slice (block.offset + 8) (block.metadataLength - 8)).toList =
        (input.toList.drop (block.offset + 8)).take (block.metadataLength - 8) ∧
      readMessage limits (input.slice (block.offset + 8) (block.metadataLength - 8)) =
        .ok ⟨.recordBatch frame.metadata, block.bodyLength⟩ ∧
      frame.body.len = block.bodyLength ∧ frame.body.toList =
        (input.toList.drop (block.offset + block.metadataLength)).take block.bodyLength := by
  cases selected : index.footer.blocks[n]? with
  | none =>
    have attached : index.toFileIndex.footer.blocks.attach[n]? = none := by
      change index.footer.blocks.attach[n]? = none
      rw [List.getElem?_attach, Option.pmap_none' selected]
    simp [Index.readBatchAt, FileReader.Index.readBatchAt, attached, Pure.pure, Except.pure] at read
    cases read
  | some block =>
    have member := List.mem_of_getElem? selected
    have attached : index.toFileIndex.footer.blocks.attach[n]? =
        some ⟨block, member⟩ := by
      change index.footer.blocks.attach[n]? = some ⟨block, member⟩
      rw [List.getElem?_attach, Option.pmap_some' selected]
    simp only [Index.readBatchAt, FileReader.Index.readBatchAt, attached, Option.mapM_some] at read
    have picked : index.toFileIndex.readBlock limits block member = .ok frame := by
      cases frameRead : index.toFileIndex.readBlock limits block member with
      | error => simp [frameRead, Functor.map, Except.map] at read
      | ok =>
        simp only [frameRead, Functor.map, Except.map] at read
        cases read
        rfl
    obtain ⟨start, _, metadataLength, _, _, finish⟩ := FileReader.BlocksFit.block_range index.fits member
    obtain ⟨envelope, metadata, bodyLength, body⟩ := index.toFileIndex.readBlock_exact limits member picked
    refine ⟨block, rfl, start, finish, envelope, ?_, metadata, bodyLength, body⟩
    apply KBytes.toList_slice _ _ _ index.span.source
    have extent := index.span.extent
    unfold FileBlock.endOffset at finish
    omega

theorem readRowsAt_exact {input : KBytes} (index : Index input) {limits : ObservationLimits}
    {n : Nat} {rows : List Row} (read : index.readRowsAt limits n = .ok (some rows)) :
    ∃ frame, index.readBatchAt limits.ipc n = .ok (some frame) ∧
      decodeBatch limits frame = .ok rows := by
  change (do
    let batch ← index.readBatchAt limits.ipc n
    batch.mapM (decodeBatch limits)) = .ok (some rows) at read
  cases selected : index.readBatchAt limits.ipc n with
  | error => simp [selected, Bind.bind, Except.bind] at read
  | ok batch =>
    cases batch with
    | none =>
      simp only [selected, Bind.bind, Except.bind, Option.mapM_none, Pure.pure, Except.pure] at read
      cases read
    | some frame =>
      cases decoded : decodeBatch limits frame with
      | error => simp [selected, decoded, Bind.bind, Except.bind, Functor.map, Except.map] at read
      | ok result =>
        simp only [selected, decoded, Bind.bind, Except.bind, Option.mapM_some, Functor.map, Except.map] at read
        cases read
        exact ⟨frame, rfl, decoded⟩

end Silmaril.Proofs.Formats.Arrow.FileReader.FooterOnly
