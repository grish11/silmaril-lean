module

public import Silmaril.Formats.Arrow.MixedFlat.File.Window.Defs
import Silmaril.Formats.Arrow.MixedFlat.File.Thms
import Silmaril.Formats.Arrow.FileReader.Thms
import Silmaril.Formats.Arrow.Framing.Thms
import Silmaril.Prelude.Bytes.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Window

open Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.MixedFlat.File
open Silmaril.Formats.Arrow.MixedFlat.File.Window

private theorem mapError_ok_iff {α ε δ : Type} {value : Except ε α} {f : ε → δ} {result : α} :
    value.mapError f = .ok result ↔ value = .ok result := by
  cases value <;> simp [Except.mapError]

theorem readIndex_exact {limits : Arrow.Limits} {input : KBytes} {start stop : Nat}
    {index : Window.Index input start stop} (read : Window.readIndex limits input start stop = .ok index) :
    FileReader.readFooterSpan limits (input.slice start (stop - start)) = .ok index.span ∧
      MixedFlat.readFileFooter limits (input.slice index.footerStart index.span.length) = .ok index.footer ∧
      readEnvelope limits input (start + 8) = .ok (.metadata index.schemaSize) ∧
      MixedFlat.readSchema limits index.schemaMetadata = .ok index.footer.fields ∧
      readEnvelope limits input (index.footerStart - 8) = .ok .eos := by
  simp only [Window.readIndex, Bind.bind, Except.bind] at read
  repeat (split at read <;> try contradiction)
  cases read
  simp_all [Window.Index.footerStart, Window.Index.schemaMetadata, mapError_ok_iff]

theorem footer_range {input : KBytes} {start stop : Nat} (index : Window.Index input start stop) :
    start ≤ index.footerStart ∧ index.footerStart + index.span.length + 10 = stop ∧ stop ≤ input.len := by
  have extent := index.span.extent
  rw [KBytes.len_slice] at extent
  have ordered := index.bounds.ordered
  exact ⟨by unfold Window.Index.footerStart; omega,
    by unfold Window.Index.footerStart; omega, index.bounds.bounded⟩

private theorem blocks_before_eos {footer cursor : Nat} {blocks : List FileBlock}
    (fits : FileReader.BlocksFit footer cursor blocks) :
    cursor + 8 ≤ footer ∧ ∀ block ∈ blocks, block.endOffset + 8 ≤ footer := by
  induction blocks generalizing cursor with
  | nil => exact ⟨Nat.le_of_eq fits, by simp⟩
  | cons head tail ih =>
    obtain ⟨offset, _, _, _, _, _, rest⟩ := fits
    obtain ⟨afterHead, afterTail⟩ := ih rest
    refine ⟨?_, fun block member => ?_⟩
    · unfold FileBlock.endOffset at afterHead
      omega
    · rcases List.mem_cons.mp member with equal | later
      · subst block
        exact afterHead
      · exact afterTail block later

theorem block_ranges {input : KBytes} {start stop : Nat} (index : Window.Index input start stop)
    {block : FileBlock} (member : block ∈ index.footer.blocks) :
    start ≤ block.offset ∧
      block.offset + 8 ≤ block.offset + block.metadataLength ∧
      block.offset + block.metadataLength ≤ block.endOffset ∧
      block.endOffset + 8 ≤ index.footerStart ∧ index.footerStart ≤ stop := by
  obtain ⟨lower, _, prefixFits, _⟩ := index.fits.block_range member
  have finish := (blocks_before_eos index.fits).2 block member
  have footer := (footer_range index).2.1
  exact ⟨by omega, by omega, by unfold FileBlock.endOffset; omega, finish, by omega⟩

theorem footer_bytes_exact {input : KBytes} {start stop : Nat} (index : Window.Index input start stop) :
    (input.slice index.footerStart index.span.length).toList =
      (input.toList.drop index.footerStart).take index.span.length := by
  obtain ⟨_, extent, bounded⟩ := footer_range index
  exact KBytes.toList_slice _ _ _ index.bounds.source (by omega)

theorem readAt_exact {limits : MixedFlat.Limits} {input : KBytes} {start stop : Nat}
    {index : Window.Index input start stop} (checked : Window.readIndex limits.observation.ipc input start stop = .ok index)
    {n : Nat} {observed : MixedFlat.Observed} (read : index.readAt limits n = .ok (some observed)) :
    ∃ block, index.footer.blocks[n]? = some block ∧
      start ≤ block.offset ∧
      block.offset + 8 ≤ block.offset + block.metadataLength ∧
      block.offset + block.metadataLength ≤ block.endOffset ∧
      block.endOffset + 8 ≤ index.footerStart ∧ index.footerStart ≤ stop ∧
      readEnvelope limits.observation.ipc input block.offset = .ok (.metadata (block.metadataLength - 8)) ∧
      (input.slice block.offset 8).toList = (input.toList.drop block.offset).take 8 ∧
      (metadataSlice input block).toList =
        (input.toList.drop (block.offset + 8)).take (block.metadataLength - 8) ∧
      (bodySlice input block).toList =
        (input.toList.drop (block.offset + block.metadataLength)).take block.bodyLength ∧
      MixedFlat.readBatch limits index.schemaMetadata (metadataSlice input block) (bodySlice input block) =
        .ok observed := by
  cases entry : index.footer.blocks[n]? with
  | none => simp [Window.Index.readAt, entry, Option.mapM, Pure.pure, Except.pure] at read
  | some block =>
    cases recordRead : readRecord limits input index.footer.fields block with
    | error =>
      simp [Window.Index.readAt, entry, recordRead, Option.mapM, Except.mapError, Functor.map, Except.map] at read
    | ok result =>
      simp [Window.Index.readAt, entry, recordRead, Option.mapM, Except.mapError, Functor.map, Except.map] at read
      subst observed
      obtain ⟨record, body, envelope, parsed, bounded, decoded⟩ := MixedFlat.File.readRecord_witness recordRead
      have exactBody := ((readBody_iff _ _ _ _ _).mp bounded).2.2.2.2
      obtain ⟨lower, prefixFits, between, finish, footer⟩ := block_ranges index (List.mem_of_getElem? entry)
      have within := index.bounds.bounded
      refine ⟨block, rfl, lower, prefixFits, between, finish, footer, envelope,
        KBytes.toList_slice _ _ _ index.bounds.source (by omega),
        metadata_exact index.bounds.source envelope, ?_, ?_⟩
      · simpa only [bodySlice, ← exactBody] using (body_exact index.bounds.source bounded).2
      · simp [MixedFlat.readBatch, (readIndex_exact checked).2.2.2.1, parsed, bodySlice, ← exactBody,
          decoded, Bind.bind, Except.bind, Except.mapError]

end Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Window
