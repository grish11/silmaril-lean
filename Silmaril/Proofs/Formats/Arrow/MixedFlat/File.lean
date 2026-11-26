module

public import Silmaril.Formats.Arrow.MixedFlat.File.Defs
import Silmaril.Formats.Arrow.FileReader.Thms
import Silmaril.Formats.Arrow.Framing.Thms
import Batteries.Data.List.Lemmas
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.File

open Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.MixedFlat.File

private theorem mapError_ok_iff {α ε δ : Type} {value : Except ε α} {f : ε → δ} {result : α} :
    value.mapError f = .ok result ↔ value = .ok result := by
  cases value <;> simp [Except.mapError]

theorem readIndex_exact {limits : Arrow.Limits} {input : KBytes} {index : Index input}
    (read : readIndex limits input = .ok index) :
    MixedFlat.readFileFooter limits (input.slice index.span.start index.span.length) = .ok index.footer ∧
      readEnvelope limits input 8 = .ok (.metadata index.schemaSize) ∧
      MixedFlat.readSchema limits index.schemaMetadata = .ok index.footer.fields ∧
      readEnvelope limits input (index.span.start - 8) = .ok .eos := by
  simp only [readIndex, bind, Except.bind] at read
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  cases read
  simp_all [Index.schemaMetadata, mapError_ok_iff]

theorem readRecord_witness {limits : MixedFlat.Limits} {input : KBytes}
    {fields : List MixedFlat.Field} {block : FileBlock} {observed : MixedFlat.Observed}
    (read : readRecord limits input fields block = .ok observed) :
    ∃ record body,
      readEnvelope limits.observation.ipc input block.offset = .ok (.metadata (block.metadataLength - 8)) ∧
      MixedFlat.readMetadata limits.observation.ipc limits.view.dataBuffers limits.totalDataBuffers
        fields (metadataSlice input block) = .ok record ∧
      readBody limits.observation.ipc input (block.offset + block.metadataLength) block.bodyLength = .ok body ∧
      MixedFlat.readParsed limits fields record body = .ok observed := by
  cases prefixRead : readEnvelope limits.observation.ipc input block.offset with
  | error => simp [readRecord, prefixRead, bind, Except.bind, Except.mapError] at read
  | ok frame =>
    cases frame with
    | eos => simp [readRecord, prefixRead, bind, Except.bind, Except.mapError] at read
    | metadata size =>
      by_cases lengthMatches : 8 + size = block.metadataLength
      · cases parsed : MixedFlat.readMetadata limits.observation.ipc limits.view.dataBuffers
          limits.totalDataBuffers fields (metadataSlice input block) with
        | error =>
          simp [readRecord, prefixRead, lengthMatches, parsed, bind, Except.bind, Except.mapError] at read
        | ok record =>
          by_cases bodyMatches : record.bodyLength = block.bodyLength
          · cases bounded : readBody limits.observation.ipc input
              (block.offset + block.metadataLength) block.bodyLength with
            | error =>
              simp [readRecord, prefixRead, lengthMatches, parsed, bodyMatches, bounded,
                bind, Except.bind, Except.mapError] at read
            | ok body =>
              cases decoded : MixedFlat.readParsed limits fields record body with
              | error =>
                simp [readRecord, prefixRead, lengthMatches, parsed, bodyMatches, bounded, decoded,
                  bind, Except.bind, Except.mapError] at read
              | ok result =>
                simp [readRecord, prefixRead, lengthMatches, parsed, bodyMatches, bounded, decoded,
                  bind, Except.bind, Except.mapError] at read
                subst observed
                have width : block.metadataLength - 8 = size := by omega
                exact ⟨record, body, by simp [width], rfl, rfl, decoded⟩
          · simp [readRecord, prefixRead, lengthMatches, parsed, bodyMatches,
              bind, Except.bind, Except.mapError] at read
      · simp [readRecord, prefixRead, lengthMatches, bind, Except.bind, Except.mapError] at read

theorem readAt_exact {limits : MixedFlat.Limits} {input : KBytes} {index : Index input}
    (checked : readIndex limits.observation.ipc input = .ok index)
    {n : Nat} {observed : MixedFlat.Observed} (read : index.readAt limits n = .ok (some observed)) :
    ∃ block, index.footer.blocks[n]? = some block ∧
      block.endOffset ≤ index.span.start ∧
      readEnvelope limits.observation.ipc input block.offset = .ok (.metadata (block.metadataLength - 8)) ∧
      (metadataSlice input block).toList =
        (input.toList.drop (block.offset + 8)).take (block.metadataLength - 8) ∧
      (bodySlice input block).toList =
        (input.toList.drop (block.offset + block.metadataLength)).take block.bodyLength ∧
      MixedFlat.readBatch limits index.schemaMetadata (metadataSlice input block) (bodySlice input block) =
        .ok observed := by
  cases entry : index.footer.blocks[n]? with
  | none => simp [Index.readAt, entry, Option.mapM, pure, Except.pure] at read
  | some block =>
    cases recordRead : readRecord limits input index.footer.fields block with
    | error =>
      simp [Index.readAt, entry, recordRead, Option.mapM, Except.mapError, Functor.map, Except.map] at read
    | ok result =>
      simp [Index.readAt, entry, recordRead, Option.mapM, Except.mapError, Functor.map, Except.map] at read
      subst observed
      obtain ⟨record, body, envelope, parsed, bounded, decoded⟩ := readRecord_witness recordRead
      have exactBody := ((readBody_iff _ _ _ _ _).mp bounded).2.2.2.2
      have range := index.fits.block_range (List.mem_of_getElem? entry)
      refine ⟨block, rfl, range.2.2.2.2.2, envelope, metadata_exact index.span.source envelope, ?_, ?_⟩
      · simpa only [bodySlice, ← exactBody] using (body_exact index.span.source bounded).2
      · simp [MixedFlat.readBatch, (readIndex_exact checked).2.2.1, parsed, bodySlice, ← exactBody, decoded,
          bind, Except.bind, Except.mapError]

private theorem ordered_lookup {α β ε : Type} {f : α → Except ε β}
    {entries : List α} {observed : List β}
    (ordered : List.Forall₂ (fun a b => f a = .ok b) entries observed) (n : Nat) :
    entries[n]?.mapM f = .ok observed[n]? := by
  induction ordered generalizing n with
  | nil => simp [Option.mapM, pure, Except.pure]
  | @cons a b as bs head _ ih =>
    cases n with
    | zero => simp [Option.mapM, head, Functor.map, Except.map]
    | succ n => exact ih n

theorem readAt_sequential {limits : MixedFlat.Limits} {input : KBytes} (index : Index input)
    {observed : List MixedFlat.Observed}
    (sequential : index.footer.blocks.mapM (readRecord limits input index.footer.fields) = .ok observed)
    (n : Nat) : index.readAt limits n = .ok observed[n]? := by
  have nth := ordered_lookup (List.mapM_eq_ok_iff_forall₂.mp sequential) n
  cases entry : index.footer.blocks[n]? with
  | none => simpa [Index.readAt, entry, Option.mapM, pure, Except.pure] using nth
  | some block =>
    cases record : readRecord limits input index.footer.fields block with
    | error => simp [entry, record, Option.mapM, Functor.map, Except.map] at nth
    | ok value =>
      simpa [Index.readAt, entry, record, Option.mapM, Except.mapError, Functor.map, Except.map] using nth

end Silmaril.Proofs.Formats.Arrow.MixedFlat.File
