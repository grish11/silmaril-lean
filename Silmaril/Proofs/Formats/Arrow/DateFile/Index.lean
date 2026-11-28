module

public import Silmaril.Formats.Arrow.DateFile.Defs
import all Silmaril.Formats.Arrow.DateFile.Defs
import Silmaril.Formats.Arrow.DateBatch.Thms
import Silmaril.Formats.Arrow.FileReader.Thms
import Silmaril.Formats.Arrow.Framing.Thms
import Silmaril.Prelude.Bytes.Thms
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Arrow.DateFile

open Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.DateFile

private theorem mapError_ok_iff {α ε δ : Type} {value : Except ε α} {f : ε → δ} {result : α} :
    value.mapError f = .ok result ↔ value = .ok result := by
  cases value <;> simp [Except.mapError]

private theorem selectDateUnit_ok_iff {kind : SchemaReader.FieldType} {unit : SchemaReader.DateUnit} :
    DateBatch.selectDateUnit kind = .ok unit ↔ kind = .date unit := by
  cases kind <;> simp [DateBatch.selectDateUnit]

theorem readIndex_exact {limits : Limits} {input : KBytes} {index : Index input}
    (admitted : DateFile.readIndex limits input = .ok index) :
    SchemaReader.readFileFooter limits (input.slice index.span.start index.span.length) =
      .ok ⟨index.schema, index.blocks⟩ ∧
      readEnvelope limits input 8 = .ok (.metadata index.schemaSize) ∧
      SchemaReader.readMessage limits index.schemaMetadata = .ok index.schema ∧
      readEnvelope limits input (index.span.start - 8) = .ok .eos := by
  simp only [DateFile.readIndex, Bind.bind, Except.bind] at admitted
  repeat' first | contradiction | split at admitted
  cases admitted
  simp_all [Index.schemaMetadata, mapError_ok_iff, selectDateUnit_ok_iff, Index.schema]
  cases_type SchemaReader.FileFooter
  repeat' cases_type SchemaReader.Schema
  cases_type SchemaReader.Field
  simp_all

theorem readRecord_checked {limits : Limits} {input : KBytes} {field : DateStream.Field}
    {block : FileBlock} {dates : DateValues.Column}
    (read : readRecord limits input field block = .ok dates) :
    ∃ batch,
      readEnvelope limits input block.offset = .ok (.metadata (block.metadataLength - 8)) ∧
      Arrow.readMessage limits (metadataSlice input block) = .ok ⟨.recordBatch batch, block.bodyLength⟩ ∧
      readBody limits input (block.offset + block.metadataLength) block.bodyLength =
        .ok (bodySlice input block) ∧
      DateValues.decodeBatch limits field.decoder field.descriptor batch (bodySlice input block) = .ok dates := by
  cases framed : readEnvelope limits input block.offset with
  | error => simp [readRecord, framed, Bind.bind, Except.bind, Except.mapError] at read
  | ok envelope =>
    cases envelope with
    | eos => simp [readRecord, framed, Bind.bind, Except.bind, Except.mapError] at read
    | metadata size =>
      by_cases width : 8 + size = block.metadataLength
      · cases parsed : Arrow.readMessage limits (metadataSlice input block) with
        | error =>
          simp [readRecord, framed, width, parsed, Bind.bind, Except.bind, Except.mapError] at read
        | ok message =>
          obtain ⟨header, length⟩ := message
          cases header with
          | schema =>
            simp [readRecord, framed, width, parsed, Bind.bind, Except.bind, Except.mapError] at read
          | recordBatch batch =>
            by_cases declared : length = block.bodyLength
            · cases bounded : readBody limits input (block.offset + block.metadataLength) block.bodyLength with
              | error =>
                simp [readRecord, framed, width, parsed, declared, bounded,
                  Bind.bind, Except.bind, Except.mapError] at read
              | ok body =>
                have extent : block.metadataLength - 8 = size := by omega
                have bodyEq := ((readBody_iff _ _ _ _ _).mp bounded).2.2.2.2
                refine ⟨batch, by simp [extent], by simp [declared], ?_, ?_⟩
                · simp only [bodyEq, bodySlice]
                · apply (mapError_ok_iff (f := BlockError.values)).mp
                  simpa [readRecord, framed, width, parsed, declared, bounded, Bind.bind,
                    Except.bind, Except.mapError, bodyEq, bodySlice] using read
            · simp [readRecord, framed, width, parsed, declared, Bind.bind,
                Except.bind, Except.mapError] at read
      · simp [readRecord, framed, width, Bind.bind, Except.bind, Except.mapError] at read

theorem readAt_exact {limits : Limits} {input : KBytes} {index : Index input}
    (admitted : DateFile.readIndex limits input = .ok index)
    {n : Nat} {dates : DateValues.Column} (read : index.readAt limits n = .ok (some dates)) :
    ∃ block, index.blocks[n]? = some block ∧
      block.endOffset ≤ index.span.start ∧
      readEnvelope limits input block.offset = .ok (.metadata (block.metadataLength - 8)) ∧
      (metadataSlice input block).toList =
        (input.toList.drop (block.offset + 8)).take (block.metadataLength - 8) ∧
      (bodySlice input block).toList =
        (input.toList.drop (block.offset + block.metadataLength)).take block.bodyLength ∧
      DateBatch.decode limits index.schemaMetadata (metadataSlice input block) (bodySlice input block) =
        .ok dates := by
  cases entry : index.blocks[n]? with
  | none => simp [Index.readAt, entry, Option.mapM, Pure.pure, Except.pure] at read
  | some block =>
    cases decoded : readRecord limits input index.field block with
    | error => simp [Index.readAt, entry, decoded, Option.mapM, Except.mapError, Functor.map, Except.map] at read
    | ok actual =>
      simp [Index.readAt, entry, decoded, Option.mapM, Except.mapError, Functor.map, Except.map] at read
      subst dates
      obtain ⟨batch, envelope, parsed, readBody, observed⟩ := readRecord_checked decoded
      obtain ⟨width, exactBody⟩ := body_exact index.span.source readBody
      have aligned := ((readBody_iff _ _ _ _ _).mp readBody).2.1
      have range := index.fits.block_range (List.mem_of_getElem? entry)
      refine ⟨block, rfl, range.2.2.2.2.2, envelope,
        metadata_exact index.span.source envelope, exactBody, ?_⟩
      simp [DateBatch.decode, (readIndex_exact admitted).2.2.1, Index.schema,
        DateBatch.selectDateUnit, parsed, width, aligned, Bind.bind, Except.bind, Except.mapError]
      exact (mapError_ok_iff (f := DateBatch.Error.values)).mpr observed

theorem readAt_absent_iff {limits : Limits} {input : KBytes} (index : Index input) (n : Nat) :
    index.readAt limits n = .ok none ↔ index.blocks[n]? = none := by
  cases entry : index.blocks[n]? with
  | none => simp [Index.readAt, entry, Option.mapM, Pure.pure, Except.pure]
  | some block =>
    cases decoded : readRecord limits input index.field block <;>
      simp [Index.readAt, entry, decoded, Option.mapM, Except.mapError, Functor.map, Except.map]

theorem readAt_error_iff {limits : Limits} {input : KBytes} (index : Index input)
    (n : Nat) (cause : BlockError) :
    index.readAt limits n = .error (.batch n cause) ↔
      ∃ block, index.blocks[n]? = some block ∧ readRecord limits input index.field block = .error cause := by
  cases entry : index.blocks[n]? with
  | none => simp [Index.readAt, entry, Option.mapM, Pure.pure, Except.pure]
  | some block =>
    cases decoded : readRecord limits input index.field block <;>
      simp [Index.readAt, entry, decoded, Option.mapM, Except.mapError, Functor.map, Except.map]

private theorem orderedLookup {α β ε δ : Type} {read : α → Except ε β}
    {entries : List α} {dates : List β}
    (ordered : List.Forall₂ (fun block column => read block = .ok column) entries dates)
    (wrap : ε → δ) (n : Nat) :
    entries[n]?.mapM (fun block => (read block).mapError wrap) = .ok dates[n]? := by
  induction ordered generalizing n with
  | nil => simp [Option.mapM, Pure.pure, Except.pure]
  | cons lead _ ih =>
    cases n with
    | zero => simp [Option.mapM, lead, Except.mapError, Functor.map, Except.map]
    | succ n => exact ih n

theorem readAt_sequential {limits : Limits} {input : KBytes} (index : Index input)
    {dates : List DateValues.Column}
    (sequential : index.blocks.mapM (readRecord limits input index.field) = .ok dates) (n : Nat) :
    index.readAt limits n = .ok dates[n]? :=
  orderedLookup (List.mapM_eq_ok_iff_forall₂.mp sequential) (DateFile.Error.batch n) n

end Silmaril.Proofs.Formats.Arrow.DateFile
