module

public import Silmaril.Formats.Compression.Zstd.CompressedBlock.Defs
import Silmaril.Formats.Compression.Zstd.LiteralBlock.Thms
import Silmaril.Formats.Compression.Zstd.SequenceTables.Repeat.Thms
import Silmaril.Formats.Compression.Zstd.SequenceDecode.Thms
import Silmaril.Formats.Compression.Zstd.Sequence.Thms
import Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.CompressedBlock

open Silmaril.Formats.Compression.Zstd
open Silmaril.Formats.Compression.Zstd.CompressedBlock

theorem decode_sound {limits : Limits} {prior : State} {declaredSize : Nat}
    {body : List UInt8} {result : Result} (accepted : prior.tables.Valid)
    (success : CompressedBlock.decode limits prior declaredSize body = .ok result) :
    body.length = declaredSize ∧ declaredSize ≤ limits.inputCapacity ∧
      result.bytes.length ≤ limits.execution.capacity ∧ result.next.Valid limits.window ∧
      BlockWire limits prior body result := by
  unfold CompressedBlock.decode at success
  split at success
  · cases success
  rename_i withinInput
  split at success
  · cases success
  split at success
  · cases success
  rename_i withinExtent
  have exactSize : body.length = declaredSize := Classical.not_not.mp withinExtent
  cases parsed : LiteralBlock.parseLiterals limits.execution.capacity body with
  | error reason => simp [parsed, Except.mapError, bind, Except.bind] at success
  | ok pair =>
    obtain ⟨literals, sequenceBytes⟩ := pair
    cases selected : SequenceTables.Repeat.resolve limits.sequences prior.tables sequenceBytes with
    | error reason => simp [parsed, selected, Except.mapError, bind, Except.bind] at success
    | ok pair =>
      obtain ⟨resolvedSection, tables⟩ := pair
      cases decoded : SequenceDecode.readResolved resolvedSection with
      | error reason => simp [parsed, selected, decoded, Except.mapError, bind, Except.bind] at success
      | ok commands =>
        cases executed : Sequence.execute limits.execution prior.history.recent literals.expand
            prior.history.offsets commands with
        | error reason => simp [parsed, selected, decoded, executed, Except.mapError, bind, Except.bind] at success
        | ok out =>
          simp only [parsed, selected, decoded, executed, Except.mapError, bind, Except.bind, pure,
            Except.pure] at success
          cases success
          obtain ⟨literalWire, literalBound⟩ := LiteralBlock.parseLiterals_sound parsed
          obtain ⟨_, countBound, sectionWire, stateUpdate⟩ := SequenceTables.Repeat.resolve_sound selected
          have valid := SequenceTables.Repeat.resolve_preserves_valid accepted selected
          have tableWitness := SequenceTables.Repeat.selected_tables_accepted stateUpdate valid
          have payload := SequenceDecode.readResolved_of_accepted tableWitness decoded
          have countExact : commands.length = resolvedSection.count := by
            cases payload with
            | empty => rfl
            | coded length _ _ _ => exact length
          obtain ⟨emitted, suffix, run, _, _, sizeEq, _, outputBound, _, offsetValid⟩ :=
            Sequence.execute_sound executed
          obtain ⟨_, historyBound, newOffsets⟩ :=
            CheckedFrame.Rle.advance_sound prior.history limits.window out.bytes out.offsets
          exact ⟨exactSize, Nat.le_of_not_gt withinInput, outputBound,
            ⟨valid, historyBound, newOffsets.symm ▸ offsetValid⟩,
            ⟨literals, sequenceBytes, resolvedSection, commands, emitted, suffix, out.offsets,
              literalWire, literalBound, sectionWire, stateUpdate, payload, countExact,
              countExact ▸ countBound, run, sizeEq, rfl⟩⟩

theorem decode_sequence_failure {limits : Limits} {prior : State} {declaredSize : Nat}
    {body sequenceBytes : List UInt8} {literals : LiteralBlock.Literals}
    {resolvedSection : SequenceTables.Section} {tables : SequenceTables.Repeat.State}
    {reason : SequenceDecode.Error}
    (fits : declaredSize ≤ limits.inputCapacity) (extent : body.length = declaredSize)
    (parsed : LiteralBlock.parseLiterals limits.execution.capacity body = .ok (literals, sequenceBytes))
    (selected : SequenceTables.Repeat.resolve limits.sequences prior.tables sequenceBytes =
      .ok (resolvedSection, tables))
    (failed : SequenceDecode.readResolved resolvedSection = .error reason) :
    CompressedBlock.decode limits prior declaredSize body = .error (.sequences reason) := by
  have noExtra : body.drop declaredSize = [] := List.drop_eq_nil_iff.mpr (by omega)
  simp [CompressedBlock.decode, Nat.not_lt.mpr fits, noExtra, extent, parsed, selected, failed,
    Except.mapError, bind, Except.bind]

theorem decode_execution_failure {limits : Limits} {prior : State} {declaredSize : Nat}
    {body sequenceBytes : List UInt8} {literals : LiteralBlock.Literals}
    {resolvedSection : SequenceTables.Section} {tables : SequenceTables.Repeat.State}
    {commands : List Sequence.Command} {reason : Sequence.Error}
    (fits : declaredSize ≤ limits.inputCapacity) (extent : body.length = declaredSize)
    (parsed : LiteralBlock.parseLiterals limits.execution.capacity body = .ok (literals, sequenceBytes))
    (selected : SequenceTables.Repeat.resolve limits.sequences prior.tables sequenceBytes =
      .ok (resolvedSection, tables))
    (decoded : SequenceDecode.readResolved resolvedSection = .ok commands)
    (failed : Sequence.execute limits.execution prior.history.recent literals.expand
      prior.history.offsets commands = .error reason) :
    CompressedBlock.decode limits prior declaredSize body = .error (.execution reason) := by
  have noExtra : body.drop declaredSize = [] := List.drop_eq_nil_iff.mpr (by omega)
  simp [CompressedBlock.decode, Nat.not_lt.mpr fits, noExtra, extent, parsed, selected, decoded, failed,
    Except.mapError, bind, Except.bind]

end Silmaril.Proofs.Formats.Compression.Zstd.CompressedBlock
