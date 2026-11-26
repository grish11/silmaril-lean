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

namespace Internal

theorem checkExtent_iff {limits : Limits} {declaredSize : Nat} {body : List UInt8} :
    CompressedBlock.Internal.checkExtent limits declaredSize body = .ok () ↔
      body.length = declaredSize ∧ declaredSize ≤ limits.inputCapacity := by
  constructor
  · intro checked
    unfold CompressedBlock.Internal.checkExtent at checked
    split at checked
    · cases checked
    rename_i withinInput
    split at checked
    · cases checked
    split at checked
    · cases checked
    rename_i withinExtent
    exact ⟨Classical.not_not.mp withinExtent, Nat.le_of_not_gt withinInput⟩
  · rintro ⟨extent, fits⟩
    have noExtra : body.drop declaredSize = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [CompressedBlock.Internal.checkExtent, Nat.not_lt.mpr fits, noExtra, extent]

theorem execute_sound {limits : Limits} {prior : State} {literals : LiteralBlock.Literals}
    {sequenceBytes : List UInt8} {result : Result} (accepted : prior.tables.Valid)
    (success : CompressedBlock.Internal.execute limits prior literals sequenceBytes = .ok result) :
    result.bytes.length ≤ limits.execution.capacity ∧ result.next.Valid limits.window ∧
      CompressedBlock.Internal.SequenceWire limits prior literals sequenceBytes result := by
  unfold CompressedBlock.Internal.execute at success
  cases selected : SequenceTables.Repeat.resolve limits.sequences prior.tables sequenceBytes with
  | error reason => simp [selected, Except.mapError, bind, Except.bind] at success
  | ok pair =>
    obtain ⟨resolvedSection, tables⟩ := pair
    cases decoded : SequenceDecode.readResolved resolvedSection with
    | error reason => simp [selected, decoded, Except.mapError, bind, Except.bind] at success
    | ok commands =>
      cases executed : Sequence.execute limits.execution prior.history.recent literals.expand
          prior.history.offsets commands with
      | error reason => simp [selected, decoded, executed, Except.mapError, bind, Except.bind] at success
      | ok out =>
        simp only [selected, decoded, executed, Except.mapError, bind, Except.bind, pure,
          Except.pure] at success
        cases success
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
        exact ⟨outputBound, ⟨valid, historyBound, newOffsets.symm ▸ offsetValid⟩,
          ⟨resolvedSection, commands, emitted, suffix, out.offsets, sectionWire, stateUpdate,
            payload, countExact, countExact ▸ countBound, run, sizeEq, rfl⟩⟩

end Internal

theorem decode_sound {limits : Limits} {prior : State} {declaredSize : Nat}
    {body : List UInt8} {result : Result} (accepted : prior.tables.Valid)
    (success : CompressedBlock.decode limits prior declaredSize body = .ok result) :
    body.length = declaredSize ∧ declaredSize ≤ limits.inputCapacity ∧
      result.bytes.length ≤ limits.execution.capacity ∧ result.next.Valid limits.window ∧
      BlockWire limits prior body result := by
  unfold CompressedBlock.decode at success
  cases extent : CompressedBlock.Internal.checkExtent limits declaredSize body with
  | error reason => simp [extent, bind, Except.bind] at success
  | ok successUnit =>
    cases successUnit
    obtain ⟨size, inputBound⟩ := Internal.checkExtent_iff.mp extent
    cases parsed : LiteralBlock.parseLiterals limits.execution.capacity body with
    | error reason => simp [extent, parsed, Except.mapError, bind, Except.bind] at success
    | ok pair =>
      obtain ⟨literals, sequenceBytes⟩ := pair
      simp only [extent, parsed, Except.mapError, bind, Except.bind] at success
      obtain ⟨literalWire, literalBound⟩ := LiteralBlock.parseLiterals_sound parsed
      obtain ⟨outputBound, nextValid, wire⟩ := Internal.execute_sound accepted success
      obtain ⟨resolved, commands, emitted, suffix, offsets, seqWire⟩ := wire
      exact ⟨size, inputBound, outputBound, nextValid, literals, sequenceBytes, resolved, commands,
        emitted, suffix, offsets, literalWire, literalBound, seqWire⟩

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
  have checked := Internal.checkExtent_iff.mpr ⟨extent, fits⟩
  simp [CompressedBlock.decode, checked, parsed, CompressedBlock.Internal.execute, selected, failed,
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
  have checked := Internal.checkExtent_iff.mpr ⟨extent, fits⟩
  simp [CompressedBlock.decode, checked, parsed, CompressedBlock.Internal.execute, selected, decoded, failed,
    Except.mapError, bind, Except.bind]

end Silmaril.Proofs.Formats.Compression.Zstd.CompressedBlock
