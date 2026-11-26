module

public import Silmaril.Formats.Compression.Zstd.CompressedBlock.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.CompressedBlock.Contracts
import Silmaril.Formats.Compression.Zstd.SequenceTables.Repeat.Thms
import Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle.Thms

public section

namespace Silmaril.Formats.Compression.Zstd.CompressedBlock

namespace Internal

theorem checkExtent_iff {limits : Limits} {declaredSize : Nat} {body : List UInt8} :
    checkExtent limits declaredSize body = .ok () ↔
      body.length = declaredSize ∧ declaredSize ≤ limits.inputCapacity :=
  Proofs.Formats.Compression.Zstd.CompressedBlock.Internal.checkExtent_iff

theorem execute_sound {limits : Limits} {prior : State} {literals : LiteralBlock.Literals}
    {sequenceBytes : List UInt8} {result : Result} (accepted : prior.tables.Valid)
    (success : execute limits prior literals sequenceBytes = .ok result) :
    result.bytes.length ≤ limits.execution.capacity ∧ result.next.Valid limits.window ∧
      SequenceWire limits prior literals sequenceBytes result :=
  Proofs.Formats.Compression.Zstd.CompressedBlock.Internal.execute_sound accepted success

end Internal

theorem initial_valid (window : Nat) : State.initial.Valid window :=
  ⟨SequenceTables.Repeat.empty_valid, Nat.zero_le _, by decide⟩

/-- Accepted raw/RLE output rotates the window without changing either
    the sequence tables or the repeat offsets. -/
theorem advancePlain_sound (state : State) (window : Nat) (bytes : List UInt8) :
    let next := state.advancePlain window bytes
    next.tables = state.tables ∧ next.history.offsets = state.history.offsets ∧
      next.history.recent.toList =
        (state.history.recent.toList ++ bytes).drop ((state.history.recent.toList ++ bytes).length - window) ∧
      next.history.recent.size ≤ window :=
  let ⟨suffix, within, offsets⟩ := CheckedFrame.Rle.advance_sound state.history window bytes state.history.offsets
  ⟨rfl, offsets, suffix, within⟩

/-- Success consumes the declared body and produces the bounded output and
    validated successor state described by the complete block relation. -/
theorem decode_sound {limits : Limits} {prior : State} {declaredSize : Nat}
    {body : List UInt8} {result : Result} (accepted : prior.tables.Valid)
    (success : decode limits prior declaredSize body = .ok result) :
    body.length = declaredSize ∧ declaredSize ≤ limits.inputCapacity ∧
      result.bytes.length ≤ limits.execution.capacity ∧ result.next.Valid limits.window ∧
      BlockWire limits prior body result :=
  Proofs.Formats.Compression.Zstd.CompressedBlock.decode_sound accepted success

/-- A valid table prefix publishes no successor if its reverse stream fails. -/
theorem decode_sequence_failure {limits : Limits} {prior : State} {declaredSize : Nat}
    {body sequenceBytes : List UInt8} {literals : LiteralBlock.Literals}
    {resolvedSection : SequenceTables.Section} {tables : SequenceTables.Repeat.State}
    {reason : SequenceDecode.Error}
    (fits : declaredSize ≤ limits.inputCapacity) (extent : body.length = declaredSize)
    (parsed : LiteralBlock.parseLiterals limits.execution.capacity body = .ok (literals, sequenceBytes))
    (selected : SequenceTables.Repeat.resolve limits.sequences prior.tables sequenceBytes =
      .ok (resolvedSection, tables))
    (failed : SequenceDecode.readResolved resolvedSection = .error reason) :
    decode limits prior declaredSize body = .error (.sequences reason) :=
  Proofs.Formats.Compression.Zstd.CompressedBlock.decode_sequence_failure fits extent parsed selected failed

/-- A decoded sequence list publishes no successor if bounded execution fails. -/
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
    decode limits prior declaredSize body = .error (.execution reason) :=
  Proofs.Formats.Compression.Zstd.CompressedBlock.decode_execution_failure fits extent parsed selected decoded failed

end Silmaril.Formats.Compression.Zstd.CompressedBlock
