module

public import Silmaril.Formats.Compression.Zstd.Sequence.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.Sequence.Contracts

/-! # Soundness of Zstandard sequence execution -/

public section

namespace Silmaril.Formats.Compression.Zstd.Sequence

/-- A decoded offset value follows the RFC repeat-offset transition. -/
theorem resolve_sound {offsets next : RepeatOffsets} {literalLength value distance : Nat}
    (success : resolve offsets literalLength value = some (distance, next)) :
    OffsetWire offsets literalLength value distance next :=
  Proofs.Formats.Compression.Zstd.Sequence.resolve_sound success

/-- The actual array copy extends history by exactly the requested number of
    bytes, reading prior history at the checked distance on every step. -/
theorem copy_sound {distance : Nat} (positive : 0 < distance) (count : Nat)
    (data : Array UInt8) (available : distance ≤ data.size) :
    ∃ bytes, (Internal.copy distance positive count data available).toList = data.toList ++ bytes ∧
      bytes.length = count ∧ MatchWire distance data.toList bytes :=
  Proofs.Formats.Compression.Zstd.Sequence.copy_sound positive count data available

/-- Interpret the block output as the command denotation followed by the exact
    unused literal suffix. This also records the output and history bounds. -/
theorem execute_sound {limits : Limits} {history : Array UInt8} {literals : List UInt8}
    {offsets : RepeatOffsets} {commands : List Command} {result : Result}
    (success : execute limits history literals offsets commands = .ok result) :
    ∃ emitted suffix, Runs limits.window commands history.toList literals offsets emitted suffix result.offsets ∧
      suffix = literals.drop (commands.map Command.literalLength).sum ∧
      literals.length = (commands.map Command.literalLength).sum + suffix.length ∧
      result.bytes = emitted ++ suffix ∧
      result.bytes.length = (commands.map Command.outputLength).sum + suffix.length ∧
      result.bytes.length ≤ limits.capacity ∧ history.size ≤ limits.window ∧ result.offsets.Valid :=
  Proofs.Formats.Compression.Zstd.Sequence.execute_sound success

end Silmaril.Formats.Compression.Zstd.Sequence
