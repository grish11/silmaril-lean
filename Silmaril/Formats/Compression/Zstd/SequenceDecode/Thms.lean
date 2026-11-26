module

public import Silmaril.Formats.Compression.Zstd.SequenceDecode.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.SequenceDecode.Contracts

public section

namespace Silmaril.Formats.Compression.Zstd.SequenceDecode

/-- The exact resolved suffix has the RFC end marker and ordered initial
    states. Every command accounts for its symbols and extra bits. Updates
    occur only between commands, with all accessed and next states in range.
    The final command exhausts the stream. -/
theorem readResolved_sound {input : List UInt8} {resolvedSection : SequenceTables.Section} {commands : List Sequence.Command}
    (wire : SequenceTables.SectionWire input resolvedSection)
    (success : Internal.readResolved resolvedSection = .ok commands) :
    PayloadWire resolvedSection commands :=
  Proofs.Formats.Compression.Zstd.SequenceDecode.readResolved_sound wire success

/-- An exact section decodes to precisely its declared number of commands,
    satisfying the caller's limits and the complete prefix and payload relations. -/
theorem decode_sound {limits : SequenceTables.Limits} {input : List UInt8} {commands : List Sequence.Command}
    (success : decode limits input = .ok commands) :
    input.length ≤ limits.inputBytes ∧ commands.length ≤ limits.sequences ∧
      ∃ resolvedSection, SequenceTables.SectionWire input resolvedSection ∧ PayloadWire resolvedSection commands ∧
        commands.length = resolvedSection.count :=
  Proofs.Formats.Compression.Zstd.SequenceDecode.decode_sound success

end Silmaril.Formats.Compression.Zstd.SequenceDecode
