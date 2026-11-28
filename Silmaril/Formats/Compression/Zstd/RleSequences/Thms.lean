module

public import Silmaril.Formats.Compression.Zstd.RleSequences.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.RleSequences.Contracts

public section

namespace Silmaril.Formats.Compression.Zstd.RleSequences

/-- The command fields use the wire order and the three RFC bases and widths. -/
theorem readCommand_sound {codes : Codes} {cursor rest : ReverseBits.Cursor} {command : Sequence.Command}
    (success : Internal.readCommand codes cursor = some (command, rest)) :
    ∃ field, cursor.bits = field ++ rest.bits ∧ CommandWire codes field command :=
  Proofs.Formats.Compression.Zstd.RleSequences.readCommand_sound success

/-- With fixed RLE symbols, the entire payload has one fixed field width
    per command. -/
theorem payloadWidth {codes : Codes} {bits : List Bit} {commands : List Sequence.Command}
    (wire : CommandsWire codes bits commands) :
    bits.length = commands.length * (codes.offset.width + codes.matched.width + codes.literals.width) :=
  Proofs.Formats.Compression.Zstd.RleSequences.payloadWidth wire

/-- Successful section decoding accounts for the whole wire, including every
    payload bit, and respects the compressed-input and command-count caps. -/
theorem decode_sound {limits : Limits} {input : List UInt8} {commands : List Sequence.Command}
    (success : decode limits input = .ok commands) :
    SectionWire input commands ∧ input.length ≤ limits.inputCapacity ∧ commands.length ≤ limits.commands :=
  Proofs.Formats.Compression.Zstd.RleSequences.decode_sound success

end Silmaril.Formats.Compression.Zstd.RleSequences
