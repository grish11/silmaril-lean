module

public import Silmaril.Formats.Compression.Zstd.CheckedFrame.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.CheckedFrame.Contracts

/-! # Exact framing, checksum and output bounds for the single-frame profile -/

public section

namespace Silmaril.Formats.Compression.Zstd.CheckedFrame

/-- A successful block consumes its exact wire extent and stays within the
    remaining output budget. -/
theorem readBlock_sound {header : Header} {remaining : Nat} {input out rest : List UInt8}
    {last : Bool} (success : Internal.readBlock header remaining input = .ok (last, out, rest)) :
    BlockWire header input last out rest ∧ out.length ≤ remaining :=
  Proofs.Formats.Compression.Zstd.CheckedFrame.readBlock_sound success

/-- The decoded suffix is a sequence ending at its first last block, and its
    combined output fits the budget supplied for that suffix. -/
theorem readBlocks_sound {header : Header} {fuel remaining : Nat} {input rest : List UInt8}
    {acc final : List (List UInt8)}
    (success : Internal.readBlocks header fuel remaining input acc = .ok (final, rest)) :
    ∃ chunks, BlocksWire header input chunks rest ∧
      chunks.flatten.length ≤ remaining ∧ final = acc.reverse ++ chunks :=
  Proofs.Formats.Compression.Zstd.CheckedFrame.readBlocks_sound success

/-- A successful decode consumes one whole frame, verifies any declared content
    size and checksum, and respects all three caller limits. -/
theorem decode_sound {limits : Limits} {input out : List UInt8}
    (success : decode limits input = .ok out) :
    ∃ header, FrameWire input out header ∧ input.length ≤ limits.input ∧
      out.length ≤ limits.output ∧ header.windowSize ≤ limits.window :=
  Proofs.Formats.Compression.Zstd.CheckedFrame.decode_sound success

end Silmaril.Formats.Compression.Zstd.CheckedFrame
