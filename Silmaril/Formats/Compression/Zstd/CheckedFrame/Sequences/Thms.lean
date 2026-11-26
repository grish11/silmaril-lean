module

public import Silmaril.Formats.Compression.Zstd.CheckedFrame.Sequences.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.CheckedFrame.Sequences.Contracts

public section

namespace Silmaril.Formats.Compression.Zstd.CheckedFrame.Sequences

open CompressedBlock (State)

/-- An accepted block keeps exactly the last window of history plus output. -/
theorem block_history {header : Header} {commands remaining : Nat} {prior : State}
    {input : List UInt8} {result : BlockResult} (wire : BlockWire header commands remaining prior input result) :
    let joined := prior.history.recent.toList ++ result.bytes
    result.next.history.recent.toList = joined.drop (joined.length - header.windowSize) :=
  Proofs.Formats.Compression.Zstd.CheckedFrame.Sequences.block_history wire

/-- Successful dispatch consumes exactly the block described by its header,
    checks its share of the frame budget and yields a valid successor. -/
theorem readBlock_sound {header : Header} {commands remaining : Nat} {prior : State}
    {input : List UInt8} {result : BlockResult} (valid : prior.Valid header.windowSize)
    (success : Internal.readBlock header commands remaining prior input = .ok result) :
    BlockWire header commands remaining prior input result ∧
      result.bytes.length ≤ remaining ∧ result.next.Valid header.windowSize :=
  Proofs.Formats.Compression.Zstd.CheckedFrame.Sequences.readBlock_sound valid success

/-- The output denotes one entire standard frame, including exact block
    boundaries and the checked content size and trailer. -/
theorem decode_sound {limits : Limits} {input output : List UInt8}
    (success : decode limits input = .ok output) :
    ∃ header, FrameWire limits input output header ∧ input.length ≤ limits.frame.input ∧
      output.length ≤ limits.frame.output ∧ header.windowSize ≤ limits.frame.window :=
  Proofs.Formats.Compression.Zstd.CheckedFrame.Sequences.decode_sound success

end Silmaril.Formats.Compression.Zstd.CheckedFrame.Sequences
