module

public import Silmaril.Formats.Compression.Zstd.CheckedFrame.Huffman.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.CheckedFrame.Huffman.Contracts

public section

namespace Silmaril.Formats.Compression.Zstd.CheckedFrame.Huffman

open Silmaril.Formats.Compression.Zstd.Huffman
open CompressedBlock.Huffman (State)

/-- Physical raw and RLE blocks preserve both tables and the repeat offsets. -/
theorem plain_state {profile : TreeDescription.Limits} {header : Header} {commands remaining : Nat}
    {prior : State profile} {first second third : UInt8} {bytes : List UInt8} {result : BlockResult profile}
    (kind : (BlockHeader.ofBytes first second third).kind ≠ 2)
    (wire : BlockWire header commands remaining prior (first :: second :: third :: bytes) result) :
    result.next.literals = prior.literals ∧ result.next.block.tables = prior.block.tables ∧
      result.next.block.history.offsets = prior.block.history.offsets :=
  Proofs.Formats.Compression.Zstd.CheckedFrame.Huffman.plain_state kind wire

/-- Every accepted block retains the last window of prior history and output. -/
theorem block_history {profile : TreeDescription.Limits} {header : Header} {commands remaining : Nat}
    {prior : State profile} {input : List UInt8} {result : BlockResult profile}
    (wire : BlockWire header commands remaining prior input result) :
    let joined := prior.block.history.recent.toList ++ result.bytes
    result.next.block.history.recent.toList = joined.drop (joined.length - header.windowSize) :=
  Proofs.Formats.Compression.Zstd.CheckedFrame.Huffman.block_history wire

/-- Dispatch consumes the exact block extent, fits its share of the frame
    budget, and hands off the accepted successor. -/
theorem readBlock_sound {profile : TreeDescription.Limits} {header : Header} {commands remaining : Nat}
    {prior : State profile} {input : List UInt8} {result : BlockResult profile}
    (valid : prior.block.Valid header.windowSize)
    (success : Internal.readBlock header commands remaining prior input = .ok result) :
    BlockWire header commands remaining prior input result ∧
      result.bytes.length ≤ remaining ∧ result.next.block.Valid header.windowSize :=
  Proofs.Formats.Compression.Zstd.CheckedFrame.Huffman.readBlock_sound valid success

/-- The block chain preserves wire order and stops at the first last flag. -/
theorem readBlocks_sound {profile : TreeDescription.Limits} {header : Header} {commands fuel remaining : Nat}
    {prior : State profile} {input trailer : List UInt8} {acc returned : List (List UInt8)}
    (valid : prior.block.Valid header.windowSize)
    (success : Internal.readBlocks header commands fuel remaining prior input acc = .ok (returned, trailer)) :
    ∃ chunks final, BlocksWire header commands remaining prior input chunks trailer final ∧
      chunks.flatten.length ≤ remaining ∧ returned = acc.reverse ++ chunks ∧ final.block.Valid header.windowSize :=
  Proofs.Formats.Compression.Zstd.CheckedFrame.Huffman.readBlocks_sound valid success

/-- One complete bounded frame, including the exact stateful block chain,
    optional declared content size and verified checksum trailer. -/
theorem decode_sound {limits : Limits} {input output : List UInt8}
    (success : decode limits input = .ok output) :
    ∃ header, FrameWire limits input output header ∧ input.length ≤ limits.frame.input ∧
      output.length ≤ limits.frame.output ∧ header.windowSize ≤ limits.frame.window :=
  Proofs.Formats.Compression.Zstd.CheckedFrame.Huffman.decode_sound success

end Silmaril.Formats.Compression.Zstd.CheckedFrame.Huffman
