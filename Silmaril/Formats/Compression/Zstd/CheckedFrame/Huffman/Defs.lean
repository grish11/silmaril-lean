module

public import Silmaril.Formats.Compression.Zstd.CheckedFrame.Sequences.Defs
public import Silmaril.Formats.Compression.Zstd.CompressedBlock.Huffman.Defs

/-! # Exact dictionary-free Zstandard frames with Huffman literals

RFC 8878 §§3.1.1–3.1.1.5. One standard frame carries Huffman tables,
sequence tables, repeat offsets and rolling history across its blocks.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.CheckedFrame.Huffman

open Silmaril.Formats.Compression.Zstd.Huffman
open CompressedBlock.Huffman (State)
open Sequences (blockLimits)

structure Limits where
  frame : CheckedFrame.Limits
  commandsPerBlock : Nat
  tree : TreeDescription.Limits

inductive Error where
  | frame (reason : CheckedFrame.Error)
  | skippableFrame
  | compressed (reason : CompressedBlock.Huffman.Error)
  deriving DecidableEq, Repr

structure BlockResult (profile : TreeDescription.Limits) where
  last : Bool
  bytes : List UInt8
  rest : List UInt8
  next : State profile

/-- Physical raw and RLE blocks only add their output to rolling history. -/
def advancePlain {profile : TreeDescription.Limits} (prior : State profile)
    (window : Nat) (out : List UInt8) : State profile :=
  { prior with block := prior.block.advancePlain window out }

inductive BlockWire {profile : TreeDescription.Limits} (header : Header) (commands remaining : Nat)
    (prior : State profile) : List UInt8 → BlockResult profile → Prop where
  | plain {first second third : UInt8} {body out rest : List UInt8} {last : Bool} :
      (BlockHeader.ofBytes first second third).kind ≠ 2 →
      CheckedFrame.BlockWire header (first :: second :: third :: body) last out rest →
      out.length ≤ remaining →
      BlockWire header commands remaining prior (first :: second :: third :: body)
        ⟨last, out, rest, advancePlain prior header.windowSize out⟩
  | compressed {first second third : UInt8} {body rest : List UInt8}
      {decoded : CompressedBlock.Huffman.Result profile} :
      (BlockHeader.ofBytes first second third).kind = 2 →
      body.length = (BlockHeader.ofBytes first second third).size →
      body.length ≤ blockMaximum header →
      decoded.bytes.length ≤ min remaining (blockMaximum header) →
      CompressedBlock.Huffman.BlockWire (blockLimits header commands remaining) prior body decoded →
      BlockWire header commands remaining prior (first :: second :: third :: (body ++ rest))
        ⟨(BlockHeader.ofBytes first second third).last, decoded.bytes, rest, decoded.next⟩

/-- Each step starts at the original block suffix and passes the accepted
    successor state and residual output budget to the next block. -/
inductive BlocksWire {profile : TreeDescription.Limits} (header : Header) (commands : Nat) :
    Nat → State profile → List UInt8 → List (List UInt8) → List UInt8 → State profile → Prop where
  | last {remaining : Nat} {prior : State profile} {input : List UInt8} {result : BlockResult profile} :
      BlockWire header commands remaining prior input result → result.last = true →
      BlocksWire header commands remaining prior input [result.bytes] result.rest result.next
  | next {remaining : Nat} {prior final : State profile} {input trailer : List UInt8}
      {chunks : List (List UInt8)} {result : BlockResult profile} :
      BlockWire header commands remaining prior input result → result.last = false →
      BlocksWire header commands (remaining - result.bytes.length) result.next result.rest chunks trailer final →
      BlocksWire header commands remaining prior input (result.bytes :: chunks) trailer final

/-- The original header and block chain, the output in wire order, and the
    exact trailer verified against that output. -/
def FrameWire (limits : Limits) (input output : List UInt8) (header : Header) : Prop :=
  ∃ frameData blocks chunks trailer final,
    input = magic ++ frameData ∧ parseHeader frameData = some (header, blocks) ∧
    header.dictionaryId = 0 ∧
    BlocksWire header limits.commandsPerBlock limits.frame.output
      (State.initial limits.tree) blocks chunks trailer final ∧
    final.block.Valid header.windowSize ∧ chunks.flatten = output ∧
    (∀ n, header.contentSize = some n → output.length = n) ∧
    trailer = (if header.checksum then contentChecksum output else [])

namespace Internal

def envelopeError (input : List UInt8) : CheckedFrame.Error → Error
  | .badMagic => if Sequences.Internal.isSkippable input then .skippableFrame else .frame .badMagic
  | reason => .frame reason

def readPlain {profile : TreeDescription.Limits} (header : Header) (remaining : Nat)
    (prior : State profile) (input : List UInt8) : Except Error (BlockResult profile) := do
  let (last, out, rest) ← (CheckedFrame.Internal.readBlock header remaining input).mapError Error.frame
  return ⟨last, out, rest, advancePlain prior header.windowSize out⟩

def readBlock {profile : TreeDescription.Limits} (header : Header) (commands remaining : Nat)
    (prior : State profile) : List UInt8 → Except Error (BlockResult profile)
  | first :: second :: third :: bytes => do
    let block := BlockHeader.ofBytes first second third
    if block.kind = 2 then
      if blockMaximum header < block.size then throw (.frame .blockLimit)
      let (body, rest) ← (CheckedFrame.Internal.takeExact block.size bytes).mapError Error.frame
      let decoded ← (CompressedBlock.Huffman.decode (blockLimits header commands remaining) prior block.size body)
        |>.mapError Error.compressed
      return ⟨block.last, decoded.bytes, rest, decoded.next⟩
    else readPlain header remaining prior (first :: second :: third :: bytes)
  | _ => .error (.frame .truncated)

def readBlocks {profile : TreeDescription.Limits} (header : Header) (commands : Nat) :
    Nat → Nat → State profile → List UInt8 → List (List UInt8) →
      Except Error (List (List UInt8) × List UInt8)
  | 0, _, _, _, _ => .error (.frame .truncated)
  | fuel + 1, remaining, prior, input, acc => do
    let block ← readBlock header commands remaining prior input
    let acc := block.bytes :: acc
    if block.last then return (acc.reverse, block.rest)
    else readBlocks header commands fuel (remaining - block.bytes.length) block.next block.rest acc

end Internal

/-- Decode one complete standard frame with dictionary-free initial state.
    Output becomes available after the declared size and trailer checks. -/
def decode (limits : Limits) (input : List UInt8) : Except Error (List UInt8) := do
  let (size, header, blocks) ←
    (CheckedFrame.Internal.openFrame limits.frame input).mapError (Internal.envelopeError input)
  let (chunks, trailer) ← Internal.readBlocks header limits.commandsPerBlock (size / 3)
    limits.frame.output (State.initial limits.tree) blocks []
  (CheckedFrame.Internal.finish header chunks.flatten trailer).mapError Error.frame

end Silmaril.Formats.Compression.Zstd.CheckedFrame.Huffman
