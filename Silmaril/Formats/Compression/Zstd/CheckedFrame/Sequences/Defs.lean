module

public import Silmaril.Formats.Compression.Zstd.CompressedBlock.Defs

/-! # Checked Zstandard frames with raw/RLE literals and sequence tables

RFC 8878 §§3.1.1–3.1.1.5. This exact single-frame profile carries accepted
sequence tables, repeat offsets and rolling history across blocks.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.CheckedFrame.Sequences

open CompressedBlock (State)

structure Limits where
  frame : CheckedFrame.Limits
  commandsPerBlock : Nat
  deriving DecidableEq, Repr

inductive Error where
  | frame (reason : CheckedFrame.Error)
  | skippableFrame
  | compressed (reason : CompressedBlock.Error)
  deriving DecidableEq, Repr

structure BlockResult where
  last : Bool
  bytes : List UInt8
  rest : List UInt8
  next : State
  deriving DecidableEq, Repr

def blockLimits (header : Header) (commands remaining : Nat) : CompressedBlock.Limits :=
  ⟨header.windowSize, blockMaximum header, remaining, commands⟩

inductive BlockWire (header : Header) (commands remaining : Nat) (prior : State) :
    List UInt8 → BlockResult → Prop where
  | plain {first second third : UInt8} {body out rest : List UInt8} {last : Bool} :
      (BlockHeader.ofBytes first second third).kind ≠ 2 →
      CheckedFrame.BlockWire header (first :: second :: third :: body) last out rest →
      BlockWire header commands remaining prior (first :: second :: third :: body)
        ⟨last, out, rest, prior.advancePlain header.windowSize out⟩
  | compressed {first second third : UInt8} {body rest : List UInt8} {decoded : CompressedBlock.Result} :
      (BlockHeader.ofBytes first second third).kind = 2 →
      body.length = (BlockHeader.ofBytes first second third).size →
      body.length ≤ blockMaximum header → decoded.bytes.length ≤ blockMaximum header →
      CompressedBlock.BlockWire (blockLimits header commands remaining) prior body decoded →
      BlockWire header commands remaining prior (first :: second :: third :: (body ++ rest))
        ⟨(BlockHeader.ofBytes first second third).last, decoded.bytes, rest, decoded.next⟩

/-- Each accepted block hands its successor to the next block and debits
    the frame's remaining output budget. The first last flag ends the chain. -/
inductive BlocksWire (header : Header) (commands : Nat) :
    Nat → State → List UInt8 → List (List UInt8) → List UInt8 → Prop where
  | last {remaining : Nat} {prior : State} {input : List UInt8} {result : BlockResult} :
      BlockWire header commands remaining prior input result → result.last = true →
      BlocksWire header commands remaining prior input [result.bytes] result.rest
  | next {remaining : Nat} {prior : State} {input trailer : List UInt8}
      {chunks : List (List UInt8)} {result : BlockResult} :
      BlockWire header commands remaining prior input result → result.last = false →
      BlocksWire header commands (remaining - result.bytes.length) result.next result.rest chunks trailer →
      BlocksWire header commands remaining prior input (result.bytes :: chunks) trailer

def FrameWire (limits : Limits) (input output : List UInt8) (header : Header) : Prop :=
  ∃ frameData blocks trailer chunks,
    input = magic ++ frameData ∧ parseHeader frameData = some (header, blocks) ∧
    header.dictionaryId = 0 ∧
    BlocksWire header limits.commandsPerBlock limits.frame.output State.initial blocks chunks trailer ∧
    chunks.flatten = output ∧
    (∀ n, header.contentSize = some n → output.length = n) ∧
    trailer = (if header.checksum then contentChecksum output else [])

namespace Internal

def isSkippable : List UInt8 → Bool
  | first :: 0x2a :: 0x4d :: 0x18 :: _ => decide (0x50 ≤ first.toNat ∧ first.toNat ≤ 0x5f)
  | _ => false

def envelopeError (input : List UInt8) : CheckedFrame.Error → Error
  | .badMagic => if isSkippable input then .skippableFrame else .frame .badMagic
  | reason => .frame reason

def readPlain (header : Header) (remaining : Nat) (prior : State) (input : List UInt8) :
    Except Error BlockResult := do
  let (last, out, rest) ← (CheckedFrame.Internal.readBlock header remaining input).mapError Error.frame
  return ⟨last, out, rest, prior.advancePlain header.windowSize out⟩

def readBlock (header : Header) (commands remaining : Nat) (prior : State) :
    List UInt8 → Except Error BlockResult
  | first :: second :: third :: bytes => do
    let block := BlockHeader.ofBytes first second third
    if block.kind = 2 then
      if blockMaximum header < block.size then throw (.frame .blockLimit)
      let (body, rest) ← (CheckedFrame.Internal.takeExact block.size bytes).mapError Error.frame
      let result ← (CompressedBlock.decode (blockLimits header commands remaining) prior block.size body)
        |>.mapError Error.compressed
      return ⟨block.last, result.bytes, rest, result.next⟩
    else readPlain header remaining prior (first :: second :: third :: bytes)
  | _ => .error (.frame .truncated)

def readBlocks (header : Header) (commands : Nat) :
    Nat → Nat → State → List UInt8 → List (List UInt8) →
      Except Error (List (List UInt8) × List UInt8)
  | 0, _, _, _, _ => .error (.frame .truncated)
  | fuel + 1, remaining, prior, input, acc => do
    let block ← readBlock header commands remaining prior input
    let acc := block.bytes :: acc
    if block.last then return (acc.reverse, block.rest)
    else readBlocks header commands fuel (remaining - block.bytes.length) block.next block.rest acc

end Internal

/-- Decode one complete standard frame in this profile. The common envelope
    checks the window, dictionary, content size, checksum and trailer. -/
def decode (limits : Limits) (input : List UInt8) : Except Error (List UInt8) := do
  let (size, header, blocks) ←
    (CheckedFrame.Internal.openFrame limits.frame input).mapError (Internal.envelopeError input)
  let (chunks, trailer) ←
    Internal.readBlocks header limits.commandsPerBlock (size / 3) limits.frame.output State.initial blocks []
  (CheckedFrame.Internal.finish header chunks.flatten trailer).mapError Error.frame

end Silmaril.Formats.Compression.Zstd.CheckedFrame.Sequences
