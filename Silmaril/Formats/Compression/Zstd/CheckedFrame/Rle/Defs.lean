module

public import Silmaril.Formats.Compression.Zstd.CheckedFrame.Defs
public import Silmaril.Formats.Compression.Zstd.RleSequences.Defs

/-! # Single-frame Zstandard profile with explicit RLE sequence tables

RFC 8878 §§3.1.1–3.1.1.5. Compressed blocks have raw/RLE literals and
zero sequences or three explicit RLE sequence tables.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle

structure Limits where
  frame : CheckedFrame.Limits
  commandsPerBlock : Nat
  deriving DecidableEq, Repr

inductive Error where
  | frame (reason : CheckedFrame.Error)
  | literals (reason : LiteralBlock.Error)
  | sequences (reason : RleSequences.Error)
  | execution (reason : Sequence.Error)
  deriving DecidableEq, Repr

structure History where
  recent : Array UInt8
  offsets : Sequence.RepeatOffsets
  deriving DecidableEq, Repr

def History.initial : History := ⟨#[], Sequence.RepeatOffsets.initial⟩

/-- Retain the last window of decoded bytes and the latest repeat offsets. -/
def History.advance (history : History) (window : Nat) (out : List UInt8)
    (offsets : Sequence.RepeatOffsets) : History :=
  let joined := history.recent ++ out.toArray
  ⟨joined.extract (joined.size - window) joined.size, offsets⟩

/-- The exact literal and sequence sections, and their execution against the
    incoming history and repeat offsets. -/
def CompressedWire (header : Header) (commandLimit : Nat) (history : History)
    (body out : List UInt8) (offsets : Sequence.RepeatOffsets) : Prop :=
  ∃ literals sequenceBytes commands emitted suffix,
    LiteralBlock.LiteralsWire body literals sequenceBytes ∧
      RleSequences.SectionWire sequenceBytes commands ∧ commands.length ≤ commandLimit ∧
      Sequence.Runs header.windowSize commands history.recent.toList literals.expand
        history.offsets emitted suffix offsets ∧ out = emitted ++ suffix

inductive BlockWire (header : Header) (commandLimit : Nat) (history : History) :
    List UInt8 → Bool → List UInt8 → List UInt8 → Sequence.RepeatOffsets → Prop where
  /-- The existing raw/RLE block relation, including its literal-only
      compressed subset, leaves the repeat state as it was. -/
  | unchanged {input out rest : List UInt8} {last : Bool} :
      CheckedFrame.BlockWire header input last out rest →
      BlockWire header commandLimit history input last out rest history.offsets
  | compressed {first second third : UInt8} {body out rest : List UInt8}
      {offsets : Sequence.RepeatOffsets} :
      (BlockHeader.ofBytes first second third).kind = 2 →
      body.length = (BlockHeader.ofBytes first second third).size →
      body.length ≤ blockMaximum header → out.length ≤ blockMaximum header →
      CompressedWire header commandLimit history body out offsets →
      BlockWire header commandLimit history (first :: second :: third :: (body ++ rest))
        (BlockHeader.ofBytes first second third).last out rest offsets

/-- A block chain carries the retained window and repeat state through each
    nonterminal block, and ends at the first last-block bit. -/
inductive BlocksWire (header : Header) (commandLimit : Nat) :
    History → List UInt8 → List (List UInt8) → List UInt8 → Prop where
  | last {history : History} {input out rest : List UInt8} {offsets : Sequence.RepeatOffsets} :
      BlockWire header commandLimit history input true out rest offsets →
      BlocksWire header commandLimit history input [out] rest
  | next {history : History} {input out tail rest : List UInt8} {chunks : List (List UInt8)}
      {offsets : Sequence.RepeatOffsets} :
      BlockWire header commandLimit history input false out tail offsets →
      BlocksWire header commandLimit (history.advance header.windowSize out offsets) tail chunks rest →
      BlocksWire header commandLimit history input (out :: chunks) rest

def FrameWire (commandLimit : Nat) (input out : List UInt8) (header : Header) : Prop :=
  ∃ frameData blocks trailer chunks,
    input = magic ++ frameData ∧ parseHeader frameData = some (header, blocks) ∧
      header.dictionaryId = 0 ∧ BlocksWire header commandLimit History.initial blocks chunks trailer ∧
      chunks.flatten = out ∧
      (∀ n, header.contentSize = some n → out.length = n) ∧
      trailer = (if header.checksum then contentChecksum out else [])

namespace Internal

def readCompressed (header : Header) (commandLimit remaining : Nat) (history : History)
    (body : List UInt8) : Except Error Sequence.Result := do
  let capacity := min remaining (blockMaximum header)
  let (literals, sections) ← (LiteralBlock.parseLiterals capacity body).mapError Error.literals
  -- Each command emits at least three match bytes.
  let commands ← (RleSequences.decode ⟨body.length, min commandLimit (capacity / 3)⟩ sections)
    |>.mapError Error.sequences
  (Sequence.execute ⟨header.windowSize, remaining⟩ history.recent literals.expand history.offsets commands)
    |>.mapError Error.execution

def readPlain (header : Header) (remaining : Nat) (history : History) (input : List UInt8) :
    Except Error (Bool × List UInt8 × List UInt8 × Sequence.RepeatOffsets) := do
  let (last, out, rest) ← (CheckedFrame.Internal.readBlock header remaining input).mapError Error.frame
  return (last, out, rest, history.offsets)

def readBlock (header : Header) (commandLimit remaining : Nat) (history : History) :
    List UInt8 → Except Error (Bool × List UInt8 × List UInt8 × Sequence.RepeatOffsets)
  | first :: second :: third :: bytes => do
    let block := BlockHeader.ofBytes first second third
    if block.kind = 2 then
      if blockMaximum header < block.size then throw (.frame .blockLimit)
      let (body, rest) ← (CheckedFrame.Internal.takeExact block.size bytes).mapError Error.frame
      let result ← readCompressed header commandLimit remaining history body
      return (block.last, result.bytes, rest, result.offsets)
    else readPlain header remaining history (first :: second :: third :: bytes)
  | _ => .error (.frame .truncated)

def readBlocks (header : Header) (commandLimit : Nat) :
    Nat → Nat → History → List UInt8 → List (List UInt8) →
      Except Error (List (List UInt8) × List UInt8)
  | 0, _, _, _, _ => .error (.frame .truncated)
  | fuel + 1, remaining, history, input, acc => do
    let (last, out, rest, offsets) ← readBlock header commandLimit remaining history input
    let acc := out :: acc
    if last then .ok (acc.reverse, rest)
    else
      readBlocks header commandLimit fuel (remaining - out.length)
        (history.advance header.windowSize out offsets) rest acc

end Internal

/-- Decode one whole frame in the RLE sequence-table profile. Unsupported
    literal and sequence modes fail before the frame yields an output. -/
def decode (limits : Limits) (input : List UInt8) : Except Error (List UInt8) := do
  let (size, header, blocks) ← (CheckedFrame.Internal.openFrame limits.frame input).mapError Error.frame
  let (chunks, trailer) ←
    Internal.readBlocks header limits.commandsPerBlock (size / 3) limits.frame.output History.initial blocks []
  (CheckedFrame.Internal.finish header chunks.flatten trailer).mapError Error.frame

end Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle
