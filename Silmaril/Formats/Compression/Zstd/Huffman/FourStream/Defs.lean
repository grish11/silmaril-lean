module

public import Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Defs

/-! # Zstandard Huffman four-stream extents

RFC 8878 §3.1.1.3.1.6. Input starts at the jump table and contains exactly
the four streams. The optional Huffman tree description precedes this input.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.Huffman.FourStream

structure Limits where
  inputBytes : Nat
  outputSymbols : Nat
  deriving DecidableEq, Repr

structure Chunk where
  bytes : List UInt8
  symbols : Nat
  deriving DecidableEq, Repr

structure Split where
  first : Chunk
  second : Chunk
  third : Chunk
  fourth : Chunk
  deriving DecidableEq, Repr

def Split.chunks (parts : Split) : List Chunk :=
  [parts.first, parts.second, parts.third, parts.fourth]

inductive Error where
  | inputLimit
  | outputLimit
  | sizeMismatch
  | shortJumpTable
  | invalidRegeneratedSize
  | emptyStream
  | invalidStreamExtent
  | table (reason : SingleStream.Error)
  | stream (index : Nat) (reason : SingleStream.Error)
  deriving DecidableEq, Repr

def le16 (low high : UInt8) : Nat := low.toNat + 256 * high.toNat

def segmentSize (regenerated : Nat) : Nat := (regenerated + 3) / 4

/-- The three jump fields describe wire bytes. The fourth extent is the
    exact suffix after those bytes, and each stream has room for a marker. -/
def ExtentsWire (declared : Nat) (input : List UInt8) (parts : Split) : Prop :=
  ∃ a0 a1 b0 b1 c0 c1 : UInt8,
    input = a0 :: a1 :: b0 :: b1 :: c0 :: c1 ::
      (parts.first.bytes ++ parts.second.bytes ++ parts.third.bytes ++ parts.fourth.bytes) ∧
    parts.first.bytes.length = le16 a0 a1 ∧ parts.second.bytes.length = le16 b0 b1 ∧
    parts.third.bytes.length = le16 c0 c1 ∧
    parts.fourth.bytes.length = declared - (6 + le16 a0 a1 + le16 b0 b1 + le16 c0 c1) ∧
    ∀ chunk ∈ parts.chunks, 0 < chunk.bytes.length

def CountsWire (regenerated : Nat) (parts : Split) : Prop :=
  let segment := segmentSize regenerated
  6 ≤ regenerated ∧ 3 * segment ≤ regenerated ∧
    parts.first.symbols = segment ∧ parts.second.symbols = segment ∧ parts.third.symbols = segment ∧
    parts.fourth.symbols = regenerated - 3 * segment

/-- Check the declared extent and caller caps before slicing. The six-symbol
    minimum follows the four-stream literals policy in pinned libzstd.
    A fourth stream with zero symbols still needs an end marker. -/
def split (limits : Limits) (declared regenerated : Nat) (input : List UInt8) : Except Error Split :=
  if limits.inputBytes < declared then .error .inputLimit
  else if input.drop declared ≠ [] then .error .sizeMismatch
  else if input.length ≠ declared then .error .sizeMismatch
  else if limits.outputSymbols < regenerated then .error .outputLimit
  else if regenerated < 6 then .error .invalidRegeneratedSize
  else match input with
    | a0 :: a1 :: b0 :: b1 :: c0 :: c1 :: body =>
      let first := le16 a0 a1
      let second := le16 b0 b1
      let third := le16 c0 c1
      if first = 0 ∨ second = 0 ∨ third = 0 then .error .emptyStream
      else if declared ≤ 6 + first + second + third then .error .invalidStreamExtent
      else
        let (bytes1, tail1) := body.splitAt first
        let (bytes2, tail2) := tail1.splitAt second
        let (bytes3, bytes4) := tail2.splitAt third
        let count := segmentSize regenerated
        .ok ⟨⟨bytes1, count⟩, ⟨bytes2, count⟩, ⟨bytes3, count⟩,
          ⟨bytes4, regenerated - 3 * count⟩⟩
    | _ => .error .shortJumpTable

def ChunkWire (table : SingleStream.Table) (chunk : Chunk) (out : List UInt8) : Prop :=
  out.length = chunk.symbols ∧ ∃ cursor, ReverseBits.StartWire chunk.bytes cursor ∧
    SingleStream.StreamWire table.entries cursor.bits out

inductive ChunksWire (table : SingleStream.Table) : List Chunk → List (List UInt8) → Prop where
  | done : ChunksWire table [] []
  | cons {chunk : Chunk} {chunks : List Chunk} {out : List UInt8} {suffix : List (List UInt8)} :
      ChunkWire table chunk out → ChunksWire table chunks suffix →
      ChunksWire table (chunk :: chunks) (out :: suffix)

namespace Internal

def decodeChunks (table : SingleStream.Table) : Nat → List Chunk → Except Error (List (List UInt8))
  | _, [] => .ok []
  | index, chunk :: chunks => do
    let out ← (SingleStream.Internal.readStream table chunk.symbols chunk.bytes).mapError (Error.stream index)
    let suffix ← decodeChunks table (index + 1) chunks
    return out :: suffix

end Internal

/-- Decode four exact streams using a single table built from direct-profile
    weights. The jump-table splitter is independent of the tree profile. -/
def decode (limits : Limits) (treeLimits : DirectWeights.Limits) (tree : DirectWeights.Tree)
    (declared regenerated : Nat) (input : List UInt8) : Except Error (List UInt8) := do
  let parts ← split limits declared regenerated input
  let table ← (SingleStream.build treeLimits tree).mapError Error.table
  let chunks ← Internal.decodeChunks table 1 parts.chunks
  return chunks.flatten

end Silmaril.Formats.Compression.Zstd.Huffman.FourStream
