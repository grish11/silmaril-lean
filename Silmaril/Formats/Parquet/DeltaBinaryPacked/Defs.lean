module

public import Silmaril.Formats.Parquet.Hybrid.Defs
public import Silmaril.Formats.ThriftCompact.Defs

/-! Bounded DELTA_BINARY_PACKED over an exact scalar slice. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.DeltaBinaryPacked

inductive Physical where
  | int32 | int64
  deriving DecidableEq, Repr

def Physical.bits : Physical → Nat
  | .int32 => 32
  | .int64 => 64

abbrev Physical.Value : Physical → Type
  | .int32 => Int32
  | .int64 => Int64

def Physical.ofInt : (physical : Physical) → Int → physical.Value
  | .int32 => Int32.ofInt
  | .int64 => Int64.ofInt

def Physical.toInt : (physical : Physical) → physical.Value → Int
  | .int32 => Int32.toInt
  | .int64 => Int64.toInt

/-- Adding in the signed representative and narrowing gives two's-complement wrap. -/
def Physical.step (physical : Physical) (previous : physical.Value) (delta : Int) : physical.Value :=
  physical.ofInt (physical.toInt previous + delta)

structure Limits where
  bytes : Nat
  values : Nat
  blockValues : Nat
  miniblocksPerBlock : Nat
  blocks : Nat
  deriving DecidableEq, Repr

structure Header where
  blockSize : Nat
  miniblockCount : Nat
  totalCount : Nat
  firstCode : Nat
  deriving DecidableEq, Repr

def Header.miniblockSize (header : Header) : Nat := header.blockSize / header.miniblockCount

def Header.first (header : Header) : Int := ThriftCompact.unzigzag header.firstCode

def Header.wire (header : Header) : List UInt8 :=
  Hybrid.uleb header.blockSize ++ Hybrid.uleb header.miniblockCount ++
    Hybrid.uleb header.totalCount ++ Hybrid.uleb header.firstCode

structure Miniblock where
  width : UInt8
  payload : List UInt8
  deriving DecidableEq, Repr

structure Block where
  minimumCode : Nat
  /-- Logical deltas in the block, before padding. -/
  count : Nat
  miniblocks : List Miniblock
  /-- Raw width bytes for absent miniblocks of the final block. -/
  unusedWidths : List UInt8
  deriving DecidableEq, Repr

def Block.minimum (block : Block) : Int := ThriftCompact.unzigzag block.minimumCode

def Block.wire (block : Block) : List UInt8 :=
  Hybrid.uleb block.minimumCode ++ block.miniblocks.map Miniblock.width ++ block.unusedWidths ++
    block.miniblocks.flatMap Miniblock.payload

structure Stream where
  header : Header
  blocks : List Block
  deriving DecidableEq, Repr

def Stream.wire (stream : Stream) : List UInt8 :=
  stream.header.wire ++ stream.blocks.flatMap Block.wire

/-- The active miniblocks cover the logical deltas in order. -/
inductive MiniblocksFit (physical : Physical) (size : Nat) : Nat → List Miniblock → Prop where
  | done : MiniblocksFit physical size 0 []
  | use {remaining : Nat} {mini : Miniblock} {rest : List Miniblock}
      (positive : 0 < remaining) (width : mini.width.toNat ≤ physical.bits)
      (extent : mini.payload.length = (size / 8) * mini.width.toNat)
      (tail : MiniblocksFit physical size (remaining - size) rest) :
      MiniblocksFit physical size remaining (mini :: rest)

/-- Blocks cover all deltas, with unused width bytes only after the active miniblocks. -/
inductive BlocksFit (physical : Physical) (header : Header) : Nat → List Block → Prop where
  | done : BlocksFit physical header 0 []
  | use {remaining : Nat} {block : Block} {rest : List Block}
      (positive : 0 < remaining) (count : block.count = min remaining header.blockSize)
      (minimum : block.minimumCode < 2 ^ physical.bits)
      (widthTable : block.miniblocks.length + block.unusedWidths.length = header.miniblockCount)
      (miniblocks : MiniblocksFit physical header.miniblockSize block.count block.miniblocks)
      (tail : BlocksFit physical header (remaining - block.count) rest) :
      BlocksFit physical header remaining (block :: rest)

/-- The checked geometry and caller limits for the three unsigned header fields. -/
def Header.Valid (header : Header) (limits : Limits) (expected : Nat) : Prop :=
  header.totalCount = expected ∧ 0 < header.blockSize ∧ header.blockSize % 128 = 0 ∧
    0 < header.miniblockCount ∧ header.blockSize % header.miniblockCount = 0 ∧
    32 ≤ header.miniblockSize ∧ header.miniblockSize % 32 = 0 ∧
    header.blockSize ≤ limits.blockValues ∧ header.miniblockCount ≤ limits.miniblocksPerBlock

def Header.CodesFit (header : Header) (physical : Physical) : Prop :=
  header.blockSize < 2 ^ 31 ∧ header.miniblockCount < 2 ^ 31 ∧
    header.totalCount < 2 ^ 31 ∧ header.firstCode < 2 ^ physical.bits

structure Stream.Valid (stream : Stream) (physical : Physical) (limits : Limits)
    (expected : Nat) : Prop where
  valueLimit : expected ≤ limits.values
  geometry : stream.header.Valid limits expected
  codes : stream.header.CodesFit physical
  layout : BlocksFit physical stream.header (stream.header.totalCount - 1) stream.blocks
  blockLimit : stream.blocks.length ≤ limits.blocks

inductive Error where
  | byteLimit
  | valueLimit
  | geometryLimit
  | blockLimit
  | countMismatch
  | invalidGeometry
  | invalidWidth
  | trailingBytes
  | wire (error : Hybrid.Error)
  deriving DecidableEq, Repr

namespace Internal

def readUnsigned (bits : Nat) (input : List UInt8) : Except Error (Nat × List UInt8) := do
  let (value, rest) ← (Hybrid.readULEB ((bits + 6) / 7) input).mapError Error.wire
  if value < 2 ^ bits then .ok (value, rest) else .error (.wire .headerOverflow)

def readHeader (physical : Physical) (input : List UInt8) : Except Error (Header × List UInt8) := do
  let (blockSize, input) ← readUnsigned 31 input
  let (miniblockCount, input) ← readUnsigned 31 input
  let (totalCount, input) ← readUnsigned 31 input
  let (first, input) ← readUnsigned physical.bits input
  pure (⟨blockSize, miniblockCount, totalCount, first⟩, input)

def validateHeader (limits : Limits) (expected : Nat) (header : Header) : Except Error Unit :=
  if header.totalCount ≠ expected then .error .countMismatch
  else if limits.blockValues < header.blockSize ∨ limits.miniblocksPerBlock < header.miniblockCount then
    .error .geometryLimit
  else if header.blockSize = 0 ∨ header.blockSize % 128 ≠ 0 ∨ header.miniblockCount = 0 ∨
      header.blockSize % header.miniblockCount ≠ 0 ∨ header.miniblockSize < 32 ∨
      header.miniblockSize % 32 ≠ 0 then .error .invalidGeometry
  else .ok ()

/-- After the last logical delta, preserve the remaining widths without
inspecting them or consuming any more payload bytes. -/
def readMiniblocks (physical : Physical) (size : Nat) : List UInt8 → Nat → List UInt8 →
    Except Error (List Miniblock × List UInt8 × List UInt8)
  | widths, 0, input => .ok ([], widths, input)
  | [], _ + 1, _ => .error .countMismatch
  | width :: widths, remaining + 1, input =>
    if physical.bits < width.toNat then .error .invalidWidth
    else do
      let (payload, rest) ← (Hybrid.takeExact ((size / 8) * width.toNat) input).mapError Error.wire
      let (minis, unused, rest) ← readMiniblocks physical size widths (remaining + 1 - size) rest
      pure (⟨width, payload⟩ :: minis, unused, rest)

def readBlock (physical : Physical) (header : Header) (count : Nat) (input : List UInt8) :
    Except Error (Block × List UInt8) := do
  let (minimum, input) ← readUnsigned physical.bits input
  let (widths, input) ← (Hybrid.takeExact header.miniblockCount input).mapError Error.wire
  let (minis, unused, rest) ← readMiniblocks physical header.miniblockSize widths count input
  pure (⟨minimum, count, minis, unused⟩, rest)

def readBlocks (physical : Physical) (header : Header) :
    Nat → Nat → List UInt8 → List Block → Except Error (List Block × List UInt8)
  | _, 0, rest, reversed => .ok (reversed.reverse, rest)
  | 0, _ + 1, _, _ => .error .blockLimit
  | fuel + 1, remaining + 1, input, reversed => do
    let count := min (remaining + 1) header.blockSize
    let (block, rest) ← readBlock physical header count input
    readBlocks physical header fuel (remaining + 1 - count) rest (block :: reversed)

end Internal

/-- Read one delta stream prefix. The byte cap applies to the entire input,
including the untouched suffix returned on success. -/
def parsePrefix (physical : Physical) (limits : Limits) (expected : Nat) (source : Bytes) :
    Except Error (Stream × List UInt8) :=
  if limits.bytes < source.length then .error .byteLimit
  else if limits.values < expected then .error .valueLimit
  else do
    let (header, input) ← Internal.readHeader physical source.toList
    Internal.validateHeader limits expected header
    let (blocks, rest) ← Internal.readBlocks physical header limits.blocks (header.totalCount - 1)
      input []
    pure (⟨header, blocks⟩, rest)

/-- Read one exact delta stream, rejecting all bytes beyond its final block. -/
def parse (physical : Physical) (limits : Limits) (expected : Nat) (source : Bytes) :
    Except Error Stream := do
  let (stream, rest) ← parsePrefix physical limits expected source
  match rest with
  | [] => .ok stream
  | _ :: _ => .error .trailingBytes

def Miniblock.residuals (size : Nat) (mini : Miniblock) : List Nat :=
  Hybrid.unpackGroups mini.width.toNat (size / 8) mini.payload []

def Block.deltas (size : Nat) (block : Block) : List Int :=
  ((block.miniblocks.flatMap (Miniblock.residuals size)).take block.count).map
    (fun residual : Nat => block.minimum + (residual : Int))

def Stream.deltas (stream : Stream) : List Int :=
  stream.blocks.flatMap (Block.deltas stream.header.miniblockSize)

def Stream.reconstruct (stream : Stream) (physical : Physical) : List physical.Value :=
  if stream.header.totalCount = 0 then []
  else stream.deltas.scanl physical.step (physical.ofInt stream.header.first)

def decode (physical : Physical) (limits : Limits) (expected : Nat) (source : Bytes) :
    Except Error (List physical.Value) :=
  (parse physical limits expected source).map (·.reconstruct physical)

end Silmaril.Formats.Parquet.DeltaBinaryPacked
