module

public import Silmaril.Formats.Compression.Zstd.LiteralBlock.Defs

/-! # Bounded single-frame Zstandard profile

RFC 8878 §§3.1.1–3.1.1.3. One standard frame may contain raw, RLE and
literal-only compressed blocks. A checksum, when present, is verified.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.CheckedFrame

structure Limits where
  input : Nat
  output : Nat
  window : Nat
  deriving DecidableEq, Repr

inductive Error where
  | inputLimit
  | outputLimit
  | windowLimit
  | blockLimit
  | badMagic
  | badHeader
  | unsupportedDictionary (id : Nat)
  | reservedBlock
  | truncated
  | literalBlock (reason : LiteralBlock.Error)
  | contentSizeMismatch
  | checksumMismatch
  | trailingInput
  deriving DecidableEq, Repr

structure BlockHeader where
  last : Bool
  kind : Nat
  size : Nat
  deriving DecidableEq, Repr

/-- The 24-bit little-endian block header (RFC 8878 §3.1.1.2). -/
def BlockHeader.ofBytes (first second third : UInt8) : BlockHeader :=
  let bits := Xxh64.leNat [first, second, third]
  ⟨bits % 2 = 1, bits / 2 % 4, bits / 8⟩

/-- Exact wire bytes and decoded meaning for each supported block type. -/
inductive PayloadWire : Nat → Nat → List UInt8 → List UInt8 → Prop where
  | raw (data : List UInt8) : PayloadWire 0 data.length data data
  | rle (count : Nat) (byte : UInt8) : PayloadWire 1 count [byte] (List.replicate count byte)
  | compressed {size : Nat} {body : List UInt8} {literals : LiteralBlock.Literals} :
      body.length = size → LiteralBlock.BlockWire body literals →
        PayloadWire 2 size body literals.expand

/-- One block consumes three header bytes and just its body. In RLE blocks the
    header size is the regenerated length, and the body is exactly one byte. -/
def BlockWire (header : Header) (input : List UInt8) (last : Bool)
    (out rest : List UInt8) : Prop :=
  ∃ (first second third : UInt8) (body : List UInt8),
    let block := BlockHeader.ofBytes first second third
    input = first :: second :: third :: (body ++ rest) ∧
      last = block.last ∧ block.size ≤ blockMaximum header ∧
      out.length ≤ blockMaximum header ∧ PayloadWire block.kind block.size body out

/-- A nonempty block sequence stops at the first block marked last. -/
inductive BlocksWire (header : Header) : List UInt8 → List (List UInt8) → List UInt8 → Prop where
  | last {input out rest : List UInt8} :
      BlockWire header input true out rest → BlocksWire header input [out] rest
  | next {input out rest tail : List UInt8} {chunks : List (List UInt8)} :
      BlockWire header input false out tail → BlocksWire header tail chunks rest →
        BlocksWire header input (out :: chunks) rest

/-- An exact single standard frame. Header interpretation uses the existing
    RFC 8878 header parser. The trailer is empty or the verified checksum. -/
def FrameWire (input out : List UInt8) (header : Header) : Prop :=
  ∃ frameData blocks trailer chunks,
    input = magic ++ frameData ∧ parseHeader frameData = some (header, blocks) ∧
      header.dictionaryId = 0 ∧ BlocksWire header blocks chunks trailer ∧
      chunks.flatten = out ∧
      (∀ n, header.contentSize = some n → out.length = n) ∧
      trailer = (if header.checksum then contentChecksum out else [])

namespace Internal

def takeExact (size : Nat) (input : List UInt8) : Except Error (List UInt8 × List UInt8) :=
  let (body, rest) := input.splitAt size
  if body.length = size then .ok (body, rest) else .error .truncated

def readBlock (header : Header) (remaining : Nat) :
    List UInt8 → Except Error (Bool × List UInt8 × List UInt8)
  | first :: second :: third :: bytes => do
    let block := BlockHeader.ofBytes first second third
    if blockMaximum header < block.size then throw .blockLimit
    if block.kind = 3 then throw .reservedBlock
    if block.kind = 2 then
      let (body, rest) ← takeExact block.size bytes
      let out ← (LiteralBlock.decode header remaining body).mapError Error.literalBlock
      return (block.last, out, rest)
    else if remaining < block.size then throw .outputLimit
    else if block.kind = 0 then
      let (out, rest) ← takeExact block.size bytes
      return (block.last, out, rest)
    else
      match bytes with
      | byte :: rest => .ok (block.last, List.replicate block.size byte, rest)
      | [] => .error .truncated
  | _ => .error .truncated

/-- Fuel counts block headers. The accumulator stores decoded chunks in reverse
    wire order, so advancing does not copy the already decoded prefix. -/
def readBlocks (header : Header) :
    Nat → Nat → List UInt8 → List (List UInt8) → Except Error (List (List UInt8) × List UInt8)
  | 0, _, _, _ => .error .truncated
  | fuel + 1, remaining, input, acc => do
    let (last, out, rest) ← readBlock header remaining input
    let acc := out :: acc
    if last then .ok (acc.reverse, rest)
    else readBlocks header fuel (remaining - out.length) rest acc

def finish (header : Header) (out trailer : List UInt8) : Except Error (List UInt8) := do
  if header.contentSize.any (· ≠ out.length) then throw .contentSizeMismatch
  if header.checksum then
    let (checksum, rest) ← takeExact 4 trailer
    if checksum ≠ contentChecksum out then throw .checksumMismatch
    if !rest.isEmpty then throw .trailingInput
    return out
  else
    if !trailer.isEmpty then throw .trailingInput
    return out

end Internal

/-- Decode exactly one standard frame. Frame and window limits are checked before
    block decoding. Each block receives only the remaining output budget. -/
def decode (limits : Limits) (input : List UInt8) : Except Error (List UInt8) := do
  let size := input.length
  if limits.input < size then throw .inputLimit
  let (signature, frameData) ← Internal.takeExact 4 input
  if signature ≠ magic then throw .badMagic
  let some (header, blocks) := parseHeader frameData | throw .badHeader
  if header.dictionaryId ≠ 0 then throw (.unsupportedDictionary header.dictionaryId)
  if limits.window < header.windowSize then throw .windowLimit
  let (chunks, trailer) ← Internal.readBlocks header (size / 3) limits.output blocks []
  Internal.finish header chunks.flatten trailer

end Silmaril.Formats.Compression.Zstd.CheckedFrame
