module

public import Silmaril.Formats.Compression.Format.Defs
public import Silmaril.Formats.Compression.Deflate.Decompress
public import Silmaril.Prelude.Bytes.Digits.Defs

/-! # Raw Snappy blocks

The Parquet payload is a uint32 varint length followed by literal and copy tags.
See `docs/projects/parquet-raw-snappy.md` for the wire and API contracts.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Snappy

/-- Largest uncompressed length in the raw wire format. -/
def maxLength : Nat := 4294967295

inductive Malformed where
  | preamble
  | truncatedTag
  | lengthMismatch
  | invalidOffset
  | trailingInput
  deriving DecidableEq, Repr

inductive Unsupported where
  | framedStream
  deriving DecidableEq, Repr

inductive Error where
  | malformed (reason : Malformed)
  | unsupported (feature : Unsupported)
  | limited (declared limit : Nat)
  deriving DecidableEq, Repr

/-- The tag AST forgets the width of a copy offset and the width of a literal length. -/
inductive Tag where
  | literal (bytes : List UInt8)
  | copy (offset length : Nat)
  deriving DecidableEq, Repr

def Tag.size : Tag → Nat
  | .literal bytes => bytes.length
  | .copy _ length => length

def tagsSize (tags : List Tag) : Nat := (tags.map Tag.size).sum

/-- The list denotation of one tag. For a copy the source is recomputed after
    each appended byte, so bytes just produced are eligible as sources. -/
inductive Tag.Denotes (history : List UInt8) : Tag → List UInt8 → Prop where
  | literal (bytes : List UInt8) : Denotes history (.literal bytes) (history ++ bytes)
  | copy {offset : Nat} (length : Nat) (positive : 0 < offset) (within : offset ≤ history.length) :
      Denotes history (.copy offset length) (Deflate.copyBack offset history length)

/-- Interpret the tags against the evolving output. -/
inductive Denotes : List UInt8 → List Tag → List UInt8 → Prop where
  | nil (history : List UInt8) : Denotes history [] history
  | cons {history next out : List UInt8} {tag : Tag} {tags : List Tag} :
      tag.Denotes history next → Denotes next tags out → Denotes history (tag :: tags) out

structure Block where
  length : Nat
  tags : List Tag
  deriving DecidableEq, Repr

namespace Internal

/-- Read the remaining varint digits, with at most `fuel` bytes. At the
    fifth digit only the low four bits are available. -/
def readLength : Nat → List UInt8 → Except Error (Nat × List UInt8)
  | 0, _ | _, [] => .error (.malformed .preamble)
  | fuel + 1, byte :: rest =>
    let digit := byte.toNat
    if fuel = 0 ∧ 16 ≤ digit then .error (.malformed .preamble)
    else if digit < 128 then .ok (digit, rest)
    else do
      let (high, tail) ← readLength fuel rest
      return (digit % 128 + 128 * high, tail)

def takeBytes (count : Nat) (input : List UInt8) : Except Error (List UInt8 × List UInt8) :=
  let (bytes, rest) := input.splitAt count
  if bytes.length = count then .ok (bytes, rest) else .error (.malformed .truncatedTag)

def readLE (count : Nat) (input : List UInt8) : Except Error (Nat × List UInt8) := do
  let (bytes, rest) ← takeBytes count input
  return (KBytes.leVal bytes, rest)

inductive TagHead where
  | literal (length : Nat)
  | copy (offset length : Nat)

def TagHead.size : TagHead → Nat
  | .literal length | .copy _ length => length

/-- Read only the tag and its fixed-width fields. In particular, literal
    bytes are still unread when the caller checks the output budget. -/
def readTagHead : List UInt8 → Except Error (TagHead × List UInt8)
  | [] => .error (.malformed .truncatedTag)
  | byte :: rest =>
    let high := byte.toNat / 4
    match byte.toNat % 4 with
    | 0 => do
      if high < 60 then return (.literal (high + 1), rest)
      let (extra, tail) ← readLE (high - 59) rest
      return (.literal (extra + 1), tail)
    | 1 => do
      let (low, tail) ← readLE 1 rest
      return (.copy (256 * (high / 8) + low) (high % 8 + 4), tail)
    | kind => do
      let (offset, tail) ← readLE (if kind = 2 then 2 else 4) rest
      return (.copy offset (high + 1), tail)

def TagHead.readBody (head : TagHead) (input : List UInt8) :
    Except Error (Tag × List UInt8) :=
  match head with
  | .literal length => do
    let (bytes, rest) ← takeBytes length input
    return (.literal bytes, rest)
  | .copy offset length => .ok (.copy offset length, input)

/-- Fuel bounds the number of tags by the initial uncompressed length.
    The room check precedes reading or allocating a literal payload. -/
def readTags : Nat → Nat → List UInt8 → List Tag → Except Error (List Tag × List UInt8)
  | _, 0, input, rev => .ok (rev.reverse, input)
  | 0, _ + 1, _, _ => .error (.malformed .lengthMismatch)
  | fuel + 1, room + 1, input, rev => do
    let (head, rest) ← readTagHead input
    if room + 1 < head.size then throw (.malformed .lengthMismatch)
    let (tag, tail) ← head.readBody rest
    readTags fuel (room + 1 - head.size) tail (tag :: rev)

def framedMagic : List UInt8 := [0xff, 6, 0, 0, 0x73, 0x4e, 0x61, 0x50, 0x70, 0x59]

def applyTag (out : Array UInt8) : Tag → Except Error (Array UInt8)
  | .literal bytes => .ok (out.appendList bytes)
  | .copy offset length =>
    if 0 < offset ∧ offset ≤ out.size then .ok (Deflate.copyBackArr offset out length)
    else .error (.malformed .invalidOffset)

def expandTags (out : Array UInt8) : List Tag → Except Error (Array UInt8)
  | [] => .ok out
  | tag :: tags => do
    let next ← applyTag out tag
    expandTags next tags

def writeLength : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel + 1, value =>
    if value < 128 then [UInt8.ofNat value]
    else UInt8.ofNat (128 + value % 128) :: writeLength fuel (value / 128)

def writeLiteralHead (minusOne : Nat) : List UInt8 :=
  if minusOne < 60 then [UInt8.ofNat (4 * minusOne)]
  else
    let width := if minusOne < 256 then 1 else if minusOne < 65536 then 2
      else if minusOne < 16777216 then 3 else 4
    UInt8.ofNat (4 * (59 + width)) :: KBytes.unpack width minusOne

end Internal

open Internal

/-- Parse a raw block from the front of the input, leaving the unread suffix.
    Reject the declared size above `limit` before reading tags. -/
def parseMember (limit : Nat) (input : List UInt8) : Except Error (Block × List UInt8) := do
  if input.take framedMagic.length = framedMagic then throw (.unsupported .framedStream)
  let (size, rest) ← readLength 5 input
  if limit < size then throw (.limited size limit)
  let (tags, tail) ← readTags size size rest []
  return (⟨size, tags⟩, tail)

/-- Parse exactly one raw block, as required for a Parquet compressed payload. -/
def parse (limit : Nat) (input : List UInt8) : Except Error Block := do
  let (block, rest) ← parseMember limit input
  if rest.isEmpty then .ok block else .error (.malformed .trailingInput)

/-- Decode exactly one raw block. Expansion uses the checked tag sizes and
    rejects offsets outside the output produced so far. -/
def decode (limit : Nat) (input : List UInt8) : Except Error (List UInt8) := do
  let block ← parse limit input
  let out ← expandTags #[] block.tags
  return out.toList

/-- Decode a raw block at the front of the input and return its unread suffix. -/
def decodeMember (limit : Nat) (input : List UInt8) : Except Error (List UInt8 × List UInt8) := do
  let (block, rest) ← parseMember limit input
  let out ← expandTags #[] block.tags
  return (out.toList, rest)

/-- The prefix adapter for the compression framework. Use `decode` on a
    page slice to enforce exact input consumption. -/
def format : Format where
  Params := Nat
  Error := Error
  decodeE := decodeMember

/-- Emit a canonical uint32 preamble and a single literal for nonempty input.
    The empty block consists only of its length byte. -/
def encode (input : List UInt8) : Except Error (List UInt8) :=
  let size := input.length
  if maxLength < size then .error (.limited size maxLength)
  else
    let preamble := writeLength 5 size
    if size = 0 then .ok preamble else .ok (preamble ++ writeLiteralHead (size - 1) ++ input)

end Silmaril.Formats.Compression.Snappy
