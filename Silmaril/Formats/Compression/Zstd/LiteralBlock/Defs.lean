module

public import Silmaril.Formats.Compression.Zstd.Defs

/-! # Literal-only Zstandard compressed blocks

RFC 8878 §§3.1.1.3.1 and 3.1.1.3.2.1. This profile reads an exact
`Compressed_Block` body with raw or RLE literals and zero sequences.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.LiteralBlock

inductive Unsupported where
  | huffmanLiterals
  | treelessLiterals
  | sequences
  deriving DecidableEq, Repr

inductive Error where
  | truncated
  | blockLimit
  | outputLimit
  | trailingSequences
  | unsupported (feature : Unsupported)
  deriving DecidableEq, Repr

/-- A raw literal string or a byte to repeat. RLE remains compact while parsing. -/
inductive Literals where
  | raw (bytes : List UInt8)
  | rle (count : Nat) (byte : UInt8)
  deriving DecidableEq, Repr

def Literals.size : Literals → Nat
  | .raw bytes => bytes.length
  | .rle n _ => n

def Literals.expand : Literals → List UInt8
  | .raw bytes => bytes
  | .rle n byte => List.replicate n byte

structure Prefix where
  literals : Literals
  consumed : Nat
  rest : List UInt8
  deriving DecidableEq, Repr

inductive BoundedError where
  | inputLimit
  | literals (reason : Error)
  deriving DecidableEq, Repr

/-- The three raw/RLE regenerated-size encodings. The short format covers
    both size-format values 00 and 10, whose high bit belongs to the size. -/
inductive SizeWire : List UInt8 → Nat → Prop where
  | short (first : UInt8) :
      first.toNat / 4 % 2 = 0 → SizeWire [first] (first.toNat / 8)
  | medium (first second : UInt8) :
      first.toNat / 4 % 4 = 1 → SizeWire [first, second] (first.toNat / 16 + 16 * second.toNat)
  | long (first second third : UInt8) :
      first.toNat / 4 % 4 = 3 →
      SizeWire [first, second, third] (first.toNat / 16 + 16 * second.toNat + 4096 * third.toNat)

/-- The literal section covers a prefix of the compressed block. The suffix
    begins at the sequence count. -/
inductive LiteralsWire : List UInt8 → Literals → List UInt8 → Prop where
  | raw {first : UInt8} {headerTail bytes rest : List UInt8} :
      first.toNat % 4 = 0 → SizeWire (first :: headerTail) bytes.length →
      LiteralsWire (first :: (headerTail ++ bytes ++ rest)) (.raw bytes) rest
  | rle {first byte : UInt8} {headerTail rest : List UInt8} {count : Nat} :
      first.toNat % 4 = 1 → SizeWire (first :: headerTail) count →
      LiteralsWire (first :: (headerTail ++ byte :: rest)) (.rle count byte) rest

def Prefix.Wire (result : Prefix) (input : List UInt8) : Prop :=
  LiteralsWire input result.literals result.rest ∧
    ∃ bytes, input = bytes ++ result.rest ∧ bytes.length = result.consumed

/-- The sequence count's one-, two- and three-byte wire forms. -/
inductive SequenceCountWire : List UInt8 → Nat → Prop where
  | short (byte : UInt8) :
      byte.toNat < 128 → SequenceCountWire [byte] byte.toNat
  | medium (first second : UInt8) :
      128 ≤ first.toNat → first.toNat < 255 →
      SequenceCountWire [first, second] (256 * (first.toNat - 128) + second.toNat)
  | long (lo hi : UInt8) :
      SequenceCountWire [255, lo, hi] (32512 + lo.toNat + 256 * hi.toNat)

/-- An exact type-2 block body in the zero-sequence profile. -/
inductive BlockWire : List UInt8 → Literals → Prop where
  | ofSections {input suffix : List UInt8} {literals : Literals} :
      LiteralsWire input literals suffix → SequenceCountWire suffix 0 → BlockWire input literals

namespace Internal

def readSize (first : UInt8) (rest : List UInt8) : Except Error (Nat × List UInt8) :=
  let format := first.toNat / 4 % 4
  if format = 1 then
    match rest with
    | byte :: tail => .ok (first.toNat / 16 + 16 * byte.toNat, tail)
    | [] => .error .truncated
  else if format = 3 then
    match rest with
    | lo :: hi :: tail => .ok (first.toNat / 16 + 16 * lo.toNat + 4096 * hi.toNat, tail)
    | _ => .error .truncated
  else .ok (first.toNat / 8, rest)

def sizeBytes (first : UInt8) : Nat :=
  let format := first.toNat / 4 % 4
  if format = 1 then 2 else if format = 3 then 3 else 1

def readPlain (inputLimit : Option Nat) (outputLimit : Nat) :
    List UInt8 → Except BoundedError Prefix
  | [] => .error (.literals .truncated)
  | first :: tail => do
    let kind := first.toNat % 4
    if kind = 2 then throw (.literals (.unsupported .huffmanLiterals))
    if kind = 3 then throw (.literals (.unsupported .treelessLiterals))
    let (size, body) ← (readSize first tail).mapError .literals
    if outputLimit < size then throw (.literals .outputLimit)
    let consumed := sizeBytes first + if kind = 0 then size else 1
    if inputLimit.any (· < consumed) then throw .inputLimit
    if kind = 0 then
      let (bytes, rest) := body.splitAt size
      if bytes.length = size then .ok ⟨.raw bytes, consumed, rest⟩ else .error (.literals .truncated)
    else
      match body with
      | byte :: rest => .ok ⟨.rle size byte, consumed, rest⟩
      | [] => .error (.literals .truncated)

/-- Check at most the supplied number of bytes and the following constructor. -/
def fitsInput : Nat → List UInt8 → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | n + 1, _ :: rest => fitsInput n rest

end Internal

/-- Read raw or RLE literals without expanding a run. Check the regenerated
    size before splitting a raw body. -/
def parseLiterals (outputLimit : Nat) (input : List UInt8) : Except Error (Literals × List UInt8) :=
  ((Internal.readPlain none outputLimit input).map fun result => (result.literals, result.rest)).mapError
    (fun | .literals reason => reason | .inputLimit => .truncated)

/-- Check the entire raw or RLE section extent before copying its payload. -/
def parseLiteralsBounded (inputLimit outputLimit : Nat) (input : List UInt8) : Except BoundedError Prefix :=
  Internal.readPlain (some inputLimit) outputLimit input

/-- Read the sequence count, leaving any modes, tables or bitstream untouched. -/
def readSequenceCount : List UInt8 → Except Error (Nat × List UInt8)
  | [] => .error .truncated
  | first :: tail =>
    if first.toNat < 128 then .ok (first.toNat, tail)
    else if first.toNat = 255 then
      match tail with
      | lo :: hi :: rest => .ok (32512 + lo.toNat + 256 * hi.toNat, rest)
      | _ => .error .truncated
    else
      match tail with
      | byte :: rest => .ok (256 * (first.toNat - 128) + byte.toNat, rest)
      | [] => .error .truncated

/-- Decode the exact type-2 block body. Its compressed extent and regenerated
    size must fit the frame's block maximum. The caller supplies an additional
    output limit, checked before expanding any run. -/
def decode (header : Header) (outputLimit : Nat) (input : List UInt8) : Except Error (List UInt8) :=
  if !Internal.fitsInput (blockMaximum header) input then .error .blockLimit
  else do
    let (literals, sequences) ← parseLiterals (min (blockMaximum header) outputLimit) input
    let (count, rest) ← readSequenceCount sequences
    if count ≠ 0 then .error (.unsupported .sequences)
    else if rest.isEmpty then .ok literals.expand
    else .error .trailingSequences

end Silmaril.Formats.Compression.Zstd.LiteralBlock
