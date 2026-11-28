module

public import Silmaril.Formats.Compression.Deflate.Decompress

/-! # Parquet LZ4_RAW blocks

The caller supplies the exact compressed and uncompressed sizes and independent
limits. The wire description is pinned in `docs/projects/parquet-lz4-raw.md`.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Lz4Raw

structure Bounds where
  compressedSize : Nat
  compressedLimit : Nat
  expectedSize : Nat
  outputLimit : Nat
  deriving Repr

inductive Error where
  | compressedLimit
  | outputLimit
  | compressedSizeMismatch
  | truncated
  | outputSizeMismatch
  | invalidOffset
  | invalidTail
  deriving DecidableEq, Repr

structure MatchSequence where
  literals : List UInt8
  offset : Nat
  length : Nat
  deriving DecidableEq, Repr

/-- Matched sequences are followed by exactly one literal-only sequence. -/
inductive Block where
  | final (literals : List UInt8)
  | more (sequence : MatchSequence) (rest : Block)
  deriving DecidableEq, Repr

def Block.outputSize : Block → Nat
  | .final literals => literals.length
  | .more sequence rest => sequence.literals.length + sequence.length + rest.outputSize

/-- Zero or more 255 bytes followed by one byte smaller than 255. -/
inductive Extension : List UInt8 → Nat → Prop where
  | stop (last : UInt8) (short : last.toNat < 255) : Extension [last] last.toNat
  | next {bytes : List UInt8} {extra : Nat} :
      Extension bytes extra → Extension (255 :: bytes) (255 + extra)

inductive LengthField : Nat → List UInt8 → Nat → Prop where
  | short (value : Nat) (small : value < 15) : LengthField value [] value
  | long {bytes : List UInt8} {extra : Nat} :
      Extension bytes extra → LengthField 15 bytes (15 + extra)

/-- Wire grammar. The final token has no match field. The empty block uses
    the zero token. A match length is four plus its encoded length field. -/
inductive Wire : List UInt8 → Block → Prop where
  | final {token : UInt8} {litExt literals : List UInt8} :
      LengthField (token.toNat / 16) litExt literals.length →
      (literals.length = 0 → token.toNat = 0) →
      Wire (token :: (litExt ++ literals)) (.final literals)
  | more {token lo hi : UInt8} {litExt literals matchExt bytes : List UInt8}
      {matchCode : Nat} {rest : Block} :
      LengthField (token.toNat / 16) litExt literals.length →
      LengthField (token.toNat % 16) matchExt matchCode →
      Wire bytes rest →
      Wire (token :: (litExt ++ literals ++ (lo :: hi :: (matchExt ++ bytes))))
        (.more ⟨literals, lo.toNat + 256 * hi.toNat, 4 + matchCode⟩ rest)

/-- With a preceding match, at least five final literals are required and
    the last match must start at least 12 decoded bytes before the end. -/
def TailValid (lastMatch : Option Nat) (literals : Nat) : Prop :=
  match lastMatch with
  | none => True
  | some length => 5 ≤ literals ∧ 12 ≤ length + literals

instance (lastMatch : Option Nat) (literals : Nat) : Decidable (TailValid lastMatch literals) := by
  cases lastMatch <;> unfold TailValid <;> infer_instance

/-- Block semantics over an evolving history, with explicit tail checks.
    Each back-copy step reads from the output as it grows. -/
inductive Denotes : Option Nat → List UInt8 → Block → List UInt8 → Prop where
  | final {lastMatch : Option Nat} {history literals : List UInt8} :
      TailValid lastMatch literals.length →
      Denotes lastMatch history (.final literals) (history ++ literals)
  | more {lastMatch : Option Nat} {history out : List UInt8} {rest : Block}
      {sequence : MatchSequence} :
      0 < sequence.offset →
      sequence.offset ≤ history.length + sequence.literals.length →
      Denotes (some sequence.length)
        (Deflate.copyBack sequence.offset (history ++ sequence.literals) sequence.length) rest out →
      Denotes lastMatch history (.more sequence rest) out

namespace Internal

/-- Test the exact compressed size without traversing bytes beyond the bound. -/
def hasLength : Nat → List UInt8 → Bool
  | 0, [] => true
  | n + 1, _ :: rest => hasLength n rest
  | _, _ => false

/-- Read an extension with an explicit room bound and a running sum. -/
def readExtension (room total : Nat) : List UInt8 → Except Error (Nat × List UInt8)
  | [] => .error .truncated
  | byte :: rest =>
    let n := byte.toNat
    if room < n then .error .outputSizeMismatch
    else if n = 255 then readExtension (room - n) (total + n) rest
    else .ok (total + n, rest)

def readLength (nibble room : Nat) (input : List UInt8) : Except Error (Nat × List UInt8) :=
  if room < nibble then .error .outputSizeMismatch
  else if nibble = 15 then readExtension (room - 15) 15 input
  else .ok (nibble, input)

def takeLiterals (count : Nat) (bytes : List UInt8) : Except Error (List UInt8 × List UInt8) :=
  let (literals, rest) := bytes.splitAt count
  if literals.length = count then .ok (literals, rest) else .error .truncated

def prependReversed (sequences : List MatchSequence) (block : Block) : Block :=
  sequences.foldl (fun rest sequence => .more sequence rest) block

/-- Fuel bounds the number of sequences by the compressed size. Room checks
    precede literal allocation and match expansion. -/
def readBlock : Nat → Nat → List UInt8 → List MatchSequence → Except Error Block
  | 0, _, _, _ | _, _, [], _ => .error .truncated
  | fuel + 1, room, token :: bytes, rev => do
    let (literalLen, afterLength) ← readLength (token.toNat / 16) room bytes
    let (literals, rest) ← takeLiterals literalLen afterLength
    match rest with
    | [] =>
      if literalLen ≠ room then .error .outputSizeMismatch
      else if literalLen = 0 ∧ token.toNat ≠ 0 then .error .invalidTail
      else .ok (prependReversed rev (.final literals))
    | [_] => .error .truncated
    | lo :: hi :: tail =>
      if room < literalLen + 4 then .error .outputSizeMismatch
      else do
        let (matchCode, next) ← readLength (token.toNat % 16) (room - literalLen - 4) tail
        let sequence : MatchSequence := ⟨literals, lo.toNat + 256 * hi.toNat, 4 + matchCode⟩
        readBlock fuel (room - literalLen - sequence.length) next (sequence :: rev)

def expand (lastMatch : Option Nat) (out : Array UInt8) : Block → Except Error (Array UInt8)
  | .final literals =>
    if TailValid lastMatch literals.length then .ok (out.appendList literals)
    else .error .invalidTail
  | .more sequence rest =>
    let withLiterals := out.appendList sequence.literals
    if 0 < sequence.offset ∧ sequence.offset ≤ withLiterals.size then
      let next := Deflate.copyBackArr sequence.offset withLiterals sequence.length
      expand (some sequence.length) next rest
    else .error .invalidOffset

end Internal

/-- Read precisely the supplied block. Syntax parsing accounts for the
    expected output size, and the expander checks offsets and the tail. -/
def parse (bounds : Bounds) (input : List UInt8) : Except Error Block :=
  if bounds.compressedLimit < bounds.compressedSize then .error .compressedLimit
  else if bounds.outputLimit < bounds.expectedSize then .error .outputLimit
  else if Internal.hasLength bounds.compressedSize input then
    Internal.readBlock bounds.compressedSize bounds.expectedSize input []
  else .error .compressedSizeMismatch

/-- Decode exactly one independent block, with empty initial history. -/
def decode (bounds : Bounds) (input : List UInt8) : Except Error (List UInt8) := do
  let block ← parse bounds input
  let out ← Internal.expand none #[] block
  return out.toList

/-- Emit a single literal-only sequence. The caller supplies outer metadata
    and limits when using these bytes as a Parquet payload. -/
def encodeLiteral (input : List UInt8) : List UInt8 :=
  let size := input.length
  if size < 15 then UInt8.ofNat (size * 16) :: input
  else
    let extra := size - 15
    0xf0 :: (List.replicate (extra / 255) 255 ++ UInt8.ofNat (extra % 255) :: input)

end Silmaril.Formats.Compression.Lz4Raw
