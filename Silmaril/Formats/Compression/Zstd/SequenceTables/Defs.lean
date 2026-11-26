module

public import Silmaril.Formats.Compression.Zstd.FseTable.NCount.Defs
public import Silmaril.Formats.Compression.Zstd.LiteralBlock.Defs

/-! # Zstandard sequence table prefixes

RFC 8878 §3.1.1.3.2.1 and §4.1.1. Given the exact extent of a sequences
section, resolve the three tables and retain the reverse bitstream verbatim.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.SequenceTables

open FseTable (Alphabet)

structure Limits where
  inputBytes : Nat
  sequences : Nat
  deriving DecidableEq, Repr

inductive Table where
  | rle (symbol : Nat)
  | fse (table : FseTable.Table)
  deriving DecidableEq, Repr

structure Tables where
  literalLength : Table
  offset : Table
  matchLength : Table
  deriving DecidableEq, Repr

inductive Section where
  | empty
  | coded (count : Nat) (tables : Tables) (bitstream : List UInt8)
  deriving DecidableEq, Repr

def Section.count : Section → Nat
  | .empty => 0
  | .coded count _ _ => count

def Section.bitstream : Section → List UInt8
  | .empty => []
  | .coded _ _ stream => stream

inductive Error where
  | inputLimit
  | sequenceLimit
  | count (reason : LiteralBlock.Error)
  | trailingEmptySection
  | missingModes
  | reservedBits
  | missingRleSymbol (alphabet : Alphabet)
  | invalidRleSymbol (alphabet : Alphabet)
  | predefined (alphabet : Alphabet) (reason : FseTable.Error)
  | transmitted (alphabet : Alphabet) (reason : FseTable.NCount.Error)
  | unsupportedMode (alphabet : Alphabet) (mode : Nat)
  | missingBitstream
  deriving DecidableEq, Repr

def tableLimits : Alphabet → FseTable.Limits
  | .literalLength => ⟨9, 36⟩
  | .offset => ⟨8, 32⟩
  | .matchLength => ⟨9, 53⟩

def transmittedLimits (alphabet : Alphabet) : FseTable.NCount.Limits :=
  ⟨tableLimits alphabet, 512, none⟩

def literalMode (byte : UInt8) : Nat := byte.toNat / 64
def offsetMode (byte : UInt8) : Nat := byte.toNat / 16 % 4
def matchMode (byte : UInt8) : Nat := byte.toNat / 4 % 4

/-- The table description is empty, one symbol byte, or an exact normalized
    distribution prefix. The FSE cases retain the state and symbol bounds. -/
inductive TableWire (alphabet : Alphabet) : Nat → List UInt8 → List UInt8 → Table → Prop where
  | predefined {rest : List UInt8} {table : FseTable.Table} :
      (FseTable.predefined alphabet).Valid (tableLimits alphabet) →
      FseTable.TableWire (FseTable.predefined alphabet) table →
      table.WellFormed (FseTable.predefined alphabet) →
      TableWire alphabet 0 [] rest (.fse table)
  | rle {byte : UInt8} {rest : List UInt8} :
      byte.toNat < (tableLimits alphabet).symbols →
      TableWire alphabet 1 [byte] rest (.rle byte.toNat)
  | transmitted {used rest : List UInt8} {parsed : FseTable.NCount.Prefix} {table : FseTable.Table} :
      parsed.rest = rest → parsed.bytes = used.length →
      parsed.Valid (transmittedLimits alphabet) (used ++ rest) →
      FseTable.TableWire parsed.distribution table → table.WellFormed parsed.distribution →
      TableWire alphabet 2 used rest (.fse table)

/-- A successful prefix identifies the exact table slices in wire order
    (literal length, offset, match length) and the untouched reverse stream. -/
inductive SectionWire : List UInt8 → Section → Prop where
  | empty {encoded : List UInt8} :
      LiteralBlock.SequenceCountWire encoded 0 → SectionWire encoded .empty
  | coded {encoded ll ofc ml stream : List UInt8} {mode : UInt8} {count : Nat} {tables : Tables} :
      LiteralBlock.SequenceCountWire encoded count → 0 < count → mode.toNat % 4 = 0 →
      TableWire .literalLength (literalMode mode) ll (ofc ++ ml ++ stream) tables.literalLength →
      TableWire .offset (offsetMode mode) ofc (ml ++ stream) tables.offset →
      TableWire .matchLength (matchMode mode) ml stream tables.matchLength →
      stream ≠ [] →
      SectionWire (encoded ++ [mode] ++ ll ++ ofc ++ ml ++ stream) (.coded count tables stream)

def resolveTable (alphabet : Alphabet) (mode : Nat) (input : List UInt8) :
    Except Error (Table × List UInt8) :=
  match mode with
  | 0 => do
    let (table, rest) ← (FseTable.selectPredefined (tableLimits alphabet) alphabet 0 input).mapError
      (Error.predefined alphabet)
    return (.fse table, rest)
  | 1 =>
    match input with
    | [] => .error (.missingRleSymbol alphabet)
    | byte :: rest =>
      if byte.toNat < (tableLimits alphabet).symbols then .ok (.rle byte.toNat, rest)
      else .error (.invalidRleSymbol alphabet)
  | 2 => do
    let (parsed, table) ← (FseTable.NCount.readTable (transmittedLimits alphabet) input).mapError
      (Error.transmitted alphabet)
    return (.fse table, parsed.rest)
  | other => .error (.unsupportedMode alphabet other)

/-- Check the bytes and count caps before table construction. For a positive
    count, the remaining bytes are reserved for reverse bitstream decoding. -/
def resolve (limits : Limits) (input : List UInt8) : Except Error Section := do
  if input.drop limits.inputBytes ≠ [] then throw .inputLimit
  let (count, rest) ← (LiteralBlock.readSequenceCount input).mapError Error.count
  if limits.sequences < count then throw .sequenceLimit
  if count = 0 then
    if rest.isEmpty then return .empty
    else throw .trailingEmptySection
  else
    match rest with
    | [] => throw .missingModes
    | mode :: descriptions => do
      if mode.toNat % 4 ≠ 0 then throw .reservedBits
      let (literalLength, afterLiteral) ← resolveTable .literalLength (literalMode mode) descriptions
      let (offset, afterOffset) ← resolveTable .offset (offsetMode mode) afterLiteral
      let (matchLength, stream) ← resolveTable .matchLength (matchMode mode) afterOffset
      if stream.isEmpty then throw .missingBitstream
      return .coded count ⟨literalLength, offset, matchLength⟩ stream

end Silmaril.Formats.Compression.Zstd.SequenceTables
