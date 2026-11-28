module

public import Silmaril.Formats.Compression.Zstd.FseTable.NCount.Defs
public import Silmaril.Formats.Compression.Zstd.ReverseBits.Defs

/-! # Zstandard Huffman FSE description and initial states

RFC 8878 §§4.2.1 and 4.2.1.2. The description's exact byte extent contains
a normalized-count prefix and a marker-terminated reverse bitstream. Two
state fields are read in order using the same bounded table.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix

open FseTable
open ReverseBits (Cursor)

/-- Weight symbols are 0 through 11. The FSE accuracy log is at most 6. -/
def countLimits (size : Nat) : NCount.Limits := ⟨⟨6, 12⟩, size, none⟩

structure States where
  first : Nat
  second : Nat
  deriving DecidableEq, Repr

structure Setup where
  counts : NCount.Prefix
  table : FseTable.Table
  states : States
  cursor : Cursor
  deriving DecidableEq, Repr

structure Prefix where
  setup : Setup
  consumed : Nat
  rest : List UInt8
  deriving DecidableEq, Repr

inductive Error where
  | truncated
  | directMode
  | emptyDescription
  | byteLimit
  | counts (reason : NCount.Error)
  | badEndMarker
  | truncatedStates
  deriving DecidableEq, Repr

/-- State 1 is for the even-indexed weights and is initialized first.
    Exactly two fixed-width fields are removed from the reverse stream. -/
def InitWire (width : Nat) (start : Cursor) (states : States) (rest : Cursor) : Prop :=
  (∃ first second : List Bit,
    start.bits = first ++ second ++ rest.bits ∧ first.length = width ∧ second.length = width ∧
    states.first = Bit.bitsToNatMSB first ∧ states.second = Bit.bitsToNatMSB second) ∧
  states.first < 2 ^ width ∧ states.second < 2 ^ width ∧ start.remaining = 2 * width + rest.remaining

def Setup.Wire (body : List UInt8) (setup : Setup) : Prop :=
  setup.counts.Valid (countLimits body.length) body ∧
    FseTable.TableWire setup.counts.distribution setup.table ∧
    setup.table.WellFormed setup.counts.distribution ∧
    setup.table.rows.length ≤ 64 ∧
    setup.states.first < setup.table.rows.length ∧ setup.states.second < setup.table.rows.length ∧
    ∃ start, ReverseBits.StartWire setup.counts.rest start ∧
      InitWire setup.table.log start setup.states setup.cursor

def PrefixWire (input : List UInt8) (result : Prefix) : Prop :=
  ∃ (header : UInt8) (body : List UInt8),
    input = header :: (body ++ result.rest) ∧ 0 < header.toNat ∧ header.toNat < 128 ∧
    body.length = header.toNat ∧ result.consumed = 1 + body.length ∧ result.setup.Wire body

namespace Internal

def readStates (width : Nat) (cursor : Cursor) : Option (States × Cursor) := do
  let (first, middle) ← ReverseBits.read width cursor
  let (second, rest) ← ReverseBits.read width middle
  return (⟨first, second⟩, rest)

def readSetup (body : List UInt8) : Except Error Setup := do
  let (counts, table) ← (NCount.readTable (countLimits body.length) body).mapError Error.counts
  let some start := ReverseBits.start counts.rest | throw .badEndMarker
  let some (states, cursor) := readStates table.log start | throw .truncatedStates
  return ⟨counts, table, states, cursor⟩

end Internal

/-- Read just the compressed weight description and initialize the two
    states. Return the remaining reverse bits and the untouched literal suffix. -/
def read (byteLimit : Nat) : List UInt8 → Except Error Prefix
  | [] => .error .truncated
  | header :: input =>
    let size := header.toNat
    if 128 ≤ size then .error .directMode
    else if size = 0 then .error .emptyDescription
    else if byteLimit < 1 + size then .error .byteLimit
    else
      let body := input.take size
      if body.length ≠ size then .error .truncated
      else (Internal.readSetup body).map fun setup => ⟨setup, 1 + size, input.drop size⟩

end Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix
