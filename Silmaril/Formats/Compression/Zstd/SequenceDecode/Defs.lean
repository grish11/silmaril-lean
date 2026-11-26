module

public import Silmaril.Formats.Compression.Zstd.SequenceTables.Defs
public import Silmaril.Formats.Compression.Zstd.RleSequences.Defs

/-! # Zstandard reverse sequence decoding

RFC 8878 §3.1.1.3.2.1.2 and §4.1. Sequence commands retain Offset_Value
for subsequent repeat-offset resolution and execution.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.SequenceDecode

open SequenceTables (Tables Table)
open ReverseBits (Cursor)

structure ByAlphabet (α : Type) where
  literalLength : α
  offset : α
  matchLength : α
  deriving DecidableEq, Repr

abbrev States := ByAlphabet Nat
abbrev Rows := ByAlphabet FseTable.Row

inductive Error where
  | prefix (reason : SequenceTables.Error)
  | badEndMarker
  | bitUnderflow
  | invalidState
  | invalidSymbol
  | trailingBits
  deriving DecidableEq, Repr

def stateWidth : Table → Nat
  | .rle _ => 0
  | .fse table => table.log

def InRange (tables : Tables) (states : States) : Prop :=
  states.literalLength < 2 ^ stateWidth tables.literalLength ∧
  states.offset < 2 ^ stateWidth tables.offset ∧
  states.matchLength < 2 ^ stateWidth tables.matchLength

/-- RLE has one state, selected with a zero-width field, and stays there. -/
def lookup : Table → Nat → Option FseTable.Row
  | .rle symbol, 0 => some ⟨symbol, 0, 0⟩
  | .rle _, _ + 1 => none
  | .fse table, state => table.rows[state]?

def offsetCode (symbol : Nat) : Option RleSequences.Code :=
  if symbol < 32 then some ⟨2 ^ symbol, symbol⟩ else none

/-- A field denotes an exact prefix of the unread bits in reverse read order. -/
def Field (width value : Nat) (before after : List Bit) : Prop :=
  ∃ field, before = field ++ after ∧ field.length = width ∧ value = Bit.bitsToNatMSB field

def ThreeFields (widths values : Nat × Nat × Nat) (before after : List Bit) : Prop :=
  ∃ middle next,
    Field widths.1 values.1 before middle ∧
    Field widths.2.1 values.2.1 middle next ∧
    Field widths.2.2 values.2.2 next after

def InitWire (tables : Tables) (before : List Bit) (states : States) (after : List Bit) : Prop :=
  ThreeFields
    (stateWidth tables.literalLength, stateWidth tables.offset, stateWidth tables.matchLength)
    (states.literalLength, states.offset, states.matchLength) before after ∧ InRange tables states

structure RowWire (alphabet : FseTable.Alphabet) (table : Table)
    (state : Nat) (row : FseTable.Row) : Prop where
  selected : lookup table state = some row
  accuracyBound : stateWidth table ≤ (SequenceTables.tableLimits alphabet).accuracyLog
  stateBound : state < 2 ^ stateWidth table
  symbolBound : row.symbol < (SequenceTables.tableLimits alphabet).symbols
  widthBound : row.bits ≤ stateWidth table
  nextBound : row.baseline + 2 ^ row.bits ≤ 2 ^ stateWidth table

structure RowsWire (tables : Tables) (states : States) (rows : Rows) : Prop where
  literalLength : RowWire .literalLength tables.literalLength states.literalLength rows.literalLength
  offset : RowWire .offset tables.offset states.offset rows.offset
  matchLength : RowWire .matchLength tables.matchLength states.matchLength rows.matchLength

/-- The command uses its selected symbols' RFC code mappings and reads the
    extra bits in offset, match length, literal length order. -/
def ExtraWire (rows : Rows) (before after : List Bit) (command : Sequence.Command) : Prop :=
  ∃ literal offset matched : RleSequences.Code,
    RleSequences.literalCode rows.literalLength.symbol = some literal ∧
    offsetCode rows.offset.symbol = some offset ∧
    RleSequences.matchCode rows.matchLength.symbol = some matched ∧
    ∃ ll ofc ml : Nat,
      ThreeFields (offset.width, matched.width, literal.width) (ofc, ml, ll) before after ∧
      command = ⟨literal.base + ll, offset.base + ofc, matched.base + ml⟩

/-- Transition bits are read in literal length, match length, offset order. -/
def NextWire (tables : Tables) (rows : Rows) (before : List Bit)
    (states : States) (after : List Bit) : Prop :=
  ∃ ll ofc ml : Nat,
    ThreeFields (rows.literalLength.bits, rows.matchLength.bits, rows.offset.bits)
      (ll, ml, ofc) before after ∧
    states = ⟨rows.literalLength.baseline + ll, rows.offset.baseline + ofc,
      rows.matchLength.baseline + ml⟩ ∧ InRange tables states

inductive CommandsWire (tables : Tables) : States → List Bit → List Sequence.Command → Prop where
  | done (states : States) : CommandsWire tables states [] []
  | last {states : States} {rows : Rows} {bits : List Bit} {command : Sequence.Command} :
      RowsWire tables states rows → ExtraWire rows bits [] command →
      CommandsWire tables states bits [command]
  | more {states next : States} {rows : Rows} {bits afterExtra afterNext : List Bit}
      {command nextCommand : Sequence.Command} {tail : List Sequence.Command} :
      RowsWire tables states rows → ExtraWire rows bits afterExtra command →
      NextWire tables rows afterExtra next afterNext →
      CommandsWire tables next afterNext (nextCommand :: tail) →
      CommandsWire tables states bits (command :: nextCommand :: tail)

inductive PayloadWire : SequenceTables.Section → List Sequence.Command → Prop where
  | empty : PayloadWire .empty []
  | coded {count : Nat} {tables : Tables} {stream : List UInt8} {commands : List Sequence.Command}
      {cursor : Cursor} {states : States} {bits : List Bit} :
      commands.length = count → ReverseBits.StartWire stream cursor →
      InitWire tables cursor.bits states bits → CommandsWire tables states bits commands →
      PayloadWire (.coded count tables stream) commands

namespace Internal

def readThree (first second third : Nat) (cursor : Cursor) : Option ((Nat × Nat × Nat) × Cursor) := do
  let (a, cursor) ← ReverseBits.read first cursor
  let (b, cursor) ← ReverseBits.read second cursor
  let (c, cursor) ← ReverseBits.read third cursor
  return ((a, b, c), cursor)

def readInitial (tables : Tables) (cursor : Cursor) : Option (States × Cursor) := do
  let ((ll, ofc, ml), rest) ← readThree
    (stateWidth tables.literalLength) (stateWidth tables.offset) (stateWidth tables.matchLength) cursor
  return (⟨ll, ofc, ml⟩, rest)

def selectRows (tables : Tables) (states : States) : Option Rows := do
  let ll ← lookup tables.literalLength states.literalLength
  let ofc ← lookup tables.offset states.offset
  let ml ← lookup tables.matchLength states.matchLength
  return ⟨ll, ofc, ml⟩

def readExtra (rows : Rows) (cursor : Cursor) : Except Error (Sequence.Command × Cursor) := do
  let some literal := RleSequences.literalCode rows.literalLength.symbol | throw .invalidSymbol
  let some offset := offsetCode rows.offset.symbol | throw .invalidSymbol
  let some matched := RleSequences.matchCode rows.matchLength.symbol | throw .invalidSymbol
  let some ((ofc, ml, ll), rest) := readThree offset.width matched.width literal.width cursor
    | throw .bitUnderflow
  return (⟨literal.base + ll, offset.base + ofc, matched.base + ml⟩, rest)

def advance (rows : Rows) (cursor : Cursor) : Option (States × Cursor) := do
  let ((ll, ml, ofc), rest) ← readThree rows.literalLength.bits rows.matchLength.bits rows.offset.bits cursor
  return (⟨rows.literalLength.baseline + ll, rows.offset.baseline + ofc, rows.matchLength.baseline + ml⟩, rest)

def readCommands (tables : Tables) :
    Nat → States → Cursor → List Sequence.Command → Except Error (List Sequence.Command)
  | 0, _, cursor, acc => if cursor.isEmpty then .ok acc.reverse else .error .trailingBits
  | count + 1, states, cursor, acc => do
    let some rows := selectRows tables states | throw .invalidState
    let (command, rest) ← readExtra rows cursor
    if count = 0 then readCommands tables count states rest (command :: acc)
    else
      let some (next, tail) := advance rows rest | throw .bitUnderflow
      readCommands tables count next tail (command :: acc)

def readResolved : SequenceTables.Section → Except Error (List Sequence.Command)
  | .empty => .ok []
  | .coded count tables stream => do
    let some cursor := ReverseBits.start stream | throw .badEndMarker
    let some (states, rest) := readInitial tables cursor | throw .bitUnderflow
    readCommands tables count states rest []

end Internal

def decode (limits : SequenceTables.Limits) (input : List UInt8) :
    Except Error (List Sequence.Command) := do
  let resolvedSection ← (SequenceTables.resolve limits input).mapError Error.prefix
  Internal.readResolved resolvedSection

end Silmaril.Formats.Compression.Zstd.SequenceDecode
