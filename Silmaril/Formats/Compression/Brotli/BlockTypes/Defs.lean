module

public import Silmaril.Formats.Compression.Brotli.Huffman.Description.Defs

/-! The first three controls in the compressed meta-block header (RFC
7932 §§6, 9.2), starting at NBLTYPESL and ending before NPOSTFIX. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.BlockTypes

open Huffman.Description (Table)

inductive Error where
  | bitLimit
  | truncated
  | description (reason : Huffman.Description.Error)
  | invalidCountCode
  deriving DecidableEq, Repr

/-- The three-bit width field can be zero, yielding a count of two
    with no extra bits. -/
inductive CountWire : List Bool → Nat → Prop where
  | one : CountWire [false] 1
  | many {width extra : Nat} : width < 8 → extra < 2 ^ width →
      CountWire ([true] ++ natBits width 3 ++ natBits extra width) (1 + 2 ^ width + extra)

/-- Section 6's block count code table, as (base, extra width). -/
def countCodes : List (Nat × Nat) :=
  [(1, 2), (5, 2), (9, 2), (13, 2), (17, 3), (25, 3), (33, 3), (41, 3),
   (49, 4), (65, 4), (81, 4), (97, 4), (113, 5), (145, 5), (177, 5), (209, 5),
   (241, 6), (305, 6), (369, 7), (497, 8), (753, 9), (1265, 10), (2289, 11),
   (4337, 12), (8433, 13), (16625, 24)]

def countCode (code : Nat) : Option (Nat × Nat) := countCodes[code]?

inductive Control where
  | single
  | multiple (types : Nat) (typeTable countTable : Table) (initialCount : Nat)

def Control.typeCount : Control → Nat
  | .single => 1
  | .multiple types .. => types

structure Controls where
  literal : Control
  insertCopy : Control
  distance : Control

/-- For a multi-type category the initial type is implicitly zero. Only
    the count symbol and its extra bits occur after the descriptions. -/
inductive ControlWire : List Bool → Control → Prop where
  | single : ControlWire [false] .single
  | multiple {types base width symbol code size extra : Nat}
      {typeTable countTable : Table} {countBits typeBits tableBits : List Bool} :
      2 ≤ types → CountWire countBits types →
      Huffman.Description.Wire (types + 2) typeBits typeTable →
      Huffman.Description.Wire 26 tableBits countTable →
      countTable.codeFor symbol = some (code, size) → size ≤ 15 →
      countCode symbol = some (base, width) → extra < 2 ^ width →
      ControlWire (countBits ++ typeBits ++ tableBits ++ msbBits code size ++ natBits extra width)
        (.multiple types typeTable countTable (base + extra))

def Wire (bits : List Bool) (controls : Controls) : Prop :=
  ∃ literal insertCopy distance,
    bits = literal ++ insertCopy ++ distance ∧ ControlWire literal controls.literal ∧
      ControlWire insertCopy controls.insertCopy ∧ ControlWire distance controls.distance

namespace Internal

structure Cursor where
  reader : LSBReader
  remaining : Nat

def Cursor.advance (cursor : Cursor) (after : LSBReader) : Cursor :=
  ⟨after, cursor.remaining - (after.totalRead - cursor.reader.totalRead)⟩

def take (cursor : Cursor) (width : Nat) : Except Error (Nat × Cursor) :=
  if cursor.remaining < width then .error .bitLimit
  else
    match cursor.reader.readBits width with
    | none => .error .truncated
    | some (value, after) => .ok (value, ⟨after, cursor.remaining - width⟩)

def readCount (cursor : Cursor) : Except Error (Nat × Cursor) := do
  let (lead, next) ← take cursor 1
  if lead = 0 then pure (1, next)
  else
    let (width, next) ← take next 3
    let (extra, after) ← take next width
    pure (1 + 2 ^ width + extra, after)

def readTable (alphabet : Nat) (cursor : Cursor) : Except Error (Table × Cursor) := do
  let (table, after) ←
    (Huffman.Description.read ⟨alphabet, cursor.remaining⟩ alphabet cursor.reader).mapError Error.description
  pure (table, cursor.advance after)

/-- Run shared lookup on at most 15 bits of scratch. Commit only a
    checked code on the original cursor, including a zero-bit singleton. -/
def findSymbol (table : Table) (cursor : Cursor) : Except Error Nat := do
  let available := cursor.reader.count + 8 * (cursor.reader.input.take 2).length
  let width := min 15 (min cursor.remaining available)
  let some (look, _) := cursor.reader.readBits width | throw .truncated
  let some (symbol, _) := table.readSymbol ⟨look, width, [], 0⟩
    | throw (if width = cursor.remaining then .bitLimit else .truncated)
  pure symbol

def readCode (table : Table) (cursor : Cursor) : Except Error (Nat × Cursor) := do
  let symbol ← findSymbol table cursor
  match table.codeFor symbol with
  | none => .error .invalidCountCode
  | some (code, width) =>
    if 15 < width then .error .invalidCountCode
    else
      let (value, after) ← take cursor width
      if natBits value width = msbBits code width then pure (symbol, after)
      else .error .invalidCountCode

def readInitial (table : Table) (cursor : Cursor) : Except Error (Nat × Cursor) := do
  let (symbol, next) ← readCode table cursor
  let some (base, width) := countCode symbol | throw .invalidCountCode
  let (extra, after) ← take next width
  pure (base + extra, after)

def readControl (cursor : Cursor) : Except Error (Control × Cursor) := do
  let (types, next) ← readCount cursor
  if types = 1 then pure (.single, next)
  else
    let (typeTable, next) ← readTable (types + 2) next
    let (countTable, next) ← readTable 26 next
    let (initial, after) ← readInitial countTable next
    pure (.multiple types typeTable countTable initial, after)

end Internal

/-- Read literal, insert-and-copy, then distance controls under one
    budget. No block switching or command execution is performed here. -/
def read (bitLimit : Nat) (before : LSBReader) : Except Error (Controls × LSBReader) := do
  let (literal, next) ← Internal.readControl ⟨before, bitLimit⟩
  let (insertCopy, next) ← Internal.readControl next
  let (distance, after) ← Internal.readControl next
  pure (⟨literal, insertCopy, distance⟩, after.reader)

end Silmaril.Formats.Compression.Brotli.BlockTypes
