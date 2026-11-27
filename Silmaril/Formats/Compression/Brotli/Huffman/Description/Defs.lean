module

public import Silmaril.Formats.Compression.Brotli.Huffman.Simple.Defs
public import Silmaril.Formats.Compression.Brotli.Huffman.MainTable.Defs

/-! A checked prefix for either RFC 7932 Huffman description grammar.
The result stops at the first following bit, before symbol data. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Huffman.Description

inductive Table where
  | singleton (alphabet only : Nat) (bounded : only < alphabet)
  | canonical (table : MainTable.Table)

def Table.alphabetSize : Table → Nat
  | .singleton alphabet _ _ => alphabet
  | .canonical table => table.lengths.length

def Table.codeFor (table : Table) (symbol : Nat) : Option (Nat × Nat) :=
  match table with
  | .singleton _ only _ => if symbol = only then some (0, 0) else none
  | .canonical table => table.decoder.encodeSymbol symbol

/-- The singleton never consults the input. Positive-width codes use the
    existing canonical reader. Callers still supply a bounded symbol count. -/
def Table.readSymbol (table : Table) (reader : LSBReader) : Option (Nat × LSBReader) :=
  match table with
  | .singleton _ only _ => some (only, reader)
  | .canonical table => table.decoder.readSymbolLSB reader

inductive SymbolError where
  | bitLimit
  | truncated
  | invalidCode
  deriving DecidableEq, Repr

def Internal.findBounded (table : Table) (bitLimit : Nat) (before : LSBReader) :
    Except SymbolError Nat := do
  let available := before.count + 8 * (before.input.take 2).length
  let width := min 15 (min bitLimit available)
  let some (look, _) := before.readBits width | throw .truncated
  let some (symbol, _) := table.readSymbol ⟨look, width, [], 0⟩
    | throw (if width = bitLimit then .bitLimit else .truncated)
  pure symbol

/-- Look up a code in at most 15 scratch bits and commit the matching
    code on the original cursor. A singleton can commit zero bits. -/
def Table.readBounded (table : Table) (bitLimit : Nat) (before : LSBReader) :
    Except SymbolError (Nat × LSBReader) := do
  let symbol ← Internal.findBounded table bitLimit before
  let some (code, width) := table.codeFor symbol | throw .invalidCode
  if 15 < width then
    throw .invalidCode
  else if bitLimit < width then
    throw .bitLimit
  else
    let some (value, after) := before.readBits width | throw .truncated
    if natBits value width = msbBits code width then pure (symbol, after)
    else throw .invalidCode

inductive Error where
  | alphabetSize
  | alphabetLimit
  | bitLimit
  | truncated
  | simple (reason : Simple.Error)
  | simpleCode (reason : MainTable.Error)
  | secondary (reason : CodeLengths.Error)
  | main (reason : MainTable.Error)
  deriving DecidableEq, Repr

def SimpleTableWire (alphabet : Nat) (shape : Simple.Shape) (table : Table) : Prop :=
  match shape with
  | .singleton only => ∃ bound : only < alphabet, table = .singleton alphabet only bound
  | _ => ∃ codes, table = .canonical codes ∧ codes.lengths = shape.lengths alphabet

inductive Wire (alphabet : Nat) : List Bool → Table → Prop where
  | simple {shape : Simple.Shape} {body : List Bool} {table : Table} :
      Simple.Wire alphabet body shape → SimpleTableWire alphabet shape table →
      Wire alphabet (natBits 1 2 ++ body) table
  | complex {secondary : CodeLengths.Table} {header body : List Bool} {table : MainTable.Table} :
      CodeLengths.Wire header secondary →
      MainLengths.RunsWire secondary MainLengths.History.start alphabet 32768 body table.lengths →
      Wire alphabet (header ++ body) (.canonical table)

namespace Internal

def installSimple {alphabet : Nat} (checked : Simple.Checked alphabet) : Except Error Table :=
  match shape : checked.shape with
  | .singleton only =>
    have bound : only < alphabet := checked.bounded only (by simp [shape, Simple.Shape.symbols])
    .ok (.singleton alphabet only bound)
  | other =>
    ((MainTable.Internal.install (other.lengths alphabet)).map Table.canonical).mapError Error.simpleCode

def readSimple (alphabet limit : Nat) (reader : LSBReader) : Except Error (Table × LSBReader) := do
  let (checked, after) ← (Simple.read alphabet limit reader).mapError Error.simple
  let table ← installSimple checked
  pure (table, after)

def readComplex (limits : MainLengths.Limits) (alphabet : Nat) (before : LSBReader) :
    Except Error (Table × LSBReader) := do
  let (secondary, cursor) ← (CodeLengths.read limits.bits before).mapError Error.secondary
  let remaining := limits.bits - (cursor.totalRead - before.totalRead)
  let (table, after) ← (MainTable.read { limits with bits := remaining } alphabet secondary cursor).mapError Error.main
  pure (.canonical table, after)

end Internal

/-- Select the grammar under one shared bit budget. The complex reader
    receives the original cursor, so its wire witness includes HSKIP. -/
def read (limits : MainLengths.Limits) (alphabet : Nat) (before : LSBReader) :
    Except Error (Table × LSBReader) :=
  if alphabet = 0 ∨ 704 < alphabet then .error .alphabetSize
  else if limits.alphabet < alphabet then .error .alphabetLimit
  else if limits.bits < 2 then .error .bitLimit
  else
    match before.readBits 2 with
    | none => .error .truncated
    | some (selector, cursor) =>
      if selector = 1 then Internal.readSimple alphabet (limits.bits - 2) cursor
      else Internal.readComplex limits alphabet before

end Silmaril.Formats.Compression.Brotli.Huffman.Description
