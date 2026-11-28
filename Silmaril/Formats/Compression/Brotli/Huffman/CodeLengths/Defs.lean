module

public import Silmaril.Formats.Compression.Bits.BitstreamLemmas
public import Silmaril.Formats.Compression.Deflate.Huffman

/-! # Brotli's complex code-length prefix table

RFC 7932 §3.5 first describes a code over the 18 code-length symbols.
Read only this first phase, from the supplied bit cursor. The following
main code lengths remain in the returned cursor.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths

/-- HSKIP = 1 belongs to the simple description grammar. -/
inductive Skip where
  | zero | two | three
  deriving DecidableEq, Repr

def Skip.count : Skip → Nat
  | .zero => 0
  | .two => 2
  | .three => 3

inductive Length where
  | zero | one | two | three | four | five
  deriving DecidableEq, Repr

def Length.value : Length → Nat
  | .zero => 0
  | .one => 1
  | .two => 2
  | .three => 3
  | .four => 4
  | .five => 5

/-- RFC §3.5's fixed code, in incoming bit order. -/
def Length.bits : Length → List Bool
  | .zero => [false, false]
  | .one => [true, true, true, false]
  | .two => [true, true, false]
  | .three => [false, true]
  | .four => [true, false]
  | .five => [true, true, true, true]

def Length.mass : Length → Nat
  | .zero => 0
  | length => 32 >>> length.value

def symbolOrder : List Nat := [1, 2, 3, 4, 0, 5, 17, 6, 16, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- Fill skipped and omitted lengths with zero, in numeric symbol order. -/
def orderedLengths (skip : Skip) (explicit : List Length) : List Length :=
  let byPosition := List.replicate skip.count .zero ++ explicit
  (List.range 18).map fun symbol => byPosition.getD (symbolOrder.idxOf symbol) .zero

def activeSymbols (lengths : List Length) : List Nat :=
  (List.range 18).filter fun symbol => lengths.getD symbol .zero != .zero

inductive Codes where
  | singleton (symbol : Nat)
  | canonical (table : HuffmanTable)

def Codes.Valid (lengths : List Length) : Codes → Prop
  | .singleton symbol => activeSymbols lengths = [symbol]
  | .canonical table =>
    isCompleteCode (lengths.map Length.value) 5 = true ∧
      HuffmanTable.ofLengths (lengths.map Length.value) 5 = some table

structure Table where
  lengths : List Length
  codes : Codes
  size : lengths.length = 18
  checked : codes.Valid lengths

/-- Look up a canonical code value and its width. A singleton has one
    present code of width zero. -/
def Table.codeFor (table : Table) (symbol : Nat) : Option (Nat × Nat) :=
  match table.codes with
  | .singleton only => if only = symbol then some (0, 0) else none
  | .canonical codes => codes.encodeSymbol symbol

inductive Error where
  | unsupportedSimple
  | bitLimit
  | truncated
  | oversubscribed
  | incomplete
  deriving DecidableEq, Repr

/-- Read in wire order while slots and Kraft space remain. Zero space
    stops immediately. Exhausting the slots exposes the remaining mass
    so that the outer grammar can check the singleton case. -/
inductive LengthsWire : Nat → Nat → List Length → Nat → List Bool → Prop where
  | complete (slots : Nat) : LengthsWire slots 0 [] 0 []
  | exhausted {space : Nat} : 0 < space → LengthsWire 0 space [] space []
  | next {slots space restSpace : Nat} {value : Length} {lengths : List Length}
      {bits : List Bool} :
      0 < space → value.mass ≤ space →
      LengthsWire slots (space - value.mass) lengths restSpace bits →
      LengthsWire (slots + 1) space (value :: lengths) restSpace (value.bits ++ bits)

def Wire (used : List Bool) (table : Table) : Prop :=
  ∃ skip explicit space body,
    used = natBits skip.count 2 ++ body ∧
    LengthsWire (18 - skip.count) 32 explicit space body ∧
    table.lengths = orderedLengths skip explicit ∧
    match table.codes with
    | .singleton _ => 0 < space
    | .canonical _ => space = 0

namespace Internal

structure Cursor where
  reader : LSBReader
  remaining : Nat

def take (cursor : Cursor) (width : Nat) : Except Error (Nat × Cursor) :=
  if cursor.remaining < width then .error .bitLimit
  else
    match cursor.reader.readBits width with
    | none => .error .truncated
    | some (value, reader) => .ok (value, ⟨reader, cursor.remaining - width⟩)

def select : Nat → Except Error Skip
  | 0 => .ok .zero
  | 2 => .ok .two
  | 3 => .ok .three
  | _ => .error .unsupportedSimple

def readLength (cursor : Cursor) : Except Error (Length × Cursor) := do
  let (head, cursor) ← take cursor 2
  match head with
  | 0 => pure (.zero, cursor)
  | 1 => pure (.four, cursor)
  | 2 => pure (.three, cursor)
  | _ => do
    let (third, cursor) ← take cursor 1
    if third = 0 then pure (.two, cursor)
    else
      let (fourth, cursor) ← take cursor 1
      pure (if fourth = 0 then .one else .five, cursor)

def readLengths (slots space : Nat) (cursor : Cursor) : Except Error (List Length × Nat × Cursor) :=
  if space = 0 then .ok ([], 0, cursor)
  else
    match slots with
    | 0 => .ok ([], space, cursor)
    | slots + 1 => do
      let (value, next) ← readLength cursor
      if space < value.mass then .error .oversubscribed
      else
        let (lengths, remaining, last) ← readLengths slots (space - value.mass) next
        pure (value :: lengths, remaining, last)

def finish (skip : Skip) (explicit : List Length) (space : Nat) : Except Error Table :=
  let lengths := orderedLengths skip explicit
  have size : lengths.length = 18 := by simp [lengths, orderedLengths]
  if space = 0 then
    let values := lengths.map Length.value
    if complete : isCompleteCode values 5 = true then
      match checked : HuffmanTable.ofLengths values 5 with
      | none => .error .incomplete
      | some table => .ok ⟨lengths, .canonical table, size, complete, checked⟩
    else .error .incomplete
  else
    match active : activeSymbols lengths with
    | [symbol] => .ok ⟨lengths, .singleton symbol, size, active⟩
    | _ => .error .incomplete

end Internal

/-- Read one complex code-length-code description, debiting the caller's
    bit limit for each field. The suffix stays in the returned cursor. -/
def read (bitLimit : Nat) (reader : LSBReader) : Except Error (Table × LSBReader) := do
  let (selector, cursor) ← Internal.take ⟨reader, bitLimit⟩ 2
  let skip ← Internal.select selector
  let (explicit, remaining, after) ← Internal.readLengths (18 - skip.count) 32 cursor
  let table ← Internal.finish skip explicit remaining
  pure (table, after.reader)

end Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths
