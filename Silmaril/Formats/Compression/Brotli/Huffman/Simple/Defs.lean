module

public import Silmaril.Formats.Compression.Bits.BitstreamLemmas

/-! The body of an RFC 7932 §3.4 simple prefix description, following
its two-bit selector. Keep symbols in their original wire order. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Huffman.Simple

def alphabetWidth (alphabet : Nat) : Nat :=
  if alphabet ≤ 1 then 0 else (alphabet - 1).log2 + 1

inductive Shape where
  | singleton (a : Nat)
  | pair (a b : Nat)
  | triple (a b c : Nat)
  | balanced (a b c d : Nat)
  | skewed (a b c d : Nat)
  deriving DecidableEq, Repr

def Shape.symbols : Shape → List Nat
  | .singleton a => [a]
  | .pair a b => [a, b]
  | .triple a b c => [a, b, c]
  | .balanced a b c d | .skewed a b c d => [a, b, c, d]

def Shape.widths : Shape → List Nat
  | .singleton _ => [0]
  | .pair .. => [1, 1]
  | .triple .. => [1, 2, 2]
  | .balanced .. => [2, 2, 2, 2]
  | .skewed .. => [1, 2, 3, 3]

/-- The optional tree-select bit appears only for four symbols. -/
def Shape.treeBits : Shape → List Bool
  | .balanced .. => [false]
  | .skewed .. => [true]
  | _ => []

/-- Put each positive width at its original numeric ordinal. The
    singleton is represented separately by the description installer. -/
def Shape.lengths (shape : Shape) (alphabet : Nat) : List Nat :=
  let entries := shape.symbols.zip shape.widths
  (List.range alphabet).map fun ordinal =>
    ((entries.find? fun entry => entry.1 == ordinal).map Prod.snd).getD 0

def Shape.bits (shape : Shape) (alphabet : Nat) : List Bool :=
  natBits (shape.symbols.length - 1) 2 ++
    (shape.symbols.flatMap fun symbol => natBits symbol (alphabetWidth alphabet)) ++ shape.treeBits

structure Checked (alphabet : Nat) where
  shape : Shape
  bounded : ∀ symbol ∈ shape.symbols, symbol < alphabet
  distinct : shape.symbols.Nodup

def Wire (alphabet : Nat) (body : List Bool) (shape : Shape) : Prop :=
  body = shape.bits alphabet ∧ shape.symbols.Nodup ∧ ∀ symbol ∈ shape.symbols, symbol < alphabet

inductive Error where
  | bitLimit
  | truncated
  | symbolRange
  | duplicateSymbol
  | invalidCount
  deriving DecidableEq, Repr

namespace Internal

structure Cursor where
  reader : LSBReader
  remaining : Nat

def take (cursor : Cursor) (width : Nat) : Except Error (Nat × Cursor) :=
  if cursor.remaining < width then .error .bitLimit
  else
    match cursor.reader.readBits width with
    | none => .error .truncated
    | some (value, next) => .ok (value, ⟨next, cursor.remaining - width⟩)

def readSymbols (width : Nat) : Nat → Cursor → Except Error (List Nat × Cursor)
  | 0, cursor => .ok ([], cursor)
  | count + 1, cursor => do
    let (symbol, next) ← take cursor width
    let (rest, last) ← readSymbols width count next
    pure (symbol :: rest, last)

def finish (symbols : List Nat) (cursor : Cursor) : Except Error (Shape × Cursor) :=
  match symbols with
  | [a] => .ok (.singleton a, cursor)
  | [a, b] => .ok (.pair a b, cursor)
  | [a, b, c] => .ok (.triple a b c, cursor)
  | [a, b, c, d] => do
    let (tree, next) ← take cursor 1
    pure (if tree = 0 then .balanced a b c d else .skewed a b c d, next)
  | _ => .error .invalidCount

def check (alphabet : Nat) (shape : Shape) : Except Error (Checked alphabet) :=
  if bounded : shape.symbols.all (fun symbol => symbol < alphabet) = true then
    if distinct : shape.symbols.Nodup then
      .ok ⟨shape, fun symbol mem => of_decide_eq_true (List.all_eq_true.mp bounded symbol mem), distinct⟩
    else .error .duplicateSymbol
  else .error .symbolRange

end Internal

/-- Read the simple body under a bit cap. A width-zero symbol field
    is possible when the caller's alphabet has just one ordinal. -/
def read (alphabet limit : Nat) (reader : LSBReader) : Except Error (Checked alphabet × LSBReader) := do
  let (count, cursor) ← Internal.take ⟨reader, limit⟩ 2
  let (symbols, cursor) ← Internal.readSymbols (alphabetWidth alphabet) (count + 1) cursor
  let (shape, after) ← Internal.finish symbols cursor
  let checked ← Internal.check alphabet shape
  pure (checked, after.reader)

end Silmaril.Formats.Compression.Brotli.Huffman.Simple
