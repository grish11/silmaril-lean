module

public import Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights.Defs
public import Silmaril.Formats.Compression.Zstd.ReverseBits.Defs

/-! # Zstandard canonical Huffman table and one reverse stream

RFC 8878 §§4.2.1.3–4.2.2. The caller supplies the weights and the exact
stream extent. The end marker and regenerated symbol count are checked.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.Huffman.SingleStream

open DirectWeights (Tree mass slots)
open ReverseBits (Cursor)

structure Entry where
  symbol : Nat
  width : Nat
  code : Nat
  deriving DecidableEq, Repr

def Entry.span (depth : Nat) (entry : Entry) : Nat := 2 ^ (depth - entry.width)

def Entry.start (depth : Nat) (entry : Entry) : Nat := entry.code * entry.span depth

def Entry.finish (depth : Nat) (entry : Entry) : Nat := entry.start depth + entry.span depth

structure Table where
  depth : Nat
  entries : List Entry
  deriving DecidableEq, Repr

structure Limits where
  tree : DirectWeights.Limits
  inputBytes : Nat
  outputSymbols : Nat
  deriving DecidableEq, Repr

inductive Error where
  | invalidTree
  | invalidLayout
  | inputLimit
  | outputLimit
  | badEndMarker
  | incompleteCode
  | trailingBits
  deriving DecidableEq, Repr

/-- Sort first by positive weight, then by the original literal value. -/
def ranked (tree : Tree) : List (Nat × Nat) :=
  (List.range' 1 tree.depth).flatMap fun weight =>
    tree.weights.zipIdx.filter (fun entry => entry.1 == weight)

/-- The slot cursor is the code left-aligned to the full depth. The slot
    interval of a code is consecutive, aligned and within the tree. -/
inductive LayoutWire (depth : Nat) : Nat → List (Nat × Nat) → List Entry → Nat → Prop where
  | done (start : Nat) : LayoutWire depth start [] [] start
  | code {start finish weight symbol : Nat} {rank : List (Nat × Nat)} {entries : List Entry} :
      0 < weight → weight ≤ depth → symbol < 256 →
      start % slots weight = 0 → start + slots weight ≤ 2 ^ depth →
      LayoutWire depth (start + slots weight) rank entries finish →
      LayoutWire depth start ((weight, symbol) :: rank)
        (⟨symbol, depth + 1 - weight, start / slots weight⟩ :: entries) finish

def TableWire (tree : Tree) (table : Table) : Prop :=
  table.depth = tree.depth ∧ LayoutWire tree.depth 0 (ranked tree) table.entries (2 ^ tree.depth)

/-- Decode a forward sequence of symbols from all reverse-ordered payload bits. -/
inductive StreamWire (entries : List Entry) : List Bit → List UInt8 → Prop where
  | done : StreamWire entries [] []
  | symbol {entry : Entry} {field tail : List Bit} {bytes : List UInt8} :
      entry ∈ entries → field.length = entry.width → Bit.bitsToNatMSB field = entry.code →
      StreamWire entries tail bytes →
      StreamWire entries (field ++ tail) (entry.symbol.toUInt8 :: bytes)

namespace Internal

/-- The list and exponents are bounded before summing tree slots. -/
def validate (limits : DirectWeights.Limits) (tree : Tree) : Except Error Unit :=
  if tree.depth = 0 ∨ limits.depthCap < tree.depth then .error .invalidTree
  else if tree.weights.drop limits.symbolCap ≠ [] then .error .invalidTree
  else if tree.weights.length < 2 then .error .invalidTree
  else if !(tree.weights.all fun weight => decide (weight ≤ tree.depth)) then .error .invalidTree
  else if mass tree.weights ≠ 2 ^ tree.depth then .error .invalidTree
  else if tree.weights.count 1 < 2 ∨ tree.weights.count 1 % 2 ≠ 0 then .error .invalidTree
  else .ok ()

def place (depth : Nat) : Nat → List (Nat × Nat) → Except Error (List Entry × Nat)
  | start, [] => .ok ([], start)
  | start, (weight, symbol) :: ranks =>
    let stride := slots weight
    let next := start + stride
    if weight = 0 ∨ depth < weight ∨ 256 ≤ symbol ∨ start % stride ≠ 0 ∨ 2 ^ depth < next then
      .error .invalidLayout
    else do
      let (entries, finish) ← place depth next ranks
      return (⟨symbol, depth + 1 - weight, start / stride⟩ :: entries, finish)

/-- Trying a code leaves the input cursor untouched unless it matches. -/
def readSymbol (cursor : Cursor) : List Entry → Option (UInt8 × Cursor)
  | [] => none
  | entry :: entries =>
    match ReverseBits.read entry.width cursor with
    | some (value, rest) =>
      if value = entry.code then some (entry.symbol.toUInt8, rest) else readSymbol cursor entries
    | none => readSymbol cursor entries

def readSymbols (entries : List Entry) :
    Nat → Cursor → List UInt8 → Except Error (List UInt8)
  | 0, cursor, acc => if cursor.isEmpty then .ok acc.reverse else .error .trailingBits
  | count + 1, cursor, acc =>
    match readSymbol cursor entries with
    | none => .error .incompleteCode
    | some (symbol, rest) => readSymbols entries count rest (symbol :: acc)

end Internal

/-- Construct a canonical table from weights satisfying the direct tree
    contract, with a checked, full interval placement. -/
def build (limits : DirectWeights.Limits) (tree : Tree) : Except Error Table := do
  Internal.validate limits tree
  let (entries, finish) ← Internal.place tree.depth 0 (ranked tree)
  if finish ≠ 2 ^ tree.depth then .error .invalidLayout else .ok ⟨tree.depth, entries⟩

/-- Decode exactly the declared number of symbols and require exhaustion. -/
def decode (limits : Limits) (tree : Tree) (expected : Nat) (input : List UInt8) :
    Except Error (List UInt8) :=
  if input.drop limits.inputBytes ≠ [] then .error .inputLimit
  else if limits.outputSymbols < expected then .error .outputLimit
  else do
    let table ← build limits.tree tree
    let some cursor := ReverseBits.start input | throw .badEndMarker
    Internal.readSymbols table.entries expected cursor []

end Silmaril.Formats.Compression.Zstd.Huffman.SingleStream
