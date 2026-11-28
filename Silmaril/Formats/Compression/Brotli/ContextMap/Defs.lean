module

public import Silmaril.Formats.Compression.Brotli.BlockTypes.Defs

/-! A context map's tree count and, for a coded map, its RLE and Huffman
prefix (RFC 7932 §§7.3, 9.2). An implicit map is complete at the tree
count. A coded map returns the cursor at the first map symbol. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.ContextMap

inductive Kind where
  | literal
  | distance
  deriving DecidableEq, Repr

def Kind.contexts : Kind → Nat
  | .literal => 64
  | .distance => 4

def Kind.extent (kind : Kind) (types : Nat) : Nat := kind.contexts * types

structure Limits where
  entries : Nat
  bits : Nat

/-- The implicit form represents a constant zero vector of the given
    extent without allocating it. The coded form is a prefix only. -/
inductive Prefix where
  | implicit (entries : Nat)
  | coded (entries trees rleMax : Nat) (table : Huffman.Description.Table)

def Prefix.implicitIndex? : Prefix → Nat → Option Nat
  | .implicit entries, index => if index < entries then some 0 else none
  | .coded .., _ => none

inductive Error where
  | invalidBlockTypes
  | entryLimit
  | treeExtent
  | count (reason : BlockTypes.Error)
  | bitLimit
  | truncated
  | description (reason : Huffman.Description.Error)
  deriving DecidableEq, Repr

inductive RleWire : List Bool → Nat → Prop where
  | off : RleWire [false] 0
  | on {field : Nat} : field < 16 → RleWire ([true] ++ natBits field 4) (field + 1)

inductive Wire (entries : Nat) : List Bool → Prefix → Prop where
  | implicit : Wire entries [false] (.implicit entries)
  | coded {trees rleMax : Nat} {table : Huffman.Description.Table} {count rle description : List Bool} :
      2 ≤ trees → trees ≤ entries → BlockTypes.CountWire count trees →
      RleWire rle rleMax → Huffman.Description.Wire (trees + rleMax) description table →
      table.alphabetSize = trees + rleMax →
      Wire entries (count ++ rle ++ description) (.coded entries trees rleMax table)

namespace Internal

def take (bitLimit width : Nat) (reader : LSBReader) : Except Error (Nat × LSBReader) :=
  if bitLimit < width then .error .bitLimit
  else
    match reader.readBits width with
    | none => .error .truncated
    | some pair => .ok pair

def readRle (bitLimit : Nat) (reader : LSBReader) : Except Error (Nat × LSBReader) := do
  let (flag, after) ← take bitLimit 1 reader
  if flag = 0 then pure (0, after)
  else
    let (value, next) ← take (bitLimit - 1) 4 after
    pure (value + 1, next)

def readPrefix (entries bitLimit : Nat) (before : LSBReader) : Except Error (Prefix × LSBReader) := do
  let (trees, afterCount) ← (BlockTypes.readCount bitLimit before).mapError Error.count
  if trees = 1 then pure (.implicit entries, afterCount)
  else if entries < trees then .error .treeExtent
  else
    let remaining := bitLimit - (afterCount.totalRead - before.totalRead)
    let (rleMax, afterRle) ← readRle remaining afterCount
    let alphabet := trees + rleMax
    let remaining := remaining - (afterRle.totalRead - afterCount.totalRead)
    let (table, after) ←
      (Huffman.Description.read ⟨alphabet, remaining⟩ alphabet afterRle).mapError Error.description
    pure (.coded entries trees rleMax table, after)

end Internal

/-- Read a literal or distance map prefix at its NTREES field. The
    caller provides the block-type count from the surrounding header. -/
def read (kind : Kind) (types : Nat) (limits : Limits) (before : LSBReader) :
    Except Error (Prefix × LSBReader) :=
  if types = 0 ∨ 256 < types then .error .invalidBlockTypes
  else if limits.entries < kind.extent types then .error .entryLimit
  else Internal.readPrefix (kind.extent types) limits.bits before

end Silmaril.Formats.Compression.Brotli.ContextMap
