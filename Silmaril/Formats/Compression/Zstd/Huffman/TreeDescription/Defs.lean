module

public import Silmaril.Formats.Compression.Zstd.Huffman.FseWeights.Defs
public import Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Defs

/-! # Zstandard Huffman tree description prefix

RFC 8878 §§4.2.1–4.2.1.3. Dispatch the direct and FSE weight encodings
and return a completed tree with the untouched suffix.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription

inductive Mode where
  | direct
  | fse
  deriving DecidableEq, Repr

structure Limits where
  bytes : Nat
  tree : Weights.Limits
  deriving DecidableEq, Repr

def Limits.direct (limits : Limits) : DirectWeights.Limits :=
  ⟨limits.bytes, limits.tree.symbols, limits.tree.depth⟩

def Limits.treeLimits (limits : Limits) : Mode → Weights.Limits
  | .direct => limits.direct.weightLimits
  | .fse => limits.tree

def Limits.byteCap (limits : Limits) : Mode → Nat
  | .direct => limits.direct.byteCap
  | .fse => min limits.bytes 128

structure Prefix where
  mode : Mode
  tree : Weights.Tree
  consumed : Nat
  rest : List UInt8
  deriving DecidableEq, Repr

def Prefix.transmitted (result : Prefix) : List Nat := result.tree.weights.dropLast

inductive Error where
  | truncated
  | direct (reason : DirectWeights.Error)
  | fse (reason : FseWeights.Error)
  | completion (reason : Weights.Error)
  | table (reason : SingleStream.Error)
  deriving DecidableEq, Repr

inductive Wire (input : List UInt8) : Prefix → Prop where
  | direct {parsed : DirectWeights.Prefix} :
      DirectWeights.PrefixWire input parsed →
      Wire input ⟨.direct, parsed.tree, parsed.consumed, parsed.rest⟩
  | fse {parsed : FseWeights.Prefix} {tree : Weights.Tree} :
      FseWeights.Wire input parsed → Weights.CompletionWire parsed.weights tree →
      Wire input ⟨.fse, tree, parsed.consumed, parsed.rest⟩

def Prefix.Valid (result : Prefix) (limits : Limits) (input : List UInt8) : Prop :=
  Wire input result ∧ Weights.Valid (limits.treeLimits result.mode) result.tree ∧
    result.consumed ≤ limits.byteCap result.mode

/-- The header chooses the encoding. In the FSE branch reserve one symbol
    position for inference before emitting the explicit weights. -/
def read (limits : Limits) (input : List UInt8) : Except Error Prefix :=
  match input with
  | [] => .error .truncated
  | header :: _ =>
    if 128 ≤ header.toNat then
      (DirectWeights.read limits.direct input).mapError Error.direct |>.map
        (fun parsed => ⟨.direct, parsed.tree, parsed.consumed, parsed.rest⟩)
    else do
      let parsed ← (FseWeights.read limits.bytes (limits.tree.symbolCap - 1) input).mapError Error.fse
      let tree ← (Weights.complete limits.tree parsed.weights).mapError Error.completion
      return ⟨.fse, tree, parsed.consumed, parsed.rest⟩

/-- Build the shared canonical table from the completed tree. -/
def readTable (limits : Limits) (input : List UInt8) : Except Error (Prefix × SingleStream.Table) := do
  let parsed ← read limits input
  let table ← (SingleStream.buildGeneral (limits.treeLimits parsed.mode) parsed.tree).mapError Error.table
  return (parsed, table)

end Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription
