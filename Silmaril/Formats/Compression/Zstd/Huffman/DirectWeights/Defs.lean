module

/-! # Direct Zstandard Huffman weight descriptions

RFC 8878 §§4.2.1–4.2.1.1. Read the byte-aligned description and infer the
last symbol's weight. The following literal stream is returned verbatim.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights

structure Limits where
  bytes : Nat
  symbols : Nat
  depth : Nat
  deriving DecidableEq, Repr

def Limits.byteCap (limits : Limits) : Nat := min limits.bytes 65

/-- Includes the symbol whose weight is inferred. -/
def Limits.symbolCap (limits : Limits) : Nat := min limits.symbols 129

def Limits.depthCap (limits : Limits) : Nat := min limits.depth 11

structure Tree where
  depth : Nat
  weights : List Nat
  deriving DecidableEq, Repr

structure Prefix where
  tree : Tree
  consumed : Nat
  rest : List UInt8
  deriving DecidableEq, Repr

inductive Error where
  | truncated
  | unsupportedFse (bytes : Nat)
  | byteLimit
  | symbolLimit
  | zeroMass
  | depthLimit
  | nonPowerRemainder
  | invalidDeepestRank
  deriving DecidableEq, Repr

def slots (weight : Nat) : Nat := if weight = 0 then 0 else 2 ^ (weight - 1)

def mass (weights : List Nat) : Nat := (weights.map slots).sum

def transmittedCount (header : UInt8) : Nat := header.toNat - 127

def packedSize (count : Nat) : Nat := (count + 1) / 2

/-- The high nibble precedes the low nibble. The caller takes just the
    transmitted symbol count, skipping the low padding nibble if odd. -/
def unpack (bytes : List UInt8) : List Nat :=
  bytes.flatMap (fun byte => [byte.toNat / 16, byte.toNat % 16])

/-- Positive weights occupy a full tree's slots. Weight 1 is the deepest
    rank, which has at least two entries and an even population. -/
def Tree.Valid (limits : Limits) (tree : Tree) : Prop :=
  0 < tree.depth ∧ tree.depth ≤ limits.depthCap ∧
    2 ≤ tree.weights.length ∧ tree.weights.length ≤ limits.symbolCap ∧
    (∀ weight ∈ tree.weights, weight ≤ tree.depth) ∧
    mass tree.weights = 2 ^ tree.depth ∧
    2 ≤ tree.weights.count 1 ∧ tree.weights.count 1 % 2 = 0

def CompletionWire (transmitted : List Nat) (tree : Tree) : Prop :=
  ∃ last, tree.weights = transmitted ++ [last] ∧ 0 < last ∧
    2 ^ (tree.depth - 1) ≤ mass transmitted ∧ mass transmitted < 2 ^ tree.depth ∧
    mass transmitted + slots last = 2 ^ tree.depth

def PrefixWire (input : List UInt8) (result : Prefix) : Prop :=
  ∃ header packed,
    input = header :: (packed ++ result.rest) ∧ 128 ≤ header.toNat ∧
      packed.length = packedSize (transmittedCount header) ∧ result.consumed = 1 + packed.length ∧
      CompletionWire ((unpack packed).take (transmittedCount header)) result.tree

namespace Internal

def complete (limits : Limits) (transmitted : List Nat) : Except Error Tree :=
  let total := mass transmitted
  if total = 0 then .error .zeroMass
  else
    let depth := total.log2 + 1
    if limits.depthCap < depth then .error .depthLimit
    else
      let remaining := 2 ^ depth - total
      let last := remaining.log2 + 1
      if slots last ≠ remaining then .error .nonPowerRemainder
      else
        let weights := transmitted ++ [last]
        let deepest := weights.count 1
        if deepest < 2 ∨ deepest % 2 ≠ 0 then .error .invalidDeepestRank
        else .ok ⟨depth, weights⟩

end Internal

/-- Check the prefix and symbol caps before reading packed weights.
    FSE-compressed weight descriptions are explicitly unsupported. -/
def read (limits : Limits) : List UInt8 → Except Error Prefix
  | [] => .error .truncated
  | header :: body =>
    if header.toNat < 128 then .error (.unsupportedFse header.toNat)
    else
      let count := transmittedCount header
      let size := packedSize count
      if limits.byteCap < 1 + size then .error .byteLimit
      else if limits.symbolCap < count + 1 then .error .symbolLimit
      else
        let packed := body.take size
        if packed.length ≠ size then .error .truncated
        else
          (Internal.complete limits ((unpack packed).take count)).map
            (fun tree => ⟨tree, 1 + size, body.drop size⟩)

end Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights
