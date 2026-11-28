module

/-! # Zstandard Huffman tree completion

RFC 8878 §§4.2.1 and 4.2.1.3. Complete a list of already decoded
weights in symbol order. Zero weights reserve symbol positions without
occupying slots. The inferred positive weight belongs to the final symbol.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.Huffman.Weights

structure Limits where
  symbols : Nat
  depth : Nat
  deriving DecidableEq, Repr

/-- Includes the inferred final weight. -/
def Limits.symbolCap (limits : Limits) : Nat := min limits.symbols 256

def Limits.depthCap (limits : Limits) : Nat := min limits.depth 11

structure Tree where
  depth : Nat
  weights : List Nat
  deriving DecidableEq, Repr

inductive Error where
  | symbolLimit
  | depthLimit
  | zeroMass
  | nonPowerRemainder
  | invalidDeepestRank
  deriving DecidableEq, Repr

def slots (weight : Nat) : Nat := if weight = 0 then 0 else 2 ^ (weight - 1)

def mass (weights : List Nat) : Nat := (weights.map slots).sum

/-- Positive weights occupy a full tree's slots. Weight 1 is the deepest
    rank, which has at least two entries and an even population. -/
def Valid (limits : Limits) (tree : Tree) : Prop :=
  0 < tree.depth ∧ tree.depth ≤ limits.depthCap ∧
    2 ≤ tree.weights.length ∧ tree.weights.length ≤ limits.symbolCap ∧
    (∀ weight ∈ tree.weights, weight ≤ tree.depth) ∧
    mass tree.weights = 2 ^ tree.depth ∧
    2 ≤ tree.weights.count 1 ∧ tree.weights.count 1 % 2 = 0

def CompletionWire (transmitted : List Nat) (tree : Tree) : Prop :=
  ∃ last, tree.weights = transmitted ++ [last] ∧ 0 < last ∧
    2 ^ (tree.depth - 1) ≤ mass transmitted ∧ mass transmitted < 2 ^ tree.depth ∧
    mass transmitted + slots last = 2 ^ tree.depth

/-- Check the input count and each exponent before computing the slot mass. -/
def complete (limits : Limits) (transmitted : List Nat) : Except Error Tree :=
  if limits.symbolCap < 2 ∨ transmitted.drop (limits.symbolCap - 1) ≠ [] then .error .symbolLimit
  else if !(transmitted.all fun weight => decide (weight ≤ limits.depthCap)) then .error .depthLimit
  else
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

end Silmaril.Formats.Compression.Zstd.Huffman.Weights
