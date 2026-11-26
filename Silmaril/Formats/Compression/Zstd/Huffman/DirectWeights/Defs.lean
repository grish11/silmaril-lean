module

public import Silmaril.Formats.Compression.Zstd.Huffman.Weights.Defs

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

def Limits.weightLimits (limits : Limits) : Weights.Limits := ⟨min limits.symbols 129, limits.depth⟩

/-- Includes the symbol whose weight is inferred. -/
def Limits.symbolCap (limits : Limits) : Nat := limits.weightLimits.symbolCap

def Limits.depthCap (limits : Limits) : Nat := limits.weightLimits.depthCap

abbrev Tree := Weights.Tree

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

abbrev slots := Weights.slots

abbrev mass := Weights.mass

def transmittedCount (header : UInt8) : Nat := header.toNat - 127

def packedSize (count : Nat) : Nat := (count + 1) / 2

/-- The high nibble precedes the low nibble. The caller takes just the
    transmitted symbol count, skipping the low padding nibble if odd. -/
def unpack (bytes : List UInt8) : List Nat :=
  bytes.flatMap (fun byte => [byte.toNat / 16, byte.toNat % 16])

def Tree.Valid (limits : Limits) (tree : Tree) : Prop := Weights.Valid limits.weightLimits tree

abbrev CompletionWire := Weights.CompletionWire

def PrefixWire (input : List UInt8) (result : Prefix) : Prop :=
  ∃ header packed,
    input = header :: (packed ++ result.rest) ∧ 128 ≤ header.toNat ∧
      packed.length = packedSize (transmittedCount header) ∧ result.consumed = 1 + packed.length ∧
      CompletionWire ((unpack packed).take (transmittedCount header)) result.tree

namespace Internal

def completionError : Weights.Error → Error
  | .symbolLimit => .symbolLimit
  | .depthLimit => .depthLimit
  | .zeroMass => .zeroMass
  | .nonPowerRemainder => .nonPowerRemainder
  | .invalidDeepestRank => .invalidDeepestRank

def complete (limits : Limits) (transmitted : List Nat) : Except Error Tree :=
  (Weights.complete limits.weightLimits transmitted).mapError completionError

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
