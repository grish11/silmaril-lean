module

public import Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.Huffman.TreeDescription.Contracts
import Silmaril.Formats.Compression.Zstd.Huffman.Weights.Thms

public section

namespace Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription

/-- The selected wire encoding determines the completed tree and preserves
    its branch-specific depth, byte and symbol caps. -/
theorem read_sound {limits : Limits} {input : List UInt8} {result : Prefix}
    (success : read limits input = .ok result) : result.Valid limits input :=
  Proofs.Formats.Compression.Zstd.Huffman.TreeDescription.read_sound success

/-- Table construction preserves the checked prefix and canonical placement. -/
theorem readTable_sound {limits : Limits} {input : List UInt8} {result : Prefix} {table : SingleStream.Table}
    (success : readTable limits input = .ok (result, table)) :
    read limits input = .ok result ∧ result.Valid limits input ∧ SingleStream.TableWire result.tree table :=
  Proofs.Formats.Compression.Zstd.Huffman.TreeDescription.readTable_sound success

theorem suffix_exact {input : List UInt8} {result : Prefix} (wire : Wire input result) :
    input.drop result.consumed = result.rest :=
  Proofs.Formats.Compression.Zstd.Huffman.TreeDescription.suffix_exact wire

/-- Stripping the inferred weight recovers the transmitted weights from
    either encoding, with the shared last-weight and slot-mass relation. -/
theorem completion_wire {input : List UInt8} {result : Prefix} (wire : Wire input result) :
    Weights.CompletionWire result.transmitted result.tree :=
  Proofs.Formats.Compression.Zstd.Huffman.TreeDescription.completion_wire wire

/-- The transmitted weights admit a unique valid completion. -/
theorem tree_unique {limits : Limits} {input : List UInt8} {result : Prefix} {other : Weights.Tree}
    (valid : result.Valid limits input) (completion : Weights.CompletionWire result.transmitted other)
    (otherValid : Weights.Valid (limits.treeLimits result.mode) other) : other = result.tree :=
  Except.ok.inj ((Weights.complete_of_valid completion otherValid).symm.trans
    (Weights.complete_of_valid (completion_wire valid.1) valid.2.1))

end Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription
