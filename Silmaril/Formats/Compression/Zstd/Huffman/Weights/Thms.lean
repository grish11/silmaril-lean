module

public import Silmaril.Formats.Compression.Zstd.Huffman.Weights.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.Huffman.Weights.Contracts

public section

namespace Silmaril.Formats.Compression.Zstd.Huffman.Weights

/-- Completion preserves the explicit weights and infers one positive final
    weight. Success certifies the full slot mass, deepest rank and RFC caps. -/
theorem complete_sound {limits : Limits} {transmitted : List Nat} {tree : Tree}
    (success : complete limits transmitted = .ok tree) :
    CompletionWire transmitted tree ∧ Valid limits tree :=
  Proofs.Formats.Compression.Zstd.Huffman.Weights.complete_sound success

/-- Every valid completion of the explicit weight list is returned by the
    checker. Together with soundness, this makes the inferred weight unique. -/
theorem complete_of_valid {limits : Limits} {transmitted : List Nat} {tree : Tree}
    (wire : CompletionWire transmitted tree) (valid : Valid limits tree) :
    complete limits transmitted = .ok tree :=
  Proofs.Formats.Compression.Zstd.Huffman.Weights.complete_of_valid wire valid

end Silmaril.Formats.Compression.Zstd.Huffman.Weights
