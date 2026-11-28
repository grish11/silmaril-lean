module

public import Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.Huffman.DirectWeights.Contracts

public section

namespace Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights

/-- Success identifies the direct description byte for byte, infers the
    positive final weight at the next power of two, and validates the complete
    tree's symbol, depth, mass, and deepest-rank bounds. -/
theorem read_sound {limits : Limits} {input : List UInt8} {result : Prefix}
    (success : read limits input = .ok result) :
    PrefixWire input result ∧ result.tree.Valid limits ∧ result.consumed ≤ limits.byteCap :=
  Proofs.Formats.Compression.Zstd.Huffman.DirectWeights.read_sound success

/-- The bytes after the last packed weight byte are untouched. -/
theorem suffix_exact {input : List UInt8} {result : Prefix} (wire : PrefixWire input result) :
    input.drop result.consumed = result.rest :=
  Proofs.Formats.Compression.Zstd.Huffman.DirectWeights.suffix_exact wire

end Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights
