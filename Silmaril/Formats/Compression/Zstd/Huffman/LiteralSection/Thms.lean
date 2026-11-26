module

public import Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.Huffman.LiteralSection.Contracts

public section

namespace Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection

/-- A successful header consumes exactly the bytes specified by its size
    format and identifies both little-endian sizes. -/
theorem readHeader_sound {input body : List UInt8} {header : Header}
    (success : readHeader input = .ok (header, body)) :
    ∃ bytes, input = bytes ++ body ∧ header.Wire bytes :=
  Proofs.Formats.Compression.Zstd.Huffman.LiteralSection.readHeader_sound success

/-- Success witnesses the exact header, tree and stream partition. The
    regenerated size is exact and both caller caps hold. -/
theorem read_sound {limits : Limits} {input : List UInt8} {result : Prefix}
    (success : read limits input = .ok result) :
    Wire limits input result ∧ result.consumed ≤ limits.inputCap ∧
      result.literals.length = result.header.regenerated ∧ result.header.regenerated ≤ limits.outputCap :=
  Proofs.Formats.Compression.Zstd.Huffman.LiteralSection.read_sound success

theorem suffix_exact {limits : Limits} {input : List UInt8} {result : Prefix}
    (wire : Wire limits input result) : input.drop result.consumed = result.rest :=
  Proofs.Formats.Compression.Zstd.Huffman.LiteralSection.suffix_exact wire

end Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection
