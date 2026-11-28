module

public import Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.Huffman.FsePrefix.Contracts

public section

namespace Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix

/-- A successful prefix accounts for the exact description and both state
    fields, validates their shared table and bounds, and retains the reverse
    bit remainder and the literal-byte suffix. -/
theorem read_sound {byteLimit : Nat} {input : List UInt8} {result : Prefix}
    (success : read byteLimit input = .ok result) :
    PrefixWire input result ∧ result.consumed ≤ min byteLimit 128 :=
  Proofs.Formats.Compression.Zstd.Huffman.FsePrefix.read_sound success

/-- Dropping the complete weight description leaves the unmodified literal bytes. -/
theorem suffix_exact {input : List UInt8} {result : Prefix} (wire : PrefixWire input result) :
    input.drop result.consumed = result.rest :=
  Proofs.Formats.Compression.Zstd.Huffman.FsePrefix.suffix_exact wire

end Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix
