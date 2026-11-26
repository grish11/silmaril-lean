module

public import Silmaril.Formats.Compression.Zstd.Huffman.FseWeights.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.Huffman.FseWeights.Contracts
import Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix.Thms

public section

namespace Silmaril.Formats.Compression.Zstd.Huffman.FseWeights

/-- Success witnesses the exact prefix and interleaved weight trace, with both
    output bounds and the checked weight alphabet. -/
theorem read_sound {byteLimit weightLimit : Nat} {input : List UInt8} {result : Prefix}
    (success : read byteLimit weightLimit input = .ok result) :
    Wire input result ∧ result.consumed ≤ min byteLimit 128 ∧
      2 ≤ result.weights.length ∧ result.weights.length ≤ weightCap weightLimit ∧
      ∀ weight ∈ result.weights, weight < 12 :=
  Proofs.Formats.Compression.Zstd.Huffman.FseWeights.read_sound success

/-- The initialized states and remaining bits determine the emitted weights. -/
theorem emits_unique {table : FseTable.Table} {active waiting : Nat} {bits : List Bit}
    {left right : List Nat} (hleft : Emits table active waiting bits left)
    (hright : Emits table active waiting bits right) : left = right :=
  Proofs.Formats.Compression.Zstd.Huffman.FseWeights.emits_unique hleft hright

theorem suffix_exact {input : List UInt8} {result : Prefix} (wire : Wire input result) :
    input.drop result.consumed = result.rest := by
  obtain ⟨_, provenance, consumed, rest, _⟩ := wire
  rw [consumed, rest]
  exact FsePrefix.suffix_exact provenance

end Silmaril.Formats.Compression.Zstd.Huffman.FseWeights
