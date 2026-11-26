module

public import Silmaril.Formats.Compression.Zstd.Huffman.FourStream.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.Huffman.FourStream.Contracts

public section

namespace Silmaril.Formats.Compression.Zstd.Huffman.FourStream

/-- Success consumes the declared bytes in wire order, checks all four
    extents, and assigns the RFC regenerated symbol quotas. -/
theorem split_sound {limits : Limits} {declared regenerated : Nat} {input : List UInt8}
    {parts : Split} (success : split limits declared regenerated input = .ok parts) :
    input.length = declared ∧ declared ≤ limits.inputBytes ∧ regenerated ≤ limits.outputSymbols ∧
      ExtentsWire declared input parts ∧ CountsWire regenerated parts :=
  Proofs.Formats.Compression.Zstd.Huffman.FourStream.split_sound success

/-- The fourth quota can be up to three symbols shorter. -/
theorem fourth_bounds {regenerated : Nat} {parts : Split} (wire : CountsWire regenerated parts) :
    parts.fourth.symbols ≤ segmentSize regenerated ∧
      segmentSize regenerated ≤ parts.fourth.symbols + 3 := by
  obtain ⟨_, _, _, _, _, last⟩ := wire
  unfold segmentSize at *
  omega

/-- One checked table denotes all four streams. Each stream exhausts its
    own bytes and the joined output has the exact regenerated size. -/
theorem decode_sound {limits : Limits} {treeLimits : DirectWeights.Limits} {tree : DirectWeights.Tree}
    {declared regenerated : Nat} {input out : List UInt8}
    (success : decode limits treeLimits tree declared regenerated input = .ok out) :
    input.length = declared ∧ declared ≤ limits.inputBytes ∧
      out.length = regenerated ∧ regenerated ≤ limits.outputSymbols ∧
      tree.Valid treeLimits ∧ ∃ parts table output, ExtentsWire declared input parts ∧
        CountsWire regenerated parts ∧ SingleStream.TableWire tree table ∧
        ChunksWire table parts.chunks output ∧ out = output.flatten :=
  Proofs.Formats.Compression.Zstd.Huffman.FourStream.decode_sound success

end Silmaril.Formats.Compression.Zstd.Huffman.FourStream
