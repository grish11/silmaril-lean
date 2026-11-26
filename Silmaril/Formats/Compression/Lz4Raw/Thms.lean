module

public import Silmaril.Formats.Compression.Lz4Raw.Defs
import Silmaril.Proofs.Formats.Compression.Lz4Raw.Sound

/-! # Wire, size and denotation laws for Parquet LZ4_RAW blocks -/

public section

namespace Silmaril.Formats.Compression.Lz4Raw

/-- Parsing accounts for the complete compressed slice and the required
    output length within both caller limits. -/
theorem parse_sound {bounds : Bounds} {input : List UInt8} {block : Block}
    (h : parse bounds input = .ok block) :
    Wire input block ∧ input.length = bounds.compressedSize ∧
      bounds.compressedSize ≤ bounds.compressedLimit ∧
      block.outputSize = bounds.expectedSize ∧ bounds.expectedSize ≤ bounds.outputLimit :=
  Proofs.Formats.Compression.Lz4Raw.parse_sound h

/-- Denotation adds precisely the parsed literal and match lengths. -/
theorem denotes_length {lastMatch : Option Nat} {history out : List UInt8} {block : Block}
    (h : Denotes lastMatch history block out) :
    out.length = history.length + block.outputSize :=
  Proofs.Formats.Compression.Lz4Raw.denotes_length h

/-- A successful decode realizes a valid block of exactly the supplied bytes.
    The denotation starts from empty history and enforces both tail rules.
    Compressed and decoded lengths equal the supplied sizes and respect the caps. -/
theorem decode_sound {bounds : Bounds} {input out : List UInt8}
    (h : decode bounds input = .ok out) :
    ∃ block, Wire input block ∧ Denotes none [] block out ∧
      input.length = bounds.compressedSize ∧ input.length ≤ bounds.compressedLimit ∧
      out.length = bounds.expectedSize ∧ out.length ≤ bounds.outputLimit :=
  Proofs.Formats.Compression.Lz4Raw.decode_sound h

end Silmaril.Formats.Compression.Lz4Raw
