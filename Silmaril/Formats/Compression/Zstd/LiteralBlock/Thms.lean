module

public import Silmaril.Formats.Compression.Zstd.LiteralBlock.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.LiteralBlock.Contracts

/-! # Wire and bounds of literal-only Zstandard compressed blocks -/

public section

namespace Silmaril.Formats.Compression.Zstd.LiteralBlock

/-- Parsing a literal section leaves the sequence bytes and checks the
    regenerated literal size before any expansion. -/
theorem parseLiterals_sound {limit : Nat} {input rest : List UInt8} {literals : Literals}
    (h : parseLiterals limit input = .ok (literals, rest)) :
    LiteralsWire input literals rest ∧ literals.size ≤ limit :=
  Proofs.Formats.Compression.Zstd.LiteralBlock.parseLiterals_sound h

/-- The bounded plain reader witnesses the exact encoded prefix and both limits. -/
theorem parseLiteralsBounded_sound {inputLimit outputLimit : Nat} {input : List UInt8} {result : Prefix}
    (h : parseLiteralsBounded inputLimit outputLimit input = .ok result) :
    result.Wire input ∧ result.consumed ≤ inputLimit ∧ result.literals.size ≤ outputLimit :=
  Proofs.Formats.Compression.Zstd.LiteralBlock.parseLiteralsBounded_sound h

/-- The count parser consumes only the count field, in one of its three forms. -/
theorem readSequenceCount_sound {input rest : List UInt8} {count : Nat}
    (h : readSequenceCount input = .ok (count, rest)) :
    ∃ encoded, input = encoded ++ rest ∧ SequenceCountWire encoded count :=
  Proofs.Formats.Compression.Zstd.LiteralBlock.readSequenceCount_sound h

/-- A successful block consumes exactly the literal section and a zero
    sequence count. Both sizes respect the frame maximum, and the output
    also respects the caller's additional limit. -/
theorem decode_sound {header : Header} {limit : Nat} {input out : List UInt8}
    (h : decode header limit input = .ok out) :
    ∃ literals, BlockWire input literals ∧ literals.expand = out ∧
      input.length ≤ blockMaximum header ∧
      out.length ≤ blockMaximum header ∧ out.length ≤ limit :=
  Proofs.Formats.Compression.Zstd.LiteralBlock.decode_sound h

end Silmaril.Formats.Compression.Zstd.LiteralBlock
