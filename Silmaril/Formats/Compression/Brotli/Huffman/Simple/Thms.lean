module

public import Silmaril.Formats.Compression.Brotli.Huffman.Simple.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Huffman.Simple.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.Huffman.Simple

/-- This is the smallest field width that covers the full alphabet. -/
theorem alphabetWidth_minimal {alphabet : Nat} (positive : 0 < alphabet) :
    alphabet ≤ 2 ^ alphabetWidth alphabet ∧ ∀ k < alphabetWidth alphabet, 2 ^ k < alphabet :=
  Proofs.Formats.Compression.Brotli.Huffman.Simple.alphabetWidth_minimal positive

theorem Wire.bit_bound {alphabet : Nat} {body : List Bool} {shape : Shape}
    (wire : Wire alphabet body shape) (fits : alphabet ≤ 704) : body.length ≤ 43 :=
  Proofs.Formats.Compression.Brotli.Huffman.Simple.Wire.bit_bound wire fits

/-- The returned shape uses the exact original symbol order and optional
    tree bit, with an unchanged bit-level suffix under the caller cap. -/
theorem read_sound {alphabet limit : Nat} {before after : LSBReader}
    {input : List Bool} {checked : Checked alphabet} (rep : before.Rep input) (count : before.count < 8)
    (read : read alphabet limit before = .ok (checked, after)) :
    ∃ used suffix, Wire alphabet used checked.shape ∧ input = used ++ suffix ∧ after.Rep suffix ∧
      after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧ used.length ≤ limit :=
  Proofs.Formats.Compression.Brotli.Huffman.Simple.read_sound rep count read

end Silmaril.Formats.Compression.Brotli.Huffman.Simple
