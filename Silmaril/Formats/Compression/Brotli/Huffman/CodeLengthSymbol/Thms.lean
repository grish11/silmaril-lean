module

public import Silmaril.Formats.Compression.Brotli.Huffman.CodeLengthSymbol.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Huffman.CodeLengthSymbol.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.Huffman.CodeLengthSymbol

/-- Only the checked code's bits are consumed. The exact suffix remains
    at the returned cursor under both the caller and code-depth bounds. -/
theorem read_sound {table : CodeLengths.Table} {limit symbol : Nat}
    {before after : LSBReader} {input : List Bool} (rep : before.Rep input) (count : before.count < 8)
    (checked : read table limit before = .ok (symbol, after)) :
    ∃ used suffix, Wire table symbol used ∧ input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ limit ∧ used.length ≤ 5 :=
  Proofs.Formats.Compression.Brotli.Huffman.CodeLengthSymbol.read_sound rep count checked

end Silmaril.Formats.Compression.Brotli.Huffman.CodeLengthSymbol
