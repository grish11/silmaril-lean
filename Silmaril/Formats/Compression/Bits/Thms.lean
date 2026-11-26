module

public import Silmaril.Formats.Compression.Bits.BitstreamLemmas
import Silmaril.Proofs.Formats.Compression.Bits.Reader
import Silmaril.Raw.Formats.Compression.Bits.BitstreamLemmas

public section

namespace Silmaril.Formats.Compression

theorem natBits_length (value width : Nat) : (natBits value width).length = width :=
  length_natBits value width

theorem natBits_zero_fill (width : Nat) : natBits 0 width = List.replicate width false :=
  natBits_zero width

/-- A successful little-endian read consumes the exact specified bit prefix
    and records its cursor advance and residual position within a byte. -/
theorem LSBReader.readBits_sound {width : Nat} {before after : LSBReader} {bits : List Bool} {value : Nat}
    (rep : before.Rep bits) (count : before.count < 8)
    (read : before.readBits width = some (value, after)) :
    ∃ tail, bits = natBits value width ++ tail ∧ after.Rep tail ∧ value < 2 ^ width ∧
      after.totalRead = before.totalRead + width ∧ after.count = (before.count + 7 * width) % 8 :=
  Proofs.Formats.Compression.Bits.readBits_sound rep count read

end Silmaril.Formats.Compression
