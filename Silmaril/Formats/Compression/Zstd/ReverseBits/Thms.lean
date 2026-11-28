module

public import Silmaril.Formats.Compression.Zstd.ReverseBits.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.ReverseBits.Contracts

public section

namespace Silmaril.Formats.Compression.Zstd.ReverseBits

/-- The cursor measures exactly the number of unread bits. -/
theorem bits_length (cursor : Cursor) : cursor.bits.length = cursor.remaining :=
  Proofs.Formats.Compression.Zstd.ReverseBits.bits_length cursor

theorem isEmpty_iff (cursor : Cursor) : cursor.isEmpty = true ↔ cursor.bits = [] :=
  Proofs.Formats.Compression.Zstd.ReverseBits.isEmpty_iff cursor

/-- Success identifies the highest set bit of the actual final byte. -/
theorem start_sound {input : List UInt8} {cursor : Cursor}
    (success : start input = some cursor) : StartWire input cursor :=
  Proofs.Formats.Compression.Zstd.ReverseBits.start_sound success

/-- A successful read consumes exactly the requested field, with the expected
    bit order, numeric range and remaining-width algebra. -/
theorem read_sound {width value : Nat} {cursor rest : Cursor}
    (success : read width cursor = some (value, rest)) :
    ∃ field, cursor.bits = field ++ rest.bits ∧ field.length = width ∧
      value = Bit.bitsToNatMSB field ∧ value < 2 ^ width ∧
      cursor.remaining = width + rest.remaining :=
  Proofs.Formats.Compression.Zstd.ReverseBits.read_sound success

end Silmaril.Formats.Compression.Zstd.ReverseBits
