module

public import Silmaril.Formats.Compression.Zstd.FseTable.NCount.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.FseTable.NCount.Contracts

public section

namespace Silmaril.Formats.Compression.Zstd.FseTable.NCount

/-- The reader consumes exactly the bytes touched by the normalized fields,
    preserves their byte suffix, and validates the distribution and limits. -/
theorem read_sound {limits : Limits} {input : List UInt8} {result : Prefix}
    (success : read limits input = .ok result) : result.Valid limits input :=
  Proofs.Formats.Compression.Zstd.FseTable.NCount.read_sound success

/-- The constructed table denotes the exact transmitted distribution and
    retains the checked prefix and suffix. -/
theorem readTable_sound {limits : Limits} {input : List UInt8} {result : Prefix} {table : Table}
    (success : readTable limits input = .ok (result, table)) :
    result.Valid limits input ∧ TableWire result.distribution table ∧ table.WellFormed result.distribution :=
  Proofs.Formats.Compression.Zstd.FseTable.NCount.readTable_sound success

end Silmaril.Formats.Compression.Zstd.FseTable.NCount
