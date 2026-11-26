module

import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Defs
meta import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Defs

/-! Exercise the production checked scanner on bytes emitted by the writer. -/

namespace Silmaril.Formats.Parquet.FlatInt32Writer

private def limits : Limits := ⟨16, 4096, {}, ⟨{}, 32, ⟨64, 64, ⟨16, 32⟩, 0⟩⟩⟩

private def mixed : Input :=
  ⟨3, [⟨"id", .required [-2147483648, 0, 2147483647]⟩,
    ⟨"café", .optional [some 7, none, some (-4)]⟩,
    ⟨"nulls", .optional [none, none, none]⟩]⟩

private def empty : Input :=
  ⟨0, [⟨"id", .required []⟩, ⟨"café", .optional []⟩, ⟨"nulls", .optional []⟩]⟩

private def readBack (input : Input) : Option (List FlatScan.Field × Nat × List (List (Option Int32))) := do
  let output ← (emit limits input).toOption
  let scan ← (FlatScan.scanFileRowGroup (limits.scanLimits input)
    (FlatScan.decodeInt32Page limits.page.scalar) output.bytes 0).toOption
  return (scan.columns.map Prod.fst, scan.rowCount, scan.rows)

private def fields : List FlatScan.Field := [⟨"id", .required⟩, ⟨"café", .optional⟩, ⟨"nulls", .optional⟩]

#guard readBack mixed = some (fields, 3,
  [[some (-2147483648), some 7, none], [some 0, none, none], [some 2147483647, some (-4), none]])
#guard readBack empty = some (fields, 0, [])

end Silmaril.Formats.Parquet.FlatInt32Writer
