module

import Silmaril.Formats.Compression.Zstd.SequenceTables.Repeat.Defs
import Silmaril.Formats.Compression.Zstd.RleSequences.Defs
meta import Silmaril.Formats.Compression.Zstd.SequenceTables.Repeat.Defs
meta import Silmaril.Formats.Compression.Zstd.RleSequences.Defs

open Silmaril.Formats.Compression.Zstd
open SequenceTables (Table)
open SequenceTables.Repeat

private def printTable (alphabet : FseTable.Alphabet) (table : Table) : IO Unit := do
  let (log, rows) : Nat × List FseTable.Row := match table with
    | .rle symbol => (0, [⟨symbol, 0, 0⟩])
    | .fse table => (table.log, table.rows)
  IO.println log
  for row in rows do
    let some code := (match alphabet with
      | .literalLength => RleSequences.literalCode row.symbol
      | .matchLength => RleSequences.matchCode row.symbol
      | .offset =>
        -- libzstd adjusts Offset_Value's base before interpreting the extra bits.
        some ⟨2 ^ row.symbol - (if row.symbol < 2 then 1 else 3), row.symbol⟩)
      | throw (IO.userError "invalid table symbol")
    IO.println s!"{row.baseline} {row.bits} {code.base} {code.width}"

public def main (files : List String) : IO UInt32 := do
  let mut state := State.empty
  for file in files do
    let input ← IO.FS.readBinFile file
    match resolve ⟨131072, 1⟩ state input.data.toList with
    | .error reason =>
      IO.println (reprStr reason)
      return 3
    | .ok (result, next) =>
      let suffix := result.bitstream
      IO.println s!"{input.size - suffix.length} {result.count}"
      match result with
      | .empty => pure ()
      | .coded _ tables _ =>
        printTable .literalLength tables.literalLength
        printTable .offset tables.offset
        printTable .matchLength tables.matchLength
      IO.println s!"suffix {String.intercalate " " (suffix.map fun byte => toString byte.toNat)}"
      IO.println ""
      state := next
  return 0
