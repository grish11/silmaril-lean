module

import Silmaril.Formats.Compression.Zstd.SequenceTables.Defs
import Silmaril.Formats.Compression.Zstd.RleSequences.Defs
meta import Silmaril.Formats.Compression.Zstd.SequenceTables.Defs
meta import Silmaril.Formats.Compression.Zstd.RleSequences.Defs

open Silmaril.Formats.Compression.Zstd
open SequenceTables

private def oracleCode (alphabet : FseTable.Alphabet) (symbol : Nat) : Option RleSequences.Code :=
  match alphabet with
  | .literalLength => RleSequences.literalCode symbol
  | .matchLength => RleSequences.matchCode symbol
  -- The native table pre-adjusts the offset base before interpreting extra bits.
  | .offset => some ⟨2 ^ symbol - (if symbol < 2 then 1 else 3), symbol⟩

private def printTable (alphabet : FseTable.Alphabet) (table : Table) : IO Unit := do
  let (log, rows) : Nat × List FseTable.Row := match table with
    | .rle symbol => (0, [⟨symbol, 0, 0⟩])
    | .fse table => (table.log, table.rows)
  IO.println log
  for row in rows do
    let some code := oracleCode alphabet row.symbol | throw (IO.userError "invalid table symbol")
    IO.println s!"{row.baseline} {row.bits} {code.base} {code.width}"

public def main (args : List String) : IO UInt32 := do
  let [file, tailFile, bytes, count] := args | return 2
  let some bytes := bytes.toNat? | return 2
  let some count := count.toNat? | return 2
  let input ← IO.FS.readBinFile file
  match resolve ⟨bytes, count⟩ input.data.toList with
  | .error reason =>
    IO.println (repr reason)
    return 3
  | .ok result =>
    let tail := result.bitstream
    IO.FS.writeBinFile tailFile ⟨tail.toArray⟩
    IO.println s!"{input.size - tail.length} {result.count}"
    match result with
    | .empty => pure ()
    | .coded _ tables _ =>
      printTable .literalLength tables.literalLength
      printTable .offset tables.offset
      printTable .matchLength tables.matchLength
    return 0
