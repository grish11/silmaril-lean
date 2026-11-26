module

import Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix.Defs
meta import Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix.Defs

open Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix

public def main (args : List String) : IO UInt32 := do
  let [source, destination, byteLimit] := args | return 2
  let some cap := byteLimit.toNat? | return 2
  let input := (← IO.FS.readBinFile source).data.toList
  match read cap input with
  | .error reason =>
    IO.println (reprStr reason)
    return 3
  | .ok result =>
    let setup := result.setup
    IO.FS.writeBinFile destination ⟨result.rest.toArray⟩
    IO.println s!"{result.consumed} {setup.counts.bytes} {setup.table.log} {setup.states.first} {setup.states.second} {setup.cursor.remaining}"
    IO.println (String.intercalate " " (setup.counts.distribution.weights.map toString))
    for row in setup.table.rows do
      IO.println s!"{row.symbol} {row.bits} {row.baseline}"
    IO.println (String.ofList (setup.cursor.bits.map fun bit => if bit then '1' else '0'))
    return 0
