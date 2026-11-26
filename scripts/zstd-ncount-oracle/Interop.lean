module

import Silmaril.Formats.Compression.Zstd.FseTable.NCount.Defs
meta import Silmaril.Formats.Compression.Zstd.FseTable.NCount.Defs

open Silmaril.Formats.Compression.Zstd.FseTable
open Silmaril.Formats.Compression.Zstd.FseTable.NCount

public def main (args : List String) : IO UInt32 := do
  let [source, remainder, byteCap, symbolCap, logCap, expected] := args
    | throw (IO.userError "usage: Interop.lean INPUT REMAINDER BYTE_CAP SYMBOL_CAP LOG_CAP EXPECTED")
  let [some byteCap, some symbolCap, some logCap] := [byteCap.toNat?, symbolCap.toNat?, logCap.toNat?]
    | throw (IO.userError "invalid fixture cap")
  let limits : NCount.Limits := ⟨⟨logCap, symbolCap⟩, byteCap, expected.toNat?⟩
  let input := (← IO.FS.readBinFile source).data.toList
  match readTable limits input with
  | .error error =>
    IO.println (reprStr error)
    return 3
  | .ok (result, table) =>
    let weights := result.distribution.weights
    IO.FS.writeBinFile remainder ⟨result.rest.toArray⟩
    IO.println result.bits
    IO.println s!"{result.bytes} {table.log} {weights.length}"
    IO.println (String.intercalate " " (weights.map toString))
    for row in table.rows do
      IO.println s!"{row.symbol} {row.bits} {row.baseline}"
    return 0
