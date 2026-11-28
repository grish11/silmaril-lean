module

import Silmaril.Formats.Compression.Zstd.CompressedBlock.Defs
meta import Silmaril.Formats.Compression.Zstd.CompressedBlock.Defs

open Silmaril.Formats.Compression.Zstd.CompressedBlock

private def printBytes (bytes : List UInt8) : IO Unit :=
  IO.println s!"ok {String.intercalate " " (bytes.map fun byte => toString byte.toNat)}"

public def main (args : List String) : IO UInt32 := do
  let mut state := State.initial
  let limits : Limits := ⟨1024, 1024, 1024, 32⟩
  for arg in args do
    let [action, path] := arg.splitOn "=" | return 2
    let body ← IO.FS.readBinFile path
    let bytes := body.data.toList
    if action == "plain" then
      state := state.advancePlain limits.window bytes
      printBytes bytes
    else
      match decode limits state bytes.length bytes with
      | .error reason =>
        IO.println ("error " ++ (reprStr reason).replace "\n" " ")
        if action != "reject" then return 3
      | .ok result =>
        if action == "reject" then return 4
        state := result.next
        printBytes result.bytes
  return 0
