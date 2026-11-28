module

import Silmaril.Formats.Compression.Zstd.SequenceDecode.Defs
meta import Silmaril.Formats.Compression.Zstd.SequenceDecode.Defs

open Silmaril.Formats.Compression.Zstd.SequenceDecode

public def main (args : List String) : IO UInt32 := do
  let [path, bytes, count] := args | return 2
  let some bytes := bytes.toNat? | return 2
  let some count := count.toNat? | return 2
  let input := (← IO.FS.readBinFile path).data.toList
  match decode ⟨bytes, count⟩ input with
  | .error reason =>
    IO.println (reprStr reason)
    return 3
  | .ok commands =>
    for command in commands do
      IO.println s!"{command.literalLength} {command.offsetValue} {command.matchLength}"
    return 0
