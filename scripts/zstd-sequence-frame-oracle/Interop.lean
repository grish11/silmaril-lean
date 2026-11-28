module

import Silmaril.Formats.Compression.Zstd.CheckedFrame.Sequences.Defs
meta import Silmaril.Formats.Compression.Zstd.CheckedFrame.Sequences.Defs

open Silmaril.Formats.Compression.Zstd.CheckedFrame.Sequences

public def main (args : List String) : IO UInt32 := do
  let [source, destination, input, output, window, commands] := args | return 2
  let [some i, some o, some w, some c] := [input, output, window, commands].map String.toNat? | return 2
  let bytes := (← IO.FS.readBinFile source).data.toList
  match decode ⟨⟨i, o, w⟩, c⟩ bytes with
  | .error reason =>
    IO.println (reprStr reason)
    return 3
  | .ok decoded =>
    IO.FS.writeBinFile destination ⟨decoded.toArray⟩
    return 0
