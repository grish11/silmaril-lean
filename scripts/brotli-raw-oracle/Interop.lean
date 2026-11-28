module

import Silmaril.Formats.Compression.Brotli.Defs
meta import Silmaril.Formats.Compression.Brotli.Defs

open Silmaril.Formats.Compression.Brotli

public def main (args : List String) : IO UInt32 := do
  let [input, output, inputCap, outputCap, windowCap, steps] := args | return 2
  let (some i, some o, some w, some s) := (inputCap.toNat?, outputCap.toNat?, windowCap.toNat?, steps.toNat?)
    | return 2
  let source ← IO.FS.readBinFile input
  match decode ⟨i, o, w, s⟩ source.data.toList with
  | .ok bytes =>
    IO.FS.writeBinFile output ⟨bytes.toArray⟩
    return 0
  | .error error =>
    IO.println (reprStr error)
    return 3
