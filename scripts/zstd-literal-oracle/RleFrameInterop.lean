module

import Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle.Defs
meta import Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle.Defs

open Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle

public def main (args : List String) : IO UInt32 := do
  let [source, target, inputCap, outputCap, windowCap, commandCap] := args
    | throw (IO.userError "usage: RleFrameInterop.lean INPUT OUTPUT INPUT_CAP OUTPUT_CAP WINDOW_CAP COMMAND_CAP")
  let [some inputCap, some outputCap, some windowCap, some commandCap] :=
    [inputCap.toNat?, outputCap.toNat?, windowCap.toNat?, commandCap.toNat?]
    | throw (IO.userError "invalid fixture cap")
  let input := (← IO.FS.readBinFile source).data.toList
  match decode ⟨⟨inputCap, outputCap, windowCap⟩, commandCap⟩ input with
  | .error error =>
    IO.println (reprStr error)
    return 3
  | .ok out =>
    IO.FS.writeBinFile target ⟨out.toArray⟩
    return 0
