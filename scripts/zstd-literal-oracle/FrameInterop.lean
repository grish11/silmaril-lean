module

import Silmaril.Formats.Compression.Zstd.CheckedFrame.Defs
meta import Silmaril.Formats.Compression.Zstd.CheckedFrame.Defs

open Silmaril.Formats.Compression.Zstd.CheckedFrame

public def main (args : List String) : IO UInt32 := do
  let [source, target, maxInput, maxOutput, maxWindow] := args
    | throw (IO.userError "usage: FrameInterop.lean INPUT OUTPUT INPUT_LIMIT OUTPUT_LIMIT WINDOW_LIMIT")
  let some maxInput := maxInput.toNat? | throw (IO.userError "invalid input limit")
  let some maxOutput := maxOutput.toNat? | throw (IO.userError "invalid output limit")
  let some maxWindow := maxWindow.toNat? | throw (IO.userError "invalid window limit")
  let input := (← IO.FS.readBinFile source).data.toList
  match decode ⟨maxInput, maxOutput, maxWindow⟩ input with
  | .ok out =>
    IO.FS.writeBinFile target ⟨out.toArray⟩
    return 0
  | .error err =>
    IO.println (reprStr err)
    return 3
