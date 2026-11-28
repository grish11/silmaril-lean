module

import Silmaril.Formats.Compression.Zstd.LiteralBlock.Defs
meta import Silmaril.Formats.Compression.Zstd.LiteralBlock.Defs

open Silmaril.Formats.Compression.Zstd (Header)
open Silmaril.Formats.Compression.Zstd.LiteralBlock

public def main (args : List String) : IO UInt32 := do
  let [source, target, window, limit] := args
    | throw (IO.userError "usage: Interop.lean INPUT OUTPUT WINDOW OUTPUT_LIMIT")
  let some window := window.toNat? | throw (IO.userError "invalid window")
  let some limit := limit.toNat? | throw (IO.userError "invalid output limit")
  let header : Header := ⟨window, false, false, 0, none⟩
  let input := (← IO.FS.readBinFile source).data.toList
  match decode header limit input with
  | .ok out => IO.FS.writeBinFile target ⟨out.toArray⟩; return 0
  | .error err => IO.println (reprStr err); return 3
