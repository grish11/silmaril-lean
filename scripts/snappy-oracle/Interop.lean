module

import Silmaril.Formats.Compression.Snappy.Defs
meta import Silmaril.Formats.Compression.Snappy.Defs

open Silmaril.Formats.Compression.Snappy

public def main (args : List String) : IO Unit := do
  let [mode, source, target] := args
    | throw (IO.userError "usage: Interop.lean encode|decode INPUT OUTPUT")
  let bytes := (← IO.FS.readBinFile source).data.toList
  let result ← match mode with
    | "encode" => pure (encode bytes)
    | "decode" => pure (decode 1048576 bytes)
    | _ => throw (IO.userError "unknown mode")
  match result with
  | .ok out => IO.FS.writeBinFile target ⟨out.toArray⟩
  | .error reason => throw (IO.userError (reprStr reason))
