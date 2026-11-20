module

import Silmaril.Wasm.Perf.CoreDecode.Defs

open Silmaril.Wasm

public def main (args : List String) : IO Unit := do
  let [mode, path] := args | throw (IO.userError "expected reference|fast INPUT")
  let decode ← match mode with
    | "reference" => pure Binary.Core.decode?
    | "fast" => pure Perf.CoreDecode.decodeF
    | _ => throw (IO.userError s!"unknown reader: {mode}")
  let bytes ← IO.FS.readBinFile path
  let start ← IO.monoNanosNow
  let some result := decode bytes | throw (IO.userError "decoder rejected source")
  let finish ← IO.monoNanosNow
  IO.println s!"native_ns {finish - start}"
  IO.println s!"functions={result.funcs.length} data_segments={result.data.length}"
