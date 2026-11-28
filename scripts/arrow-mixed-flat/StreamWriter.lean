module

import Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Examples
meta import Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Examples

open Silmaril.Formats.Arrow.MixedFlat.StreamWriter

public def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: StreamWriter.lean DIR")
  IO.FS.createDirAll directory
  for (name, schema, batches) in Examples.cases do
    match emit {} schema batches with
    | .error failure => throw (IO.userError s!"{name}: {repr failure}")
    | .ok bytes =>
      IO.FS.writeBinFile (System.FilePath.mk directory / (name ++ ".arrow")) bytes.toByteArray
