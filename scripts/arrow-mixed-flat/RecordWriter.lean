module

import Silmaril.Formats.Arrow.MixedFlat.Writer.Examples
meta import Silmaril.Formats.Arrow.MixedFlat.Writer.Examples
import Silmaril.Formats.Arrow.StreamWriter.Defs
meta import Silmaril.Formats.Arrow.StreamWriter.Defs

open Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.MixedFlat.Writer

public def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: RecordWriter.lean DIR")
  IO.FS.createDirAll directory
  for (name, input) in Examples.cases do
    match emit {} input with
    | .error failure => throw (IO.userError s!"{name}: {repr failure}")
    | .ok output =>
      let envelope := StreamWriter.envelopeBytes output.metadataBytes.len
      let message := envelope ++ (output.metadataBytes ++ output.body)
      IO.FS.writeBinFile (System.FilePath.mk directory / (name ++ ".arrow")) message.toByteArray
