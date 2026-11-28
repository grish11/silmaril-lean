module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc

private def expectError (label : String) (expected : Error) (result : Except Error KBytes) : IO Unit := do
  match result with
  | .error actual => unless actual == expected do
      throw (IO.userError s!"{label}: unexpected error {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected complete stream")

private def input (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map fun raw => ⟨raw⟩

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "usage: Emit.lean DIRECTORY")
  let directory : System.FilePath := folder
  for name in ["ms_local", "ms_utc", "us_local", "us_utc", "ns_local", "ns_utc"] do
    let wire ← input directory name
    match convert {} {} wire 1 with
    | .error cause => throw (IO.userError s!"{name}: {repr cause}")
    | .ok output => IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray

  let v1 ← input directory "v1-selected"
  match convert {} {} v1 5 with
  | .error cause => throw (IO.userError s!"V1 selected column: {repr cause}")
  | .ok output => IO.FS.writeBinFile (directory / "v1-selected.arrows") output.toByteArray

  let good ← input directory "us_local"
  let bad ← input directory "damaged"
  let two ← input directory "damaged_twice"
  expectError "root selection" (.source (.openFailure (.annotation .notInt64Leaf)))
    (convert {} {} good 0)
  expectError "non-timestamp decoy" (.source (.openFailure (.annotation .notInt64Leaf)))
    (convert {} {} v1 1)
  expectError "file bound" (.fileByteLimit (good.length - 1) good.length)
    (convert { maxFileBytes := good.length - 1 } {} good 1)
  expectError "group bound counts empty groups" (.groupLimit 2 3)
    (convert { maxGroups := 2 } {} good 1)
  expectError "input row bound" (.rowLimit 5 6)
    (convert { maxTotalRows := 5 } {} good 1)
  expectError "output batch bound counts empty groups" (.writer (.writer (.limit .batches)))
    (convert {} { ipc.batches := 2 } good 1)
  expectError "output row bound" (.writer (.writer (.limit .totalRows)))
    (convert {} { totalRows := 5 } good 1)
  expectError "late source error before output admission"
    (.source (.groupFailure 2 (.page 0 (.scalar (.unsupportedEncoding 8)))))
    (convert {} { ipc.fields := 0 } bad 1)
  expectError "earliest damaged group"
    (.source (.groupFailure 0 (.page 0 (.scalar (.unsupportedEncoding 5)))))
    (convert {} { ipc.batches := 0 } two 1)
  IO.println "Nine typed refusal and precedence checks passed"
