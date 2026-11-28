module

import Silmaril.Formats.Parquet.Timestamp.FromIpc.Defs
meta import Silmaril.Formats.Parquet.Timestamp.FromIpc.Defs

open Silmaril Silmaril.Formats

private def input (directory : System.FilePath) (name : String) : IO KBytes := do
  let raw ← IO.FS.readBinFile (directory / (name ++ ".arrows"))
  return KBytes.ofChunks 1 raw.size (raw.data.toList.map UInt8.toNat)

private def expectError (directory : System.FilePath) (name : String)
    (cause : Parquet.Timestamp.FromIpc.Error) : IO Unit := do
  let wire ← input directory name
  match Parquet.Timestamp.FromIpc.convert {} {} wire with
  | .error actual => unless actual == cause do
      throw (IO.userError s!"{name}: unexpected {repr actual}")
  | .ok _ => throw (IO.userError s!"{name}: unexpected output")

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "usage: Emit.lean DIRECTORY")
  let directory : System.FilePath := folder
  for name in ["ms_local", "ms_utc", "us_local", "us_utc", "ns_local", "ns_utc", "schema_only"] do
    let wire ← input directory name
    match Parquet.Timestamp.FromIpc.convert {} {} wire with
    | .ok file => IO.FS.writeBinFile (directory / (name ++ ".parquet")) file.data
    | .error cause => throw (IO.userError s!"{name}: {repr cause}")
  expectError directory "seconds" .seconds
  expectError directory "named" (.timezone "Asia/Kathmandu")
  expectError directory "offset" (.timezone "+00:00")
  expectError directory "empty_timezone" (.timezone "")
  expectError directory "missing_eos" (.source (.batch 4 (.envelope (.malformed .truncated))))
  IO.println "Five typed admission and source refusal checks passed"
