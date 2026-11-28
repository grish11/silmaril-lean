module

import Silmaril.Formats.Parquet.Timestamp.RoundTrip.Defs
meta import Silmaril.Formats.Parquet.Timestamp.RoundTrip.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp

private def convert (directory : System.FilePath) (name : String) : IO (Except FromIpc.Error Bytes) := do
  let raw ← IO.FS.readBinFile (directory / (name ++ ".arrows"))
  return FromIpc.convert {} {} (KBytes.ofChunks 1 raw.size (raw.data.toList.map UInt8.toNat))

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "usage: Emit.lean DIRECTORY")
  let directory : System.FilePath := folder
  for name in ["ms_local", "ms_utc", "us_local", "us_utc", "ns_local", "ns_utc", "schema_only"] do
    match ← convert directory name with
    | .error cause => throw (IO.userError s!"{name}: reverse {repr cause}")
    | .ok middle =>
      match Leaf.Events.ToIpc.convert {} {} middle 1 with
      | .error cause => throw (IO.userError s!"{name}: forward {repr cause}")
      | .ok output =>
        IO.FS.writeBinFile (directory / (name ++ ".parquet")) middle.data
        IO.FS.writeBinFile (directory / (name ++ ".roundtrip")) output.toByteArray
  let refusals : List (String × FromIpc.Error) :=
    [("seconds", .seconds), ("named", .timezone "Asia/Kathmandu"),
      ("offset", .timezone "+00:00"), ("empty_timezone", .timezone ""),
      ("missing_eos", .source (.batch 4 (.envelope (.malformed .truncated))))]
  for (name, expected) in refusals do
    match ← convert directory name with
    | .error actual =>
      unless actual == expected do throw (IO.userError s!"{name}: unexpected {repr actual}")
    | .ok _ => throw (IO.userError s!"{name}: unexpected output")
  IO.println "Five pinned typed source refusals passed"
