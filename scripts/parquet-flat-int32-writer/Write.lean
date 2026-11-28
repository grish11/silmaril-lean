module

import Silmaril.Formats.Parquet.FlatInt32Writer.Defs
meta import Silmaril.Formats.Parquet.FlatInt32Writer.Defs

open Silmaril.Formats.Parquet.FlatInt32Writer

private def fixtures : List (String × Input) :=
  [("mixed", ⟨3, [⟨"id", .required [-2147483648, 0, 2147483647]⟩,
    ⟨"café", .optional [some 7, none, some (-4)]⟩, ⟨"nulls", .optional [none, none, none]⟩]⟩),
   ("empty", ⟨0, [⟨"id", .required []⟩, ⟨"optional", .optional []⟩]⟩),
   ("wide", ⟨1, (List.range 15).map fun i => ⟨s!"v{i}", .required [Int32.ofInt (Int.ofNat i)]⟩⟩)]

public def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: Write.lean OUTPUT-DIRECTORY")
  let destination : System.FilePath := directory
  IO.FS.createDirAll destination
  let limits : Limits := ⟨16, 4096, {}, ⟨{}, 32, ⟨64, 64, ⟨16, 32⟩, 0⟩⟩⟩
  for (name, input) in fixtures do
    match emit limits input with
    | .error error => throw (IO.userError s!"{name}: {reprStr error}")
    | .ok result => IO.FS.writeBinFile (destination / s!"{name}.parquet") result.bytes.data
