module

import Silmaril.Formats.Parquet.PlainV1Writer.Defs
meta import Silmaril.Formats.Parquet.PlainV1Writer.Defs

open Silmaril.Formats.Parquet.PlainV1Writer

private def fixtures : List (String × Input) :=
  [("required", .required [-2147483648, 0, 2147483647]),
   ("mixed", .optional [some 7, none, some (-4), none, some 19]),
   ("all-null", .optional [none, none, none]),
   ("required-empty", .required []), ("optional-empty", .optional [])]

public def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: Write.lean OUTPUT-DIRECTORY")
  let output : System.FilePath := directory
  IO.FS.createDirAll output
  for (name, input) in fixtures do
    let limits : Limits := ⟨{}, 17,
      ⟨input.bodySize, input.bodySize, ⟨input.numValues, input.definitionSize⟩, 0⟩⟩
    let .ok page := emit limits input | throw (IO.userError s!"{name}: page write failed")
    IO.FS.writeBinFile (output / s!"{name}.page") page.wire.data
