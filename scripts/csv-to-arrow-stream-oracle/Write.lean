module

import Silmaril.Formats.Arrow.FromCsv.Stream.Defs
meta import Silmaril.Formats.Arrow.FromCsv.Stream.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Relational.NamedTable (Packed)
open Silmaril.Formats.Arrow.FromCsv.Stream

private def namedFields : List Field := [⟨"key", false, .int32⟩, ⟨"café", true, .utf8⟩]

private def namedTable : Packed String Csv.Field ToCsv.Cell := fun name => do
  if name ≠ "inventory" then none else
    let rows ← ([[some (.int32 7), some (.utf8 "λ")],
      [some (.int32 8), none], [some (.int32 7), some (.utf8 "")],
      [some (.int32 7), some (.utf8 "λ")]].mapM (ToCsv.typedRow namedFields)).toOption
    return ⟨ToCsv.schemaOf namedFields, rows⟩

private def write (directory : System.FilePath) (name : String)
    (result : Except EmitError KBytes) : IO Unit :=
  match result with
  | .error (.adapter _) => throw (IO.userError s!"{name}: adapter error")
  | .error (.writer _) => throw (IO.userError s!"{name}: writer error")
  | .ok bytes => IO.FS.writeBinFile (directory / s!"{name}.arrows") ⟨bytes.toList.toArray⟩

public def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: Write.lean OUTPUT-DIRECTORY")
  let output : System.FilePath := directory
  let ascii ← IO.FS.readBinFile (output / "ascii.csv")
  write output "csv" (emitCsv {} [⟨"n", true, .int32⟩, ⟨"text", true, .utf8⟩] ascii.data.toList)
  write output "csv-utf8" (emitCsvUtf8 {} [⟨"id", false, .int32⟩, ⟨"café", true, .utf8⟩]
    "\"id\",\"café\"\r\n\"T-1\",\"T雪\"\r\n\"T0\",\"N\"\r\n\"T1\",\"T\"\r\n".toUTF8.data.toList)
  write output "named" (emitNamed {} namedTable "inventory" namedFields)
  write output "zero-columns" (emitCsv {} [] "\"\"\r\n\"\"\r\n\"\"\r\n".toUTF8.data.toList)
  write output "empty" (emitCsv {} [⟨"n", false, .int32⟩] "\"n\"\r\n".toUTF8.data.toList)
