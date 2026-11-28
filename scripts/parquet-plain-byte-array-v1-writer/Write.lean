module

import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.Defs
meta import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.Defs

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.PlainByteArrayV1Writer

private def binary : Bytes := .ofList [255, 0, 128]
private def long : Bytes := .ofList (List.replicate 20 42)
private def mixed : Input := .optional [none, some .empty, some binary, none, some long]

private def fixtures : List (String × Input) :=
  [("required", .required [.empty, binary, long]),
   ("mixed", mixed), ("all-null", .optional [none, none, none]),
   ("required-empty", .required []), ("optional-empty", .optional [])]

private def exactLimits (input : Input) : Limits :=
  ⟨⟨{}, 17, ⟨input.bodySize, input.bodySize, ⟨input.numValues, input.definitionSize⟩, 0⟩⟩,
   ⟨Plain.ByteArray.encodedSize input.values, 20⟩⟩

private def reject (limits : Limits) (cause : Error) : IO Unit := do
  let .error actual := emit limits mixed
    | throw (IO.userError s!"expected {repr cause}, got a page")
  unless actual == cause do
    throw (IO.userError s!"expected {repr cause}, got {repr actual}")

public def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected the output directory")
  let output : System.FilePath := directory
  IO.FS.createDirAll output
  for (name, input) in fixtures do
    let limits := exactLimits input
    let .ok page := emit limits input | throw (IO.userError s!"{name}: page write failed")
    unless page.body.length == input.bodySize do throw (IO.userError s!"{name}: wrong body extent")
    let .ok checked := ScalarPage.decode (.byteArray limits.plain) input.parameters limits.page.scalar page.body
      | throw (IO.userError s!"{name}: page readback failed")
    unless checked == input.slots do throw (IO.userError s!"{name}: wrong ordered nullable slots")
    IO.FS.writeBinFile (output / s!"{name}.page") page.wire.data

  let limits := exactLimits mixed
  let page := limits.page
  let scalar := page.scalar
  let levels := scalar.levels
  reject { limits with page := { page with scalar := { scalar with levels := { levels with values := 4 } } } }
    .bodyBudget
  reject { limits with page := { page with scalar := { scalar with levels := { levels with bytes := 9 } } } }
    .bodyBudget
  reject { limits with page := { page with scalar := { scalar with compressedBytes := mixed.bodySize - 1 } } }
    .bodyBudget
  reject { limits with page := { page with scalar := { scalar with uncompressedBytes := mixed.bodySize - 1 } } }
    .bodyBudget
  reject { limits with page := { page with headerBytes := 0 }, plain := ⟨0, 0⟩ } .headerBudget
  reject { limits with plain := { limits.plain with valueBytes := 19 } } (.plain .valueByteLimit)
  reject { limits with plain := { limits.plain with totalBytes := limits.plain.totalBytes - 1 } }
    (.plain .totalByteLimit)
  IO.println "Lean checked five emitted pages and seven typed refusal controls."
