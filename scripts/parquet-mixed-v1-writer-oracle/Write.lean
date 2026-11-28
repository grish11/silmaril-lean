module

import Silmaril.Formats.Parquet.MixedV1Writer.Defs
meta import Silmaril.Formats.Parquet.MixedV1Writer.Defs

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.MixedV1Writer

private def opaqueBytes : Bytes := .ofList [255, 0, 128]
private def long : Bytes := .ofList (List.replicate 20 42)
private def mixed : Input :=
  ⟨"ordinal", .required [-2147483648, 0, 17, 2147483647, -1], "payload",
    .optional [none, some .empty, some opaqueBytes, none, some long]⟩

private def fixtures : List (String × Input) :=
  [("required", ⟨"id", .required [-2147483648, 0, 2147483647], "raw", .required [.empty, opaqueBytes, long]⟩),
   ("mixed", mixed),
   ("optional-int", ⟨"count", .optional [some (-7), none, some 2], "raw", .required [opaqueBytes, .empty, long]⟩),
   ("both-optional", ⟨"count", .optional [none, some 5, none], "clé", .optional [none, some .empty, some opaqueBytes]⟩),
   ("empty-group", ⟨"id", .required [], "raw", .optional []⟩)]

private def exactPages (input : Input) : Limits :=
  ⟨4096, {},
    ⟨{}, 32, ⟨input.integers.bodySize, input.integers.bodySize,
      ⟨input.integers.numValues, input.integers.definitionSize⟩, 0⟩⟩,
    ⟨⟨{}, 32, ⟨input.octets.bodySize, input.octets.bodySize,
      ⟨input.octets.numValues, input.octets.definitionSize⟩, 0⟩⟩,
      ⟨Plain.ByteArray.encodedSize input.octets.values, 20⟩⟩, {}⟩

private def reject (input : Input) (limits : Limits) (expected : Error) : IO Unit := do
  let .error result := emit limits input | throw (IO.userError s!"expected {repr expected}, got a file")
  unless result == expected do
    throw (IO.userError s!"expected {repr expected}, got {repr result}")

public def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected an output directory")
  let destination : System.FilePath := directory
  IO.FS.createDirAll destination
  for (name, input) in fixtures do
    let limits := exactPages input
    match emit limits input with
    | .error reason => throw (IO.userError s!"{name}: {repr reason}")
    | .ok output =>
      let .ok observed := Int32ByteArrayGroup.readFileRowGroup limits.readback output.bytes
          input.intField input.byteField 0
        | throw (IO.userError s!"{name}: mixed reader refused the file")
      unless observed == input.rows do throw (IO.userError s!"{name}: wrong paired rows")
      let .ok exact := emit { limits with maxFileBytes := output.bytes.length } input
        | throw (IO.userError s!"{name}: exact file budget did not admit the file")
      unless exact.bytes == output.bytes do throw (IO.userError s!"{name}: budget changed the file")
      IO.FS.writeBinFile (destination / s!"{name}.parquet") output.bytes.data

  let limits := exactPages mixed
  reject { mixed with byteName := mixed.intName } limits .schemaOrCount
  reject { mixed with octets := .optional [] } limits .schemaOrCount
  reject mixed { limits with maxFileBytes := 4 } .fileLimit
  reject mixed { limits with footer := { limits.footer with maxFooterBytes := 0 } } (.compact .byteLimit)
  reject mixed { limits with intPage := { limits.intPage with headerBytes := 0 } } .intBudget
  let bytePage := limits.bytePage
  reject mixed { limits with bytePage := { bytePage with page := { bytePage.page with headerBytes := 0 } } }
    .byteBudget
  reject mixed { limits with bytePage := { bytePage with plain := { bytePage.plain with valueBytes := 19 } } }
    (.bytePage (.plain .valueByteLimit))
  let .ok output := emit limits mixed | throw (IO.userError "the clean control did not produce a file")
  reject mixed { limits with readback := { limits.readback with maxFileBytes := 0 } }
    (.readback (.fileByteLimit 0 output.bytes.length))
  IO.println "Five native full files, exact file-cap admission and eight typed refusals."
