module

import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Defs
meta import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Defs

open Silmaril Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.MixedV1Writer.FromIpc
open Silmaril.Formats.Relational.NamedTable

private def sink : MixedV1Writer.Multi.Limits :=
  ⟨⟨4096, {}, ⟨{}, 32, ⟨128, 128, ⟨16, 32⟩, 0⟩⟩,
    ⟨⟨{}, 32, ⟨128, 128, ⟨16, 32⟩, 0⟩⟩, ⟨128, 32⟩⟩, {}⟩, 8, 16⟩

private def load (directory : System.FilePath) (name : String) : IO KBytes := do
  let wire ← IO.FS.readBinFile (directory / (name ++ ".arrows"))
  return KBytes.ofChunks 1 wire.size (wire.data.toList.map UInt8.toNat)

private def refuse (input : KBytes) (expected : Error) (limits : MixedV1Writer.Multi.Limits := sink)
    (source : MixedIpc.Limits := {}) : IO Unit := do
  let .error actual := convert source limits input | throw (IO.userError s!"expected {repr expected}, got a file")
  unless actual == expected do
    throw (IO.userError s!"expected {repr expected}, got {repr actual}")

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the fixture directory")
  let directory := System.FilePath.mk path
  let mixed ← load directory "mixed"
  let required ← load directory "required"
  let emptyBatch ← load directory "empty-batch"
  let schemaOnly ← load directory "schema-only"
  let reversed ← load directory "reverse"
  let unsupported ← load directory "unsupported"
  let missingEos ← load directory "missing-eos"
  let truncated ← load directory "late-body"

  for (name, input) in [("mixed", mixed), ("required", required), ("empty-batch", emptyBatch)] do
    let .ok output := convert { inputBytes := input.len } sink input
      | throw (IO.userError s!"{name}: native conversion failed")
    IO.FS.writeBinFile (directory / (name ++ ".parquet")) output.bytes.data

  refuse truncated (.source (.reader (.batch 2 (.body (.malformed .truncated))))) { sink with maxGroups := 0 }
  refuse missingEos (.source (.reader (.batch 3 (.envelope (.malformed .truncated)))))
  refuse mixed (.source (.inputBytes mixed.len (mixed.len - 1))) sink { inputBytes := mixed.len - 1 }
  refuse unsupported (.source (.unsupportedFields
    [⟨"ordinal", true, .primitive .int32⟩, ⟨"payload", true, .view .utf8⟩]))
  refuse reversed (.plan .fieldOrder)
  refuse schemaOnly (.plan .noBatches)
  refuse mixed (.sink .groupLimit) { sink with maxGroups := 2 }
  refuse mixed (.sink .totalRows) { sink with maxTotalRows := 4 }
  let page := sink.writer.bytePage
  let writer := { sink.writer with bytePage := { page with plain := { page.plain with valueBytes := 12 } } }
  refuse mixed (.sink (.page 2 (.bytePage (.plain .valueByteLimit)))) { sink with writer }
  refuse mixed (.sink .fileLimit) { sink with writer := { sink.writer with maxFileBytes := 12 } }
  IO.println "Three full Parquet files and ten typed source, planning and sink refusals."
