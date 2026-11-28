module

import Silmaril.Formats.Arrow.MixedFlat.Stream.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture

open Silmaril Silmaril.Formats
open Arrow.MixedFlat.Stream Arrow.MixedFlat.Stream.Fixture

private inductive Values where
  | primitive (values : Arrow.Column)
  | binary (values : List (Option (List UInt8)))
  | text (values : List (Option String))
  deriving DecidableEq

private def valuesOf (observed : Arrow.MixedFlat.Observed) : List Values :=
  observed.columns.map fun (_, column) =>
    match column with
    | .primitive values => .primitive values
    | .binaryView values => .binary (values.map (·.map KBytes.toList))
    | .utf8View values => .text values

private def streamFields : List Arrow.MixedFlat.Field :=
  [⟨"i", true, .primitive .int32⟩, ⟨"b", true, .view .binary⟩,
    ⟨"u", true, .primitive .utf8⟩, ⟨"v", true, .view .utf8⟩]

private def expected : List (List Values) :=
  [[.primitive [some (.int32 1), none, some (.int32 (-7)), some (.int32 0)],
    .binary [some (List.replicate 13 120), none, some [], some (List.replicate 17 121)],
    .primitive [some (.utf8 "α"), some (.utf8 ""), none, some (.utf8 "last")],
    .text [none, some "", some "short", some "雪雪雪雪雪雪"]],
   [.primitive [], .binary [], .primitive [], .text []],
   [.primitive [some (.int32 42), none], .binary [some [], some [255]],
    .primitive [some (.utf8 "end"), none], .text [some "ΩΩΩΩΩΩΩ", some ""]]]

#guard match read {} multi with
  | .ok observed =>
    decide (observed.fields = streamFields ∧
      observed.batches.map (·.observed.rowCount) = [4, 0, 2] ∧
      observed.batches.map (fun batch => valuesOf batch.observed) = expected ∧
      observed.batches.map (fun batch =>
        (batch.range.offset, batch.range.metadataSize, batch.range.bodyLength)) = multiRanges)
  | _ => false

#guard match read { observation := { ipc := { batches := 0 }, totalRows := 0 } } schemaOnly with
  | .ok observed => decide (observed.fields = streamFields) && observed.batches.isEmpty
  | _ => false

private def rejects (input : KBytes) (expected : Error) (limits : Arrow.MixedFlat.Limits := {}) : Bool :=
  match read limits input with
  | .error actual => decide (actual = expected)
  | .ok _ => false

private def eos : KBytes := .leaf 8 0xffffffff

private def patch (bytes : KBytes) (offset width value : Nat) : KBytes :=
  bytes.slice 0 offset ++ .leaf width value ++
    bytes.slice (offset + width) (bytes.len - (offset + width))

#guard rejects lateTruncated (.batch 2 (.body (.malformed .truncated)))
#guard rejects (multi.slice 0 (lastRecordOffset + 9)) (.batch 2 (.envelope (.malformed .truncated)))
#guard rejects (multi.slice 0 multiEos) (.batch 3 (.envelope (.malformed .truncated)))
#guard rejects (multi ++ .leaf 1 0) (.batch 3 .trailingBytes)
#guard rejects (multi.slice 0 lastRecordOffset ++ eos ++ .leaf 1 0) (.batch 2 .trailingBytes)
#guard rejects (multi.slice 0 lastRecordOffset ++ multi.slice 0 (8 + multiSchemaSize))
  (.batch 2 (.metadata (.metadata (.unsupported (.messageKind 1)))))
#guard rejects (patch multi lastViewPrefix 4 0) (.batch 2 (.decode (.field 3 (.view (.slot 0 .prefixMismatch)))))
#guard rejects multi (.batch 2 .batchLimit) { observation := { ipc := { batches := 2 } } }
#guard rejects multi (.batch 2 (.budget (.limit .totalRows))) { observation := { totalRows := 5 } }
#guard rejects multi (.batch 2 (.budget (.limit .totalCells))) { observation := { totalCells := 20 } }
#guard rejects eos .expectedSchema
#guard rejects (.node multi.len .empty .empty) .source
