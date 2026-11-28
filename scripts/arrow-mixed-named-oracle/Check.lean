module

import Lean.Data.Json
import Silmaril.Formats.Relational.NamedTable.MixedIpc.Defs
meta import Lean.Data.Json
meta import Silmaril.Formats.Relational.NamedTable.MixedIpc.Defs

open Lean (Json toJson)
open Silmaril Silmaril.Formats.Arrow Silmaril.Relational
open Silmaril.Formats.Relational.NamedTable.MixedIpc

private def ordered : Descriptor := ⟨false, ("ordinal", true), ("payload", true)⟩
private def reverse : Descriptor := ⟨true, ("ordinal", false), ("payload", true)⟩

private def original : Database String := fun name =>
  if name = "other" then some ⟨ordered.schema, [ordered.row (some 17, some [255])]⟩ else none

private def rowsOf (table : Scan.Observation Label Cell) : List (List Json) :=
  table.rows.map fun row => List.ofFn fun i =>
    match h : (table.schema.kind i).2 with
    | .int32 => toJson (((show Option Int32 from cast (congrArg (fun kind => Option (Cell kind)) h) (row i))).map Int32.toInt)
    | .binaryView => toJson (((show Option (List UInt8) from cast (congrArg (fun kind => Option (Cell kind)) h) (row i))).map (List.map UInt8.toNat))

private def fieldsOf (table : Scan.Observation Label Cell) : List (List Json) :=
  List.ofFn fun i =>
    let (label, kind) := table.schema.kind i
    [toJson label.1, toJson label.2, toJson (match kind with | .int32 => "int32" | .binaryView => "binary_view")]

private def load (directory : System.FilePath) (label : String) : IO KBytes := do
  let bytes ← IO.FS.readBinFile (directory / (label ++ ".arrows"))
  return KBytes.ofChunks 1 bytes.size (bytes.data.toList.map UInt8.toNat)

private def examine (input : KBytes) (descriptor : Descriptor) : IO Json := do
  let .ok prepared := read {} input | throw (IO.userError "the checked source did not return batches")
  unless prepared.descriptor == descriptor do throw (IO.userError "wrong normalized descriptor")
  let .ok next := importIpc original "target" descriptor {} input
    | throw (IO.userError "checked IPC import failed")
  let some table := Scan.observePacked next "target" | throw (IO.userError "missing inserted table")
  let some existing := Scan.observePacked next "other" | throw (IO.userError "missing existing table")
  unless rowsOf existing == [[toJson (17 : Int), toJson ([255] : List Nat)]] do
    throw (IO.userError "existing row changed")
  let .error .nameConflict := importIpc next "target" descriptor {} input
    | throw (IO.userError "repeated import did not detect occupied destination")
  return Json.mkObj [("fields", toJson (fieldsOf table)), ("rows", toJson (rowsOf table)),
    ("counts", toJson (prepared.batches.map List.length))]

private def refuse (input : KBytes)
    (reason : Silmaril.Formats.Relational.NamedTable.ImportError
      Silmaril.Formats.Relational.NamedTable.MixedIpc.Error)
    (expected : Descriptor := ordered) (limits : Silmaril.Formats.Relational.NamedTable.MixedIpc.Limits := {}) :
    IO Unit := do
  match importIpc original "target" expected limits input with
  | .error cause =>
    unless cause == reason do throw (IO.userError s!"wrong refusal: expected {reasonCode reason}, got {reasonCode cause}")
  | .ok _ => throw (IO.userError "an invalid source returned an updated database")
where
  reasonCode : Silmaril.Formats.Relational.NamedTable.ImportError
      Silmaril.Formats.Relational.NamedTable.MixedIpc.Error → String
    := fun reason => match reason with
    | .readError err | .openError err => reprStr err
    | .schemaMismatch => "schemaMismatch"
    | .nameConflict => "nameConflict"
    | .closed => "closed"
    | .closeError err => reprStr err

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the fixture directory")
  let dir := System.FilePath.mk path
  let mixed ← load dir "mixed"
  let reversed ← load dir "reverse"
  let schemaOnly ← load dir "schema-only"
  let empty ← load dir "empty-batch"
  let truncated ← load dir "late-body"
  let missingEos ← load dir "missing-eos"
  let unsupported ← load dir "unsupported"

  refuse truncated (.readError (.reader (.batch 2 (.body (.malformed .truncated)))))
  refuse missingEos (.readError (.reader (.batch 3 (.envelope (.malformed .truncated)))))
  refuse (mixed ++ .leaf 1 0) (.readError (.reader (.batch 3 .trailingBytes)))
  refuse mixed (.readError (.reader (.batch 2 (.budget (.limit .totalRows)))))
    ordered { mixed := { observation := { totalRows := 4 } } }
  refuse truncated (.openError (.inputBytes truncated.len 7)) ordered { inputBytes := 7 }
  refuse unsupported (.openError (.unsupportedFields
    [⟨"ordinal", true, .primitive .int32⟩, ⟨"payload", true, .view .utf8⟩]))
  refuse reversed .schemaMismatch { reverse with integer := ("ordinal", true) }
  refuse mixed .schemaMismatch { ordered with viewFirst := true }
  refuse mixed .schemaMismatch { ordered with binary := ("foreign", true) }
  refuse .empty (.openError (.reader (.schemaEnvelope (.malformed .truncated))))
  let .error .nameConflict := importIpc original "other" ordered {} truncated
    | throw (IO.userError "name conflict did not precede the late reader error")

  let observations ← [(mixed, ordered), (reversed, reverse), (schemaOnly, ordered),
    (empty, ordered)].mapM fun (input, descriptor) => examine input descriptor
  IO.println (toJson observations).compress
