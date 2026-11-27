module

import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan.Defs
meta import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan.Defs

open Silmaril Silmaril.Formats Silmaril.Relational
open Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan

private def project (positions : List Nat) : Projection := fun selected =>
  Scan.Projection.ofArray ((positions.filterMap fun i =>
    if h : i < selected.width then some ⟨i, h⟩ else none).toArray)

private def byOrdinal : Predicate := fun selected row => do
  let position ← if h : 0 < selected.width then some ⟨0, h⟩ else none
  match kind : (selected.kind position).2 with
  | .int32 _ =>
    let value : Int32 ← cast (congrArg (fun k => Option (Legacy.Value k)) kind) (row position)
    return value.toInt % 13 == 5 || value.toInt % 64 == 0 || value.toInt == 372
  | .byteArray _ => none

private def byPayload : Predicate := fun selected row => do
  let position ← if h : 1 < selected.width then some ⟨1, h⟩ else none
  match kind : (selected.kind position).2 with
  | .byteArray _ =>
    let value : Bytes ← cast (congrArg (fun k => Option (Legacy.Value k)) kind) (row position)
    return value.length > 8
  | .int32 _ => none

private def discard : Predicate := fun _ _ => some false

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

private def convertNamed (input : Bytes) (positions : List Nat) (keep : Predicate)
    (ipc : Arrow.MixedFlat.Limits := {}) : Except Legacy.ToIpc.Scan.Error KBytes :=
  convert {} ipc input "ordinal" "payload" (project positions) keep

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the fixture directory")
  let directory := System.FilePath.mk path
  let cases := [
    ("payload-by-ordinal", [1], byOrdinal),
    ("ordinal-by-payload", [0], byPayload),
    ("reordered", [1, 0], byOrdinal),
    ("paired-by-payload", [0, 1], byPayload),
    ("repeated-int32", [0, 0], byPayload),
    ("zero-width", [], byPayload),
    ("discard-all", [1, 0], discard)]
  for name in ["original", "opaque"] do
    let input ← load directory name
    for (label, positions, keep) in cases do
      match convertNamed input positions keep with
      | .error cause => throw (IO.userError s!"{name} {label}: {repr cause}")
      | .ok wire => IO.FS.writeBinFile (directory / s!"{name}-{label}.arrows") wire.toByteArray
  let original ← load directory "original"
  let .error (.unsupportedProjection [("payload", .byteArray .optional),
      ("ordinal", .int32 .required), ("payload", .byteArray .optional)]) :=
    convertNamed original [1, 0, 1] discard |
    throw (IO.userError "expected a typed refusal for repeated BinaryView")
  let lowIpc : Arrow.MixedFlat.Limits := { observation := { totalRows := 0 } }
  let .error (.budget (.limit .totalRows)) := convertNamed original [] byPayload lowIpc |
    throw (IO.userError "zero-width rows must still count toward the IPC budget")
  let damaged ← load directory "damaged"
  for positions in [[], [1, 0], [1, 0, 1]] do
    let .error (.source (.byteArray (.page 2 1 "payload" 19 21009
        (.decode (.plain (.plain .integerOverflow)))))) :=
      convertNamed damaged positions discard lowIpc |
      throw (IO.userError "late indexed failure must prevent a carrier before projection and writer refusal")
  IO.println "Lean: projected native streams, repeated BinaryView refusal, zero-width budget and late source precedence passed"
