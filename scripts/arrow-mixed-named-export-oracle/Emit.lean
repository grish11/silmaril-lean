module

import Silmaril.Formats.Relational.NamedTable.MixedIpc.Export.Defs
meta import Silmaril.Formats.Relational.NamedTable.MixedIpc.Export.Defs

open Silmaril
open Silmaril.Formats.Relational.NamedTable.MixedIpc

private def ordered : Descriptor := ⟨false, ("ordinal", true), ("payload", true)⟩
private def reversed : Descriptor := ⟨true, ("value", false), ("raw", true)⟩

private def long : List UInt8 := [255, 0, 1] ++ List.replicate 16 113

private def pairs : List Pair :=
  [(some (-2147483648), some []), (none, none), (some 2147483647, some long), (some 0, some [0, 255])]

private def reversePairs : List Pair :=
  [(some (-2147483648), some []), (some 7, none), (some 2147483647, some long), (some 0, some [0, 255])]

private def database (descriptor : Descriptor) (rows : List Pair) : Database String := fun key =>
  if key = "stored" then some ⟨descriptor.schema, rows.map descriptor.row⟩ else none

private def make (directory : System.FilePath) (file : String) (descriptor : Descriptor)
    (rows : List Pair) (sizes : List Nat) : IO Unit := do
  let source := database descriptor rows
  let .ok bytes := Export.emit source "stored" descriptor sizes {}
    | throw (IO.userError s!"{file}: export failed")
  let .ok checked := read {} bytes | throw (IO.userError s!"{file}: native read failed")
  unless checked.descriptor == descriptor && checked.batches.map List.length == sizes &&
      checked.batches.flatten == rows do
    throw (IO.userError s!"{file}: incorrect native observation")
  let .ok updated := importIpc source "copy" descriptor {} bytes
    | throw (IO.userError s!"{file}: import at vacant key failed")
  for key in ["stored", "copy"] do
    let .ok [stored] := Export.prepare updated key descriptor [rows.length]
      | throw (IO.userError s!"{file}: incorrect schema or row count at {key}")
    unless stored == rows do throw (IO.userError s!"{file}: incorrect stored rows at {key}")
  IO.FS.writeBinFile (directory / (file ++ ".arrows")) bytes.toByteArray

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fixture directory")
  let directory := System.FilePath.mk path
  make directory "empty-middle" ordered pairs [2, 0, 2]
  make directory "rechunked" ordered pairs [4]
  make directory "reversed" reversed reversePairs [1, 3]
  make directory "schema-only" ordered [] []
  make directory "empty-batch" ordered [] [0]

  let source := database ordered pairs
  let .error (.table .missingName) := Export.emit source "missing" ordered [4] {}
    | throw (IO.userError "missing key")
  let .error (.table (.rowCountMismatch 3 4)) := Export.emit source "stored" reversed [3] {}
    | throw (IO.userError "inexact batch plan or error precedence")
  let .error .schemaMismatch := Export.emit source "stored" { ordered with viewFirst := true } [4] {}
    | throw (IO.userError "incompatible physical field order")
  let .error .schemaMismatch := Export.emit source "stored" { ordered with binary := ("payload", false) } [4] {}
    | throw (IO.userError "incompatible nullability")
  let .error (.octetBytes 21 5) := Export.emit source "stored" ordered [4] { inputBytes := 5 }
    | throw (IO.userError "raw octet cap")
  let .error (.wireBytes actual 7) := Export.emit (database ordered []) "stored" ordered [] { inputBytes := 7 }
    | throw (IO.userError "framed carrier cap")
  unless actual > 7 do throw (IO.userError "invalid rejected wire length")
  let .error (.writer (.batch 1 (.view 1 .valueLimit))) := Export.emit source "stored" ordered [2, 2]
      { mixed := { view := { valueBytes := 3 } } }
    | throw (IO.userError "indexed writer error")
  let .error (.writer (.batch 1 (.nullInRequired 1))) :=
      Export.emit (database reversed pairs) "stored" reversed [1, 3] {}
    | throw (IO.userError "required INT32 accepted a null in the reversed schema")
  let .error (.writer (.ipc (.limit .batches))) := Export.emit source "stored" ordered [2, 0, 2]
      { mixed := { observation := { ipc := { batches := 2 } } } }
    | throw (IO.userError "empty batch did not count toward batch limit")
  IO.println "Five native exports with checked read/import, and nine typed refusals."
