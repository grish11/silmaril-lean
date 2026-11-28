module

import Silmaril.Formats.Relational.BinaryObservation.Defs
meta import Silmaril.Formats.Relational.BinaryObservation.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Relational.BinaryObservation

private def field : Field := ⟨"blob", true⟩
private def column : ParquetColumn := ⟨field, .byteArray, 0, ⟨0, 1⟩⟩
private def limits : PageLimits := ⟨⟨4096, 4096, ⟨64, 64⟩, 0⟩, ⟨4096, 256⟩⟩

private def slots : List Slot :=
  [none, some [], some [0xff, 0], some "123456789012".toUTF8.data.toList,
    some "1234567890123".toUTF8.data.toList, none, some [0],
    some ("long".toUTF8.data.toList ++ [0] ++ "opaque".toUTF8.data.toList ++
      [0xfe] ++ "value".toUTF8.data.toList)]

private def matchesExpected (observed : Observation) : Bool :=
  List.ofFn observed.schema.kind == [(field.name, field.nullable)] &&
  (observed.rows.map fun row =>
    List.ofFn fun index : Fin observed.schema.width => (row index : Slot)) == slots.map (· :: [])

private def expectError {Error : Type} [DecidableEq Error] (label : String) (expected : Error)
    (result : Except Error Observation) : IO Unit :=
  match result with
  | .error actual => unless actual == expected do throw (IO.userError s!"wrong error: {label}")
  | .ok _ => throw (IO.userError s!"unexpected table: {label}")

private def parquetBytes (path : String) : IO Bytes := do
  return Bytes.ofList (← IO.FS.readBinFile path).data.toList

private def arrowBytes (path : String) : IO KBytes := do
  let input ← IO.FS.readBinFile path
  return KBytes.ofChunks 1 input.size (input.data.toList.map UInt8.toNat)

private def readWindow (headerPath bodyPath : String) : IO PageWindow := do
  let source ← parquetBytes headerPath
  let .ok (header, consumed) := Page.readHeaderPrefix {} source
    | throw (IO.userError "fixture header could not be parsed")
  unless consumed == source.length do throw (IO.userError "fixture header not consumed")
  return ⟨header, ← parquetBytes bodyPath⟩

public def main (args : List String) : IO Unit := do
  let [ipcPath, truncatedIpc, header0, body0, header1, body1, truncatedPage] := args
    | throw (IO.userError "expected seven fixture paths")
  let ipc ← arrowBytes ipcPath
  let shortIpc ← arrowBytes truncatedIpc
  let first ← readWindow header0 body0
  let second ← readWindow header1 body1
  let shortPage ← readWindow header1 truncatedPage
  let crcPage := { second with header := { second.header with crc := some 0 } }
  let parquet := fun expected => observeParquet expected limits column
  let arrow := fun expected => observeIpc expected {} {}

  let .ok parquetResult := parquet field [first, second]
    | throw (IO.userError "Parquet page observation failed")
  let .ok ipcResult := arrow field ipc
    | throw (IO.userError "Arrow IPC observation failed")
  unless matchesExpected parquetResult && matchesExpected ipcResult do
    throw (IO.userError "wrong descriptor or ordered binary slots")

  expectError "second page extent before later CRC" (.page 1 (.scalar (.payload .compressedSizeMismatch)))
    (parquet field [first, shortPage, crcPage])
  expectError "third IPC record body" (.reader (.batch 2 (.body (.malformed .truncated))))
    (arrow field shortIpc)
  expectError "Parquet field name" (.fieldMismatch field) (parquet ⟨"other", true⟩ [first, second])
  expectError "IPC field name" (.fieldMismatch field) (arrow ⟨"other", true⟩ ipc)
  expectError "Parquet nullability" (.fieldMismatch field) (parquet ⟨"blob", false⟩ [first, second])
  expectError "IPC nullability" (.fieldMismatch field) (arrow ⟨"blob", false⟩ ipc)
  expectError "CRC before a later page error" (.page 0 .crcUnsupported)
    (parquet field [crcPage, shortPage])
  expectError "unsupported physical type" (.physicalType .int32)
    (observeParquet field limits { column with physicalType := .int32 } [first])
  expectError "unsupported codec" (.codec 1) (observeParquet field limits { column with codec := 1 } [first])
  expectError "levels inconsistent with nullability" (.levels ⟨0, 0⟩)
    (observeParquet field limits { column with levels := ⟨0, 0⟩ } [first])
  let .dataV2 data := second.header.kind
    | throw (IO.userError "fixture must use V2")
  let encoded := { second with header := { second.header with kind := .dataV2 { data with encoding := 7 } } }
  expectError "non-PLAIN page" (.page 1 (.scalar (.unsupportedEncoding 7)))
    (parquet field [first, encoded])
  IO.println "Lean: 2 exact binary observations of 8 nullable slots and 11 typed rejection cases"
