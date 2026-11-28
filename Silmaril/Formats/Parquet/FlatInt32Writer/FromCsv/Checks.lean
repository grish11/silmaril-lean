module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv.Defs
meta import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Defs

namespace Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv

open Silmaril.Relational
open Silmaril.Formats.Relational.NamedTable (Packed)
open Silmaril.Formats.Parquet.Snapshot.FlatInt32 (Cell)
open Silmaril.Formats.Parquet.Snapshot.FlatInt32.ToCsv (csvSchema)

private def schema : Scan.Schema String Unit := ⟨2, fun i => (if i.val = 0 then "café" else "值", ())⟩

private def csvLimits : CsvLimits := ⟨4096, 64, 8⟩
private def parquetLimits : FlatInt32Writer.Limits := ⟨8, 16384, {}, ⟨{}, 64, ⟨4096, 4096, ⟨64, 512⟩, 0⟩⟩⟩

private def scanLimits : FlatScan.Limits := {
  footer := parquetLimits.footer
  page := parquetLimits.pageReader
  maxRows := 64
  maxColumns := 8
  maxCells := 512
  maxPageBytes := 4096
}

private def db : Packed Nat Csv.Field Cell := fun name =>
  if name = 0 then some ⟨csvSchema schema, [fun _ => some 201]⟩ else none

private def utf8 (text : String) : Csv.Bytes := text.toByteArray.data.toList
private def header : String := "\"café\",\"值\"\r\n"
private def wire : Csv.Bytes := utf8 (header ++
  "\"T-2147483648\",\"N\"\r\n\"T0\",\"T-1\"\r\n\"T2147483647\",\"T0\"\r\n")

private def observe (database : Packed Nat Csv.Field Cell) (name : Nat) :
    Option (List Csv.Field × List (List (Option Int32))) :=
  (Scan.observePacked database name).map fun table =>
    ((List.ofFn fun i => (table.schema.kind i).1), table.rows.map List.ofFn)

private def scan (result : Result Nat) :=
  (FlatScan.scanFileRowGroup scanLimits (FlatScan.decodeInt32Page parquetLimits.page.scalar)
    result.bytes 0).toOption.map fun batch =>
      (batch.columns.map (·.1), batch.rowCount, batch.rows)

private def run (wire : Csv.Bytes) := convert db 1 schema csvLimits parquetLimits wire

private def expected : List (List (Option Int32)) :=
  [[some (-2147483648), none], [some 0, some (-1)], [some 2147483647, some 0]]

private def fields : List FlatScan.Field := [⟨"café", .optional⟩, ⟨"值", .optional⟩]

#guard (run wire).toOption.bind scan = some (fields, 3, expected)
#guard (run wire).toOption.map (fun result => (observe result.db 1, observe result.db 0)) ==
  some (some ([utf8 "café", utf8 "值"], expected), some ([utf8 "café", utf8 "值"], [[some 201, some 201]]))
#guard (run (utf8 header)).toOption.bind scan = some (fields, 0, [])
#guard (convert db 0 schema csvLimits parquetLimits []).map Result.bytes =
  .error (.destination .nameConflict)
#guard (run (utf8 "\"值\",\"café\"\r\n")).map Result.bytes = .error (.csv .headerMismatch)
#guard (run (utf8 (header ++ "\"\",\"T0\"\r\n"))).map Result.bytes = .error (.csv (.invalidTag 0))
#guard (run (utf8 (header ++ "\"0\",\"T0\"\r\n"))).map Result.bytes = .error (.csv (.invalidTag 0))
#guard (run (utf8 (header ++ "\"T\",\"N\"\r\n"))).map Result.bytes = .error (.csv (.parseCell 0))
#guard (run (utf8 (header ++ "\"T2147483648\",\"N\"\r\n"))).map Result.bytes =
  .error (.csv (.parseCell 0))
#guard (convert db 1 schema {csvLimits with maxBytes := 4} parquetLimits wire).map Result.bytes =
  .error .csvByteLimit
#guard (convert db 1 schema {csvLimits with maxColumns := 1} parquetLimits wire).map Result.bytes =
  .error .csvColumnLimit
#guard (convert db 1 schema {csvLimits with maxRows := 2} parquetLimits wire).map Result.bytes =
  .error .csvRowLimit
#guard (convert db 1 schema csvLimits {parquetLimits with maxFileBytes := 11} wire).map Result.bytes =
  .error (.parquet .fileLimit)

private def duplicate : Scan.Schema String Unit := ⟨2, fun _ => ("id", ())⟩
private def empty : Scan.Schema String Unit := ⟨0, Fin.elim0⟩

#guard (convert db 1 duplicate csvLimits parquetLimits (utf8 "\"id\",\"id\"\r\n")).map Result.bytes =
  .error (.parquet .schemaOrCount)
#guard (convert db 1 empty csvLimits parquetLimits (utf8 "\"\"\r\n")).map Result.bytes =
  .error (.parquet .schemaOrCount)

private def v1 : Bytes := ⟨include_bytes "../../../../../tools/parquet-flat-scan/fixtures/flat-plain-v1.parquet"⟩
private def v2 : Bytes := ⟨include_bytes "../../../../../tools/parquet-flat-scan/fixtures/flat-plain-v2.parquet"⟩
private def fixtureSchema : Scan.Schema String Unit :=
  ⟨2, fun i => (if i.val = 0 then "required_i32" else "optional_i32", ())⟩

private def fixtureRoundTrip (input : Bytes) := do
  let exported ← (Snapshot.FlatInt32.ToCsv.convert db 1 fixtureSchema {} input).toOption
  let output ← (convert db 1 fixtureSchema csvLimits parquetLimits exported.wire).toOption
  scan output

private def fixtureFields : List FlatScan.Field := [⟨"required_i32", .optional⟩, ⟨"optional_i32", .optional⟩]
private def fixtureRows : List (List (Option Int32)) := (List.range 24).map fun i =>
  [some (Int32.ofInt (10 * (i : Int) - 17)),
    if i % 3 = 0 then none else some (Int32.ofInt (-3 * (i : Int)))]

#guard fixtureRoundTrip v1 = some (fixtureFields, 24, fixtureRows)
#guard fixtureRoundTrip v2 = some (fixtureFields, 24, fixtureRows)

#print axioms convert_readback
#print axioms convert_parquet_error
#print axioms convert_name_conflict

end Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv
