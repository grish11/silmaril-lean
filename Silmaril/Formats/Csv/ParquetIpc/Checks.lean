module

import Silmaril.Formats.Csv.ParquetIpc.Thms
import Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv.Thms
meta import Silmaril.Formats.Csv.ParquetIpc.Defs
meta import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Arrow.Defs

namespace Silmaril.Formats.Csv.ParquetIpc

open Silmaril.Relational
open Silmaril.Formats.Parquet
open Snapshot.FlatInt32 (Cell)
open Snapshot.FlatInt32.ToCsv (csvSchema)
open Silmaril.Formats.Relational.NamedTable (Packed)

private def schema : Scan.Schema String Unit := ⟨2, fun i => (if i.val = 0 then "café" else "値", ())⟩
private def db : Packed Nat Csv.Field Cell := fun name =>
  if name = 0 then some ⟨csvSchema schema, [fun _ => some 7]⟩ else none

private def limits (count : Nat) : Limits :=
  let parquet : FlatInt32Writer.Limits := ⟨8, 16384, {}, ⟨{}, 64, ⟨4096, 4096, ⟨64, 512⟩, 0⟩⟩⟩
  let snapshot := parquet.snapshotLimits ⟨count, [⟨"café", .optional []⟩, ⟨"値", .optional []⟩]⟩
  ⟨⟨4096, 64, 8⟩, parquet, snapshot, {}⟩

private def utf8 (text : String) : Csv.Bytes := text.toByteArray.data.toList
private def zeroRows := utf8 "café,値\r\n"
private def mixedRows := utf8 "café,値\r\nT-2147483648,N\r\nN,T0\r\nT2147483647,T-1\r\n"

private def observeDb (database : Packed Nat Csv.Field Cell) (name : Nat) :
    Option (List Csv.Field × List (List (Option Int32))) :=
  (Scan.observePacked database name).map fun table =>
    ((List.ofFn fun i => (table.schema.kind i).1), table.rows.map List.ofFn)

private def observe (limits : Limits) (wire : Csv.Bytes) := do
  let result ← (convert db 1 schema limits wire).toOption
  let csv ← (Csv.Typed.Utf8.decode (csvSchema schema) Snapshot.FlatInt32.ToCsv.codecs result.csv).toOption
  let ipc ← (Arrow.readRows limits.ipc result.ipc).toOption
  let snapshot ← (Snapshot.FlatInt32.ToCsv.readEvents limits.snapshot schema result.parquet).collect.toOption
  pure (observeDb result.db 0, observeDb result.db 1, csv.map List.ofFn, ipc,
    snapshot.table.rows.map (fun (row : Fin snapshot.table.schema.width → Option Int32) => List.ofFn row), snapshot.termination)

private def expected : List (List (Option Int32)) :=
  [[some (-2147483648), none], [none, some 0], [some 2147483647, some (-1)]]

private def expectedFields : List Arrow.Field := [⟨"café", true, .int32⟩, ⟨"値", true, .int32⟩]
private def labels := [utf8 "café", utf8 "値"]
private def original : Option (List Csv.Field × List (List (Option Int32))) := some (labels, [[some 7, some 7]])

#guard observe (limits 0) zeroRows == some (original, some (labels, []), [],
  ⟨expectedFields, [[]]⟩, [], .eos)
#guard observe (limits 3) mixedRows == some (original, some (labels, expected), expected,
  ⟨expectedFields, [expected.map (List.map (Option.map Arrow.Value.int32))]⟩, expected, .eos)
#guard (convert db 0 schema (limits 3) []).map Result.csv =
  .error (.writeParquet (.destination .nameConflict))
#guard (convert db 1 schema (limits 3) (utf8 "値,café\r\n")).map Result.csv =
  .error (.writeParquet (.csv .headerMismatch))
#guard (convert db 1 schema (limits 2) mixedRows).map Result.csv =
  .error (.exportCsv (.input (.readError (.decode 0 (.profile .rowLimit)))))
#guard (convert db 1 schema {limits 3 with ipc := {totalRows := 2}} mixedRows).map Result.csv =
  .error (.writeIpc (.writer (.limit .totalRows)))

#print axioms FlatInt32Writer.FromCsv.convert_written
#print axioms convert_of_admitted
#print axioms convert_readback

end Silmaril.Formats.Csv.ParquetIpc
