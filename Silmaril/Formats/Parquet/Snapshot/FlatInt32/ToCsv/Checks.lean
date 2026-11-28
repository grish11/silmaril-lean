module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Snapshot.FlatInt32.ToCsv.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Snapshot.FlatInt32.ToCsv.Defs

namespace Silmaril.Formats.Parquet.Snapshot.FlatInt32.ToCsv

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Relational.NamedTable (Packed)

private def v1 : Bytes := ⟨include_bytes "../../../../../../tools/parquet-flat-scan/fixtures/flat-plain-v1.parquet"⟩
private def v2 : Bytes := ⟨include_bytes "../../../../../../tools/parquet-flat-scan/fixtures/flat-plain-v2.parquet"⟩

-- Compact STOP at the first PageHeader of the second row group. The footer is unchanged.
private def late : Bytes := ⟨(v2.data.extract 0 234).push 0 ++ v2.data.extract 235 v2.length⟩

private def expected : Scan.Schema String Unit :=
  ⟨2, fun i => (if i.val = 0 then "required_i32" else "optional_i32", ())⟩

private def reversed : Scan.Schema String Unit :=
  ⟨2, fun i => (if i.val = 0 then "optional_i32" else "required_i32", ())⟩

private def utf8 (text : String) : Csv.Bytes := text.toByteArray.data.toList

private def db : Packed Nat Csv.Field Cell := fun name =>
  if name = 0 then some ⟨csvSchema expected, [fun _ => some 201]⟩ else none

private def observed (database : Packed Nat Csv.Field Cell) (name : Nat) :
    Option (List (List (Option Int32))) :=
  (Scan.observePacked database name).map fun table => table.rows.map List.ofFn

private def rows : List (List (Option Int32)) := (List.range 24).map fun i =>
  [some (Int32.ofInt (10 * (i : Int) - 17)),
    if i % 3 = 0 then none else some (Int32.ofInt (-3 * (i : Int)))]

private def tag (value : Option Int32) : String :=
  match value with
  | none => "\"N\""
  | some n => "\"T" ++ toString n.toInt ++ "\""

private def wire : Csv.Bytes := utf8 ("\"required_i32\",\"optional_i32\"\r\n" ++
  String.join (rows.map fun row => ",".intercalate (row.map tag) ++ "\r\n"))

private def run (bytes : Bytes) := convert db 1 expected {} bytes

#guard (run v1).map Csv.EventStream.Result.wire = .ok wire
#guard (run v2).map Csv.EventStream.Result.wire = .ok wire
#guard (run v2).map (fun result => List.ofFn result.schema.kind) =
  .ok [(utf8 "required_i32", ()), (utf8 "optional_i32", ())]
#guard (run v2).map (fun result => (observed result.db 1, observed result.db 0)) =
  .ok (some rows, some [[some 201, some 201]])
#guard (run v2).map (fun result =>
  (Csv.Typed.Utf8.decode (csvSchema expected) codecs result.wire).map (List.map List.ofFn)) =
  .ok (.ok rows)
#guard List.ofFn (csvSchema ⟨1, fun _ => ("都市", ())⟩).kind = [(utf8 "都市", ())]

#guard (convert db 1 reversed {} v2).map Csv.EventStream.Result.wire =
  .error (.input (.openError (.schema (.schemaNames ["optional_i32", "required_i32"]
    ["required_i32", "optional_i32"]))))
#guard (run .empty).map Csv.EventStream.Result.wire =
  .error (.input (.openError (.footer (.framing .shortFile))))

private def lateError : Snapshot.Error (Error Unit) :=
  .decode 1 (.profile (.page (.header (.missingField 1))))

#guard (readEvents {} expected late).collect.map (fun source =>
  (source.table.rows.map List.ofFn, source.termination)) = .ok (rows.take 12, .readError lateError)
#guard (run late).map (fun result => (observed result.db 1, result.wire)) =
  .error (.input (.readError lateError))
#guard (convert db 0 expected {} late).map Csv.EventStream.Result.wire = .error (.input .nameConflict)

#print axioms collect_readEvents
#print axioms convert_roundTrip
#print axioms convert_read_error

end Silmaril.Formats.Parquet.Snapshot.FlatInt32.ToCsv
