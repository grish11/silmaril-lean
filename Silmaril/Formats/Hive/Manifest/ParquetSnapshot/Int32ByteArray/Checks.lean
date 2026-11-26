module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Defs

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet Silmaril.Relational
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

private def v1 : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-plain-byte-array-file/plain-byte-array-v1.parquet"⟩
private def v2 : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-plain-byte-array-file/plain-byte-array-v2.parquet"⟩
private def damaged : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-plain-byte-array-file/plain-byte-array-v2-bad-length.parquet"⟩
private def emptyMiddle : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int32-byte-array-file/empty-middle-v2.parquet"⟩

private def ordinal : Field := ⟨"ordinal", .required⟩
private def payload : Field := ⟨"payload", .optional⟩
private def physical := Int32ByteArrayGroup.File.schema ordinal payload

private def partition (name : String) : PartitionSchema Kind :=
  ⟨#[⟨name, .int32 .optional, .asNull⟩]⟩

private def years := partition "year"
private def keys := partition "key"

private def convert : TypedPartitions.Convert Value String := fun field text =>
  match field.kind with
  | .int32 _ =>
    match text.toInt? with
    | none => .error "expected INT32 partition"
    | some ordinal => .ok (Int32.ofInt ordinal)
  | .byteArray _ => .ok ⟨text.toUTF8⟩

private def first := "year=%37/v1.parquet"
private def nullYear := "year=__HIVE_DEFAULT_PARTITION__/v2.parquet"
private def omitted := "v2.parquet"
private def late := "year=%38/bad.parquet"
private def missing := "year=9/missing.parquet"
private def middle := "year=7/middle.parquet"
private def collision := "key=8/collision.parquet"
private def beforeCollision := "key=7/middle.parquet"

private def lookup : String → Except String Bytes
  | "year=%37/v1.parquet" | "key=8/collision.parquet" => .ok v1
  | "year=__HIVE_DEFAULT_PARTITION__/v2.parquet" | "v2.parquet" => .ok v2
  | "year=%38/bad.parquet" => .ok damaged
  | "year=7/middle.parquet" | "key=7/middle.parquet" => .ok emptyMiddle
  | _ => .error "snapshot missing"

private abbrev Failure := FileError (Int32ByteArray.Error String)
private abbrev Cell := Sum (Option Int32) (Option Bytes)

private def observeRow {output : Scan.Schema String Kind} (row : Scan.Row output Value) : List Cell :=
  List.ofFn fun i =>
    match kind : (output.kind i).2 with
    | .int32 _ => .inl (cast (congrArg (fun k => Option (Value k)) kind) (row i))
    | .byteArray _ => .inr (cast (congrArg (fun k => Option (Value k)) kind) (row i))

private def projected (partitions : PartitionSchema Kind)
    (projection : Scan.Projection (partitions.extend physical)) (keep : Scan.Predicate partitions.toScan Value)
    (paths : List String) (expected : List (List (List Cell))) (outcome : Events.Termination Failure) : Bool :=
  match prepare physical partitions {} convert paths with
  | .error _ => false
  | .ok files =>
    let trace := scan (int32ByteArraySnapshotOpener {} ordinal payload partitions lookup) projection keep files
    trace.batches.map (fun batch => batch.toRows.map observeRow) == expected &&
      trace.batches.map (·.rowCount) == expected.map List.length &&
      decide (trace.termination = outcome)

private def all (partitions : PartitionSchema Kind) : Scan.Predicate partitions.toScan Value :=
  fun _ => some true

private def keepExceptEight : Scan.Predicate years.toScan Value :=
  fun row => (row ⟨0, by decide⟩).map (· != (8 : Int32))

private def expectedRow (ordinal : Int32) (payload : Option Bytes) (year : Option Int32) : List Cell :=
  [.inl (some ordinal), .inr payload, .inl year]

private def expectedGroup (group : Nat) (year : Option Int32) : List (List Cell) :=
  let tag := group.toUInt8
  let values : List (Option (List UInt8)) :=
    [some [], none, some [0xFF, 0, 0x80, tag], some (List.replicate 48 120 ++ [tag]),
      none, none, none, none, some [0, tag], some [0xC3, 0xA9, tag], none,
      some (List.replicate 36 121 ++ [tag])]
  values.zipIdx.map fun (value, row) =>
    expectedRow (Int32.ofNat (group * 12 + row)) (value.map Bytes.ofList) year

private def expectedFile (year : Option Int32) : List (List (List Cell)) :=
  (List.range 3).map (fun group => expectedGroup group year)

private def expectedMiddle : List (List (List Cell)) :=
  [[expectedRow (-2147483648) none (some 7),
    expectedRow 0 (some Bytes.empty) (some 7),
    expectedRow 17 (some (Bytes.ofList [0xFF, 0])) (some 7)],
   [],
   [expectedRow 2147483647 (some (Bytes.ofList [0x80])) (some 7),
    expectedRow (-1) (some (Bytes.ofList [120, 121])) (some 7)]]

private def lateError : Events.Termination Failure :=
  .readError (.source late (.parquet (.groupFailure 1
    (.byteArray (.page 1 1 "payload" 1 646 (.decode (.scalar (.plain .truncated))))))))

#guard projected years (Scan.Projection.id _) (all years) [first, nullYear, first]
  (expectedFile (some 7) ++ expectedFile none ++ expectedFile (some 7)) .eos
#guard projected years (Scan.Projection.id _) (all years) [omitted] (expectedFile none) .eos
#guard projected years (Scan.Projection.id _) keepExceptEight [nullYear, first] (expectedFile (some 7)) .eos

private def reordered : Scan.Projection (years.extend physical) :=
  Scan.Projection.ofArray #[⟨2, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

#guard List.ofFn reordered.schema.kind ==
  [("year", .int32 .optional), ("payload", .byteArray .optional), ("year", .int32 .optional)]
#guard projected years reordered (all years) [first]
  ((expectedFile (some 7)).map (List.map fun row => [row[2]!, row[1]!, row[2]!])) .eos

#guard projected years (Scan.Projection.id _) (all years) [middle] expectedMiddle .eos
#guard projected years (Scan.Projection.ofArray #[]) (all years) [middle]
  [List.replicate 3 [], [], List.replicate 2 []] .eos

#guard projected years (Scan.Projection.id _) (all years) [first, late, missing]
  (expectedFile (some 7) ++ [expectedGroup 0 (some 8)]) lateError
#guard projected years reordered keepExceptEight [late, missing] [] lateError
#guard projected years (Scan.Projection.ofArray #[]) (all years) [late, missing]
  [List.replicate 12 []] lateError
#guard projected years (Scan.Projection.ofArray #[]) keepExceptEight [middle, late, missing]
  [List.replicate 3 [], [], List.replicate 2 []] lateError
#guard projected years (Scan.Projection.id _) (all years) [missing, first] []
  (.readError (.open missing (.lookup "snapshot missing")))

#guard projected keys (Scan.Projection.id _) (all keys) [beforeCollision, collision, "key=9/missing.parquet"] expectedMiddle
  (.readError (.open collision (.reservedPartition "key")))

#guard match int32ByteArraySnapshotOpener {} ⟨"absent", .required⟩ payload keys lookup collision with
  | .error reason => decide (reason = .parquet (.openFailure (.bind .int32 (.unknownLeaf "absent"))))
  | .ok _ => false

#print axioms scanInt32ByteArraySnapshots_eq_reference
#print axioms scanInt32ByteArraySnapshots_collect_eq_rows

end Silmaril.Formats.Hive.Manifest
