module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Hive.WritePlan.Restore.Thms
import Silmaril.Formats.Hive.PartitionPath.Thms
import Silmaril.Formats.Parquet.Snapshot.FlatInt32.Defs
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Snapshot.FlatInt32.Defs
meta import Silmaril.Formats.Hive.WritePlan.Restore.Defs

namespace Silmaril.Formats.Hive.WritePlan

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema extendRow)

local instance {E A : Type} [BEq E] [BEq A] : BEq (Except E A) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

private inductive Kind where
  | text
  | int32

private abbrev Cell : Kind → Type
  | .text => String
  | .int32 => Int32

private def physical : Scan.Schema String Kind :=
  ⟨2, fun i => (if i.val == 0 then "id" else "amount", .int32)⟩

private def partitions : PartitionSchema Kind :=
  ⟨#[⟨"region", .text, .reject⟩, ⟨"year", .int32, .reject⟩]⟩

private def physicalRow (id : Int32) (amount : Option Int32) : Scan.Row physical Cell :=
  fun i => if i.val == 0 then some id else amount

private def partitionRow (region : Option String) (year : Option Int32) : Scan.Row partitions.toScan Cell :=
  fun i => Fin.cases (motive := fun j : Fin 2 => Option (Cell (partitions.toScan.kind j).2))
    region (fun j => by rw [Fin.fin_one_eq_zero j]; exact year) i

private def row (id : Int32) (amount : Option Int32) (region : Option String) (year : Option Int32) :
    Scan.Row (partitions.extend physical) Cell :=
  extendRow (physicalRow id amount) (partitionRow region year)

private def encode : Encode Cell String
  | ⟨_, .text, _⟩, text => if text == "bad text" then .error "rejected text" else .ok text
  | ⟨_, .int32, _⟩, value =>
    if value == -1 then .error "rejected integer" else .ok (toString value.toInt)

private def first := row 10 none (some "a/b") (some 2025)
private def second := row 20 (some 4) none (some 2025)

-- Same input and output membership as the independent PyArrow fixture.
private def input : Scan.Table (partitions.extend physical) Cell :=
  [first, second, row 11 (some 8) (some "a/b") (some 2025),
   row 30 (some 9) (some "日本") (some 2024), row 40 none (some "") (some 2025),
   row 21 none none (some 2025), row 50 (some 2) (some "x=y") none, first]

private def decode : TypedPartitions.Convert Cell String
  | ⟨_, .text, _⟩, text => .ok text
  | ⟨_, .int32, _⟩, text =>
    match text.toInt? with
    | none => .error "expected decimal"
    | some ticks =>
      let value := Int32.ofInt ticks
      if value.toInt == ticks then .ok value else .error "outside Int32"

private def readPlan (options : PartitionPath.Options) (buckets : List (Bucket physical Cell)) :=
  (restore physical partitions options decode buckets).mapError (fun _ => "restore")

private def observe (rows : Scan.Table (partitions.extend physical) Cell) :
    List (Option Int32 × Option Int32 × Option String × Option Int32) :=
  rows.map fun r =>
    let payload := TypedPartitions.physicalCells (physical := physical) (schema := partitions) r
    let virtual := TypedPartitions.partitionCells (physical := physical) (schema := partitions) r
    (payload (0 : Fin 2), payload (1 : Fin 2), virtual (0 : Fin 2), virtual (1 : Fin 2))

private def reconstructed :=
  ((plan physical partitions {} encode input).mapError (fun _ => "plan") >>= readPlan {}).map observe

private def grouped :=
  observe [first, row 11 (some 8) (some "a/b") (some 2025), first, second, row 21 none none (some 2025),
    row 30 (some 9) (some "日本") (some 2024), row 40 none (some "") (some 2025), row 50 (some 2) (some "x=y") none]

#guard reconstructed == .ok grouped
#guard reconstructed != .ok (observe input)
#guard observe (groupOriginalRows {} encode input) == grouped

private def wire : Scan.Schema String Unit :=
  ⟨2, fun i => (if i.val == 0 then "id" else "amount", ())⟩

private def fetchBucket (directory : String) (bytes : Bytes) : Except String (Bucket physical Cell) := do
  let source ← (Snapshot.openSource {} (Snapshot.FlatInt32.bind (InputFailure := Unit) {} wire) bytes)
    |>.mapError (fun _ => "wire open")
  let (groups, outcome) := Reader.denoteGroups source.readGroup source.groups
  if outcome = .eos then
    return ⟨directory, groups.flatten.map (fun r i => r i)⟩
  else
    throw "wire group read"

private def fixtureBuckets : Except String (List (Bucket physical Cell)) :=
  [
    ("region=a%2Fb/year=2025",
      ⟨include_bytes "../../../../../tools/parquet-flat-scan/fixtures/hive-write-plan/region=a%2Fb/year=2025/part-0.parquet"⟩),
    ("region=__HIVE_DEFAULT_PARTITION__/year=2025",
      ⟨include_bytes "../../../../../tools/parquet-flat-scan/fixtures/hive-write-plan/region=__HIVE_DEFAULT_PARTITION__/year=2025/part-0.parquet"⟩),
    ("region=%E6%97%A5%E6%9C%AC/year=2024",
      ⟨include_bytes "../../../../../tools/parquet-flat-scan/fixtures/hive-write-plan/region=%E6%97%A5%E6%9C%AC/year=2024/part-0.parquet"⟩),
    ("region=/year=2025",
      ⟨include_bytes "../../../../../tools/parquet-flat-scan/fixtures/hive-write-plan/region=/year=2025/part-0.parquet"⟩),
    ("region=x%3Dy/year=__HIVE_DEFAULT_PARTITION__",
      ⟨include_bytes "../../../../../tools/parquet-flat-scan/fixtures/hive-write-plan/region=x%3Dy/year=__HIVE_DEFAULT_PARTITION__/part-0.parquet"⟩)
  ].mapM fun (directory, bytes) => fetchBucket directory bytes

#guard (fixtureBuckets >>= readPlan {}).map observe == .ok grouped

private def overwriteText : Encode Cell String
  | ⟨_, .text, _⟩, _ => .ok "fixed"
  | ⟨_, .int32, _⟩, value => .ok (toString value.toInt)

private def lossy :=
  ((plan physical partitions {} overwriteText [first]).mapError (fun _ => "plan") >>= readPlan {}).map observe

#guard lossy == .ok (observe [row 10 none (some "fixed") (some 2025)])
#guard lossy != .ok (observe [first])

private def custom : PartitionPath.Options := { nullMarker := "null/=" }
private def customPath := "region=null%2F%3D/year=2025"
private def customBuckets : List (Bucket physical Cell) := [⟨customPath, [physicalRow 20 (some 4)]⟩]

#guard (((plan physical partitions custom encode [second]).mapError (fun _ => "plan")) >>= readPlan custom).map
    observe == .ok (observe [second])

#guard (PartitionPath.render custom [] >>= PartitionPath.parse custom) == .ok []

#guard (restore physical partitions custom decode customBuckets).map observe == .ok (observe [second])
#guard (restore physical partitions {} decode customBuckets).map observe ==
  .ok (observe [row 20 (some 4) (some "null/=") (some 2025)])

#guard (restore physical partitions {} decode [⟨"missing-equals", []⟩]).map observe ==
  .error (.path "missing-equals" (.missingEquals "missing-equals"))

#guard (restore physical partitions {} decode [⟨"region=x/year=bad", []⟩]).map observe ==
  .error (.binding "region=x/year=bad" (.conversion "year" "expected decimal"))

#print axioms PartitionPath.parse_render_of_ok
#print axioms restore_plan_eq_groupedRows

end Silmaril.Formats.Hive.WritePlan
