module

import Silmaril.Formats.Hive.WritePlan.Thms
meta import Silmaril.Formats.Hive.WritePlan.Defs

namespace Silmaril.Formats.Hive.WritePlan

open Silmaril.Relational
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

private def summarize (buckets : List (Bucket physical Cell)) : List (String × List (List (Option Int32))) :=
  buckets.map fun bucket =>
    (bucket.directory, bucket.rows.map fun cells => List.ofFn fun i => cells i)

private def observe (rows : Scan.Table (partitions.extend physical) Cell)
    (options : PartitionPath.Options := {}) :=
  (plan physical partitions options encode rows).map summarize

-- Assert the planner's order in Lean. The PyArrow fixture checks membership.
#guard observe input == .ok [
  ("region=a%2Fb/year=2025", [[some 10, none], [some 11, some 8], [some 10, none]]),
  ("region=__HIVE_DEFAULT_PARTITION__/year=2025", [[some 20, some 4], [some 21, none]]),
  ("region=%E6%97%A5%E6%9C%AC/year=2024", [[some 30, some 9]]),
  ("region=/year=2025", [[some 40, none]]),
  ("region=x%3Dy/year=__HIVE_DEFAULT_PARTITION__", [[some 50, some 2]])]

#guard observe [] == .ok []
#guard observe [second, first, second] == .ok [
  ("region=__HIVE_DEFAULT_PARTITION__/year=2025", [[some 20, some 4], [some 20, some 4]]),
  ("region=a%2Fb/year=2025", [[some 10, none]])]

private def sentinel := row 70 none (some "__HIVE_DEFAULT_PARTITION__") (some 2025)
private def rejected := row 71 none (some "bad text") (some (-1))

-- Sentinel ambiguity is rejected by Lean's existing render policy.
#guard observe [first, second, sentinel, rejected] ==
  .error (.row 2 (.render (.nullMarkerCollision "region")))

#guard observe [first, rejected, sentinel] ==
  .error (.row 1 (.encode "region" "rejected text"))

-- Within a row, encoders run in schema order before render admission.
#guard observe [row 72 none (some "__HIVE_DEFAULT_PARTITION__") (some (-1))] ==
  .error (.row 0 (.encode "year" "rejected integer"))

#guard observe [first] { requiredKeys := ["absent"] } ==
  .error (.row 0 (.render (.missingKey "absent")))

#guard observe [first] { nullMarker := "" } == .error (.row 0 (.render .emptyNullMarker))

private def collidingPhysical : Scan.Schema String Kind := ⟨1, fun _ => ("region", .text)⟩

#guard (plan collidingPhysical partitions {} encode []).map List.length ==
  .error (.schema (.physicalCollision "region"))

private def noPartition : PartitionSchema Kind := ⟨#[]⟩
private def rootRow (id : Int32) : Scan.Row (noPartition.extend physical) Cell :=
  extendRow (physicalRow id none) (fun i => Fin.elim0 i)

#guard (plan physical noPartition {} encode [rootRow 10, rootRow 11]).map summarize ==
  .ok [("", [[some 10, none], [some 11, none]])]

private def zeroPhysical : Scan.Schema String Kind := ⟨0, Fin.elim0⟩
private def zeroRow (region : Option String) : Scan.Row (partitions.extend zeroPhysical) Cell :=
  extendRow (fun i => Fin.elim0 i) (partitionRow region none)

#guard (plan zeroPhysical partitions {} encode [zeroRow (some "a"), zeroRow none, zeroRow (some "a")]).map
    (List.map fun bucket => (bucket.directory, bucket.rows.length)) ==
  .ok [("region=a/year=__HIVE_DEFAULT_PARTITION__", 2),
    ("region=__HIVE_DEFAULT_PARTITION__/year=__HIVE_DEFAULT_PARTITION__", 1)]

#print axioms plan_eq_reference
#print axioms plan_first_row_error_iff

end Silmaril.Formats.Hive.WritePlan
