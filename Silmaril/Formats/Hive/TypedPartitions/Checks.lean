module

import Silmaril.Formats.Hive.TypedPartitions.Thms
meta import Silmaril.Formats.Hive.TypedPartitions.Defs

namespace Silmaril.Formats.Hive.TypedPartitions

open Silmaril.Relational

local instance {α : Type} [BEq α] : BEq (Except (Error String) α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

private inductive Kind
  | text
  | number

private def Value : Kind → Type
  | .text => String
  | .number => Nat

private def physical : Scan.Schema String Kind := ⟨1, fun _ => ("payload", .number)⟩

private def partitions : PartitionSchema Kind :=
  ⟨#[⟨"label", .text, .asNull⟩, ⟨"year", .number, .reject⟩]⟩

private def convert : Convert Value String
  | ⟨_, .text, _⟩, text => .ok text
  | ⟨_, .number, _⟩, text =>
    match text.toNat? with
    | some n => .ok n
    | none => .error "expected a natural number"

private def fragment (entries : PartitionPath.Partition) (payloads : List Nat) :
    InputPartition physical Value :=
  ⟨entries, payloads.map fun n _ => some n⟩

private def manifest : List (InputPartition physical Value) :=
  [fragment [("year", some "2026"), ("label", some "")] [8, 8, 2],
   fragment [("year", none), ("label", some "null year")] [9],
   fragment [("year", some "2026")] [],
   fragment [("year", some "2025")] [3],
   fragment [("year", some "2026"), ("label", none)] [4]]

private def view (row : Scan.Row (partitions.extend physical) Value) :
    Option Nat × Option String × Option Nat :=
  (row (0 : Fin 3), row (1 : Fin 3), row (2 : Fin 3))

private def yearPredicate : Scan.Predicate partitions.toScan Value :=
  fun cells => (cells (1 : Fin 2)).map (fun (year : Nat) => year == 2026)

private def projection : Scan.Projection (partitions.extend physical) :=
  Scan.Projection.ofArray (#[2, 0, 1] : Array (Fin 3))

private def scanView (row : Scan.Row projection.schema Value) :
    Option Nat × Option Nat × Option String :=
  (row (0 : Fin 3), row (1 : Fin 3), row (2 : Fin 3))

#guard (prepare partitions convert manifest).map (fun typed => typed.map (·.rows.length)) ==
  .ok [3, 1, 0, 1, 1]

#guard (prepare partitions convert manifest).map (fun typed => (materialize typed).map view) ==
  .ok [(some 8, some "", some 2026), (some 8, some "", some 2026), (some 2, some "", some 2026),
    (some 9, some "null year", none), (some 3, none, some 2025), (some 4, none, some 2026)]

#guard (prepare partitions convert manifest).map
    (fun typed => (scanPartitions projection yearPredicate typed).map scanView) ==
  .ok [(some 2026, some 8, some ""), (some 2026, some 8, some ""), (some 2026, some 2, some ""),
    (some 2026, some 4, none)]

private def checkedCount (schema : PartitionSchema Kind) (input : List (InputPartition physical Value)) :
    Except (Error String) Nat :=
  (prepare schema convert input).map (fun typed => (materialize typed).length)

#guard checkedCount partitions [] == .ok 0
#guard checkedCount partitions [fragment [("year", none)] [1]] == .ok 1
#guard checkedCount partitions [fragment [] []] == .error (.missingKey "year")
#guard checkedCount partitions [fragment [("year", none), ("year", none)] []] ==
  .error (.partitionKeys (.duplicateKey "year"))
#guard checkedCount partitions [fragment [("", some ""), ("year", some "2026")] []] ==
  .error (.partitionKeys .emptyKey)
#guard checkedCount partitions [fragment [("year", none), ("Year", some "2026")] []] ==
  .error (.unknownKey "Year")
#guard checkedCount partitions [fragment [("year", some "")] []] ==
  .error (.conversion "year" "expected a natural number")
#guard checkedCount partitions [fragment [("year", some "twenty")] [1]] ==
  .error (.conversion "year" "expected a natural number")
#guard checkedCount ⟨#[⟨"year", .number, .reject⟩, ⟨"year", .text, .asNull⟩]⟩ [] ==
  .error (.schemaKeys (.duplicateKey "year"))
#guard checkedCount ⟨#[⟨"payload", .text, .asNull⟩]⟩ [] ==
  .error (.physicalCollision "payload")

private def noPhysical : Scan.Schema String Kind := ⟨0, Fin.elim0⟩
private def noPartitions : PartitionSchema Kind := ⟨#[]⟩
private def zeroRow : Scan.Row noPhysical Value := fun i => nomatch i
private def zeroColumns : List (InputPartition noPhysical Value) :=
  [⟨[], [zeroRow, zeroRow]⟩]

#guard (prepare noPartitions convert zeroColumns).map (fun typed => (materialize typed).length) ==
  .ok 2

#print axioms physicalCells_extendRow
#print axioms partitionCells_extendRow
#print axioms prepare_preserves_rows
#print axioms materialize_preserves_order
#print axioms materialize_rowCount
#print axioms scanPartitions_eq_scan

end Silmaril.Formats.Hive.TypedPartitions
