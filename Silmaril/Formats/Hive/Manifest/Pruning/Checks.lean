module

import Silmaril.Formats.Hive.Manifest.Pruning.Thms
meta import Silmaril.Formats.Hive.Manifest.Pruning.Defs

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema Convert)

local instance : BEq (Events.Termination (FileError String)) where
  beq a b := decide (a = b)

private abbrev Value (_ : Unit) := Nat
private def physical : Scan.Schema String Unit := ⟨1, fun _ => ("value", ())⟩
private def virtual : PartitionSchema Unit := ⟨#[⟨"year", (), .asNull⟩]⟩

private def convert : Convert Value String := fun _ text =>
  match text.toNat? with
  | some year => .ok year
  | none => .error "expected a natural number"

private def readGroup (group : Nat) : Except String (Scan.Table physical Value) :=
  if group == 99 then .error "bad group" else .ok [fun _ => some group]

private def source (groups : List Nat) (close : Except String Unit := .ok ()) :
    Parquet.Reader.Source Nat physical Value String :=
  ⟨groups, readGroup, fun _ => close⟩

private def openFile : Opener Nat physical Value String
  | "year=7/first.parquet" => .ok ⟨source [10], 2⟩
  | "year=7/last.parquet" => .ok ⟨source [20], 2⟩
  | "year=8/false.parquet" => .ok ⟨source [30], 2⟩
  | "year=__HIVE_DEFAULT_PARTITION__/unknown.parquet" => .ok ⟨source [], 1⟩
  | "year=7/bad.parquet" | "year=8/bad.parquet" => .ok ⟨source [30, 99], 3⟩
  | "year=7/closed.parquet" | "year=8/closed.parquet" => .ok ⟨source [30], 1⟩
  | "year=7/close-error.parquet" | "year=8/close-error.parquet" => .ok ⟨source [30] (.error "cleanup"), 1⟩
  | _ => .error "missing source"

private def projection : Scan.Projection (virtual.extend physical) :=
  Scan.Projection.ofArray (#[1, 0] : Array (Fin 2))

private def keep : Scan.Predicate virtual.toScan Value :=
  fun cells => (cells (0 : Fin 1)).map (fun (year : Nat) => year == 7)

private def observe
    (run : List (File virtual Value) → Events.Trace projection.schema Value (FileError String))
    (paths : List String) :
    Option (List (List (Option Nat)) × Events.Termination (FileError String)) :=
  match prepare physical virtual {} convert paths with
  | .error _ => none
  | .ok files =>
    let trace := run files
    some (trace.rows.map List.ofFn, trace.termination)

private def strict := observe (scan openFile projection keep)
private def skipping := observe (scanSkippingRejected openFile projection keep)

private def exhausted := ["year=7/first.parquet", "year=8/false.parquet",
  "year=__HIVE_DEFAULT_PARTITION__/unknown.parquet", "year=7/last.parquet", "year=7/first.parquet"]

#guard skipping [] == some ([], .eos)
#guard strict exhausted == skipping exhausted
#guard skipping exhausted == some ([[some 7, some 10], [some 7, some 20], [some 7, some 10]], .eos)

-- This rejected file opens and yields a group before hitting a read error.
private def rejectedFailure := ["year=7/first.parquet", "year=8/bad.parquet", "year=7/last.parquet"]
#guard strict rejectedFailure ==
  some ([[some 7, some 10]], .readError (.source "year=8/bad.parquet" "bad group"))
#guard skipping rejectedFailure == some ([[some 7, some 10], [some 7, some 20]], .eos)

#guard strict ["year=8/missing.parquet"] ==
  some ([], .readError (.open "year=8/missing.parquet" "missing source"))
#guard skipping ["year=8/missing.parquet"] == some ([], .eos)
#guard skipping ["year=__HIVE_DEFAULT_PARTITION__/missing.parquet"] == some ([], .eos)

-- A pull budget that ends after the final batch still closes before observing EOF.
#guard strict ["year=8/closed.parquet"] == some ([], .closed)
#guard skipping ["year=8/closed.parquet"] == some ([], .eos)
#guard strict ["year=8/close-error.parquet"] ==
  some ([], .closeError (.source "year=8/close-error.parquet" "cleanup"))
#guard skipping ["year=8/close-error.parquet"] == some ([], .eos)

private def retainedFailure := ["year=8/false.parquet", "year=7/bad.parquet", "year=7/last.parquet"]
#guard strict retainedFailure == skipping retainedFailure
#guard skipping retainedFailure ==
  some ([[some 7, some 30]], .readError (.source "year=7/bad.parquet" "bad group"))

private def failureBeforeRejected :=
  ["year=7/first.parquet", "year=7/bad.parquet", "year=8/bad.parquet"]

#guard strict failureBeforeRejected ==
  some ([[some 7, some 10], [some 7, some 30]], .readError (.source "year=7/bad.parquet" "bad group"))
#guard skipping failureBeforeRejected == strict failureBeforeRejected

private def closeBeforeRejected :=
  ["year=7/first.parquet", "year=7/closed.parquet", "year=8/bad.parquet"]

#guard strict closeBeforeRejected == some ([[some 7, some 10], [some 7, some 30]], .closed)
#guard skipping closeBeforeRejected == strict closeBeforeRejected

private def closeErrorBeforeRejected :=
  ["year=7/first.parquet", "year=7/close-error.parquet", "year=8/bad.parquet"]

#guard strict closeErrorBeforeRejected ==
  some ([[some 7, some 10], [some 7, some 30]], .closeError (.source "year=7/close-error.parquet" "cleanup"))
#guard skipping closeErrorBeforeRejected == strict closeErrorBeforeRejected

#guard strict rejectedFailure != skipping rejectedFailure

#print axioms scanSkippingRejected_eq_scan_of_reached_eof
#print axioms RejectedFilesReachEOF.reached
#print axioms scanSkippingRejected_eq_scan
#print axioms scanSkippingRejected_equivalent
#print axioms scanSkippingRejected_not_equivalent_singleton

end Silmaril.Formats.Hive.Manifest
