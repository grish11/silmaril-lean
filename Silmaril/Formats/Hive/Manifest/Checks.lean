module

import Silmaril.Formats.Hive.Manifest.Thms
meta import Silmaril.Formats.Hive.Manifest.Defs

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema Convert)

local instance {E A : Type} [BEq E] [BEq A] : BEq (Except E A) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

local instance : BEq (Events.Termination (FileError String)) where
  beq a b := decide (a = b)

private abbrev Value (_ : Unit) := Nat
private def physical : Scan.Schema String Unit := ⟨1, fun _ => ("value", ())⟩
private def virtual : PartitionSchema Unit := ⟨#[⟨"year", (), .asNull⟩]⟩

private def convert : Convert Value String := fun _ text =>
  match text.toNat? with
  | some number => .ok number
  | none => .error "expected a natural number"

private def escaped : String := "year=%37/first%2f=opaque.parquet"

private def paths (declarations : List String) : Except (PrepareError String) (List FilePath) :=
  (prepare physical virtual {} convert declarations).map (List.map File.path)

#guard paths [escaped, "root=literal.parquet", escaped] ==
  .ok [⟨escaped, "year=7", "first%2f=opaque.parquet"⟩,
    ⟨"root=literal.parquet", "", "root=literal.parquet"⟩, ⟨escaped, "year=7", "first%2f=opaque.parquet"⟩]
#guard paths ["/year=7/file"] == .error (.relativePath "/year=7/file" .invalidSegment)
#guard paths ["year=7//file"] == .error (.relativePath "year=7//file" .invalidSegment)
#guard paths ["year=7/../file"] == .error (.relativePath "year=7/../file" .invalidSegment)
#guard paths ["year=7/"] == .error (.relativePath "year=7/" .missingFilename)
#guard paths ["C:file"] == .error (.relativePath "C:file" .invalidCharacter)
#guard paths ["year=7\\file"] == .error (.relativePath "year=7\\file" .invalidCharacter)
#guard paths ["year=%/file"] == .error (.partitionPath "year=%/file" .invalidEscape)
#guard paths ["year=7/%79ear=8/file"] ==
  .error (.partitionPath "year=7/%79ear=8/file" (.duplicateKey "year"))
#guard paths ["month=7/file"] == .error (.binding "month=7/file" (.unknownKey "month"))
#guard paths ["year=/file"] ==
  .error (.binding "year=/file" (.conversion "year" "expected a natural number"))
#guard (prepare physical ⟨#[⟨"value", (), .reject⟩]⟩ {} convert []).map List.length ==
  .error (.schema (.physicalCollision "value"))

private def readGroup : Nat → Except String (Scan.Table physical Value)
  | 0 => .ok [fun _ => some 10]
  | 1 => .ok [fun _ => some 20]
  | 2 => .error "bad group"
  | _ => .ok [fun _ => some 30]

private def source (groups : List Nat) : Parquet.Reader.Source Nat physical Value String :=
  ⟨groups, readGroup, fun remaining => if remaining.isEmpty then .error "cleanup" else .ok ()⟩

private def openFile : Opener Nat physical Value String
  | "year=%37/first%2f=opaque.parquet" => .ok ⟨source [0], 2⟩
  | "year=7/empty.parquet" => .ok ⟨source [], 1⟩
  | "root=literal.parquet" => .ok ⟨source [3], 2⟩
  | "year=__HIVE_DEFAULT_PARTITION__/null.parquet" => .ok ⟨source [3], 2⟩
  | "year=7/last.parquet" => .ok ⟨source [3], 2⟩
  | "year=7/bad.parquet" | "year=8/bad.parquet" => .ok ⟨source [1, 2, 3], 4⟩
  | "year=7/early.parquet" => .ok ⟨source [1, 3], 1⟩
  | "year=7/close-error.parquet" => .ok ⟨source [1], 1⟩
  | _ => .error "missing source"

private def projection : Scan.Projection (virtual.extend physical) :=
  Scan.Projection.ofArray (#[1, 0] : Array (Fin 2))

private def keep : Scan.Predicate virtual.toScan Value :=
  fun cells => (cells (0 : Fin 1)).map (fun (year : Nat) => year == 7)

private def observe (declarations : List String) :
    Except (PrepareError String) (List (List (Option Nat)) × Events.Termination (FileError String)) :=
  (prepare physical virtual {} convert declarations).map fun files =>
    let trace := scan openFile projection keep files
    (trace.rows.map List.ofFn, trace.termination)

#guard observe [] == .ok ([], .eos)
#guard observe [escaped, "year=7/empty.parquet", "root=literal.parquet",
    "year=__HIVE_DEFAULT_PARTITION__/null.parquet", escaped, "year=7/last.parquet"] ==
  .ok ([[some 7, some 10], [some 7, some 10], [some 7, some 30]], .eos)

#guard observe [escaped, "year=8/absent.parquet", "year=7/bad.parquet"] ==
  .ok ([[some 7, some 10]], .readError (.open "year=8/absent.parquet" "missing source"))

#guard observe [escaped, "year=7/bad.parquet", "year=8/absent.parquet"] ==
  .ok ([[some 7, some 10], [some 7, some 20]], .readError (.source "year=7/bad.parquet" "bad group"))

#guard observe [escaped, "year=8/bad.parquet", "year=7/last.parquet"] ==
  .ok ([[some 7, some 10]], .readError (.source "year=8/bad.parquet" "bad group"))

#guard observe ["year=7/early.parquet", "year=8/absent.parquet"] ==
  .ok ([[some 7, some 20]], .closed)

#guard observe ["year=7/close-error.parquet", "year=7/last.parquet"] ==
  .ok ([[some 7, some 20]], .closeError (.source "year=7/close-error.parquet" "cleanup"))

#print axioms prepare_preserves_paths
#print axioms scan_open_failure
#print axioms scan_first_terminal

end Silmaril.Formats.Hive.Manifest
