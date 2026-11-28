module

import Silmaril.Formats.Hive.ParquetScan.Thms

namespace Silmaril.Formats.Hive.ParquetScan

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)

private abbrev Value (_ : Unit) := Nat
private def physical : Scan.Schema String Unit := ⟨1, fun _ => ("value", ())⟩
private def virtual : PartitionSchema Unit := ⟨#[⟨"partition", (), .reject⟩]⟩

private def readGroup : Nat → Except String (Scan.Table physical Value)
  | 0 => .ok [fun _ => some 10, fun _ => some 10]
  | 1 => .ok []
  | 2 => .ok [fun _ => some 20]
  | 3 => .ok [fun _ => some 30]
  | 4 => .error "bad group"
  | _ => .ok [fun _ => some 50]

private def source (groups : List Nat) : Parquet.Reader.Source Nat physical Value String :=
  ⟨groups, readGroup, fun rest => if rest.isEmpty then .error "cleanup" else .ok ()⟩

private def file (groups : List Nat) : Events.Trace physical Value String :=
  readFile (source groups) (groups.length + 1)

private abbrev Part := Partition physical virtual Value String

private def part (tag : Option Nat) (files : List (Events.Trace physical Value String)) : Part :=
  ⟨fun _ => tag, files⟩

private def projection : Scan.Projection (virtual.extend physical) :=
  Scan.Projection.ofArray (#[1, 0] : Array (Fin 2))

private def keep : Scan.Predicate virtual.toScan Value :=
  fun cells => (cells (0 : Fin 1)).map (fun tag : Nat => tag == 7)

private def snapshot (trace : Events.Trace projection.schema Value String) :
    List (List (Option Nat)) × Events.Termination String :=
  (trace.rows.map List.ofFn, trace.termination)

private def hoisted (manifest : List Part) := snapshot (scanHoisted manifest projection keep)
private def rowwise (manifest : List Part) := snapshot (scanRowwise manifest projection keep)

private def first : Part := part (some 7) [file [0, 1], file [2]]
private def last : Part := part (some 7) [file [3]]

example : (Parquet.Reader.readAll (.ok ⟨physical, source [0, 1, 2]⟩)).collect =
    .ok (file [0, 1, 2]).collect := rfl

example : hoisted [first, part (some 7) [], part (some 8) [file [3]], part none [file [5]], last] =
    ([[some 7, some 10], [some 7, some 10], [some 7, some 20], [some 7, some 30]], .eos) := rfl

example : hoisted [part none []] = ([], .eos) := rfl

private def filteredFailure : List Part :=
  [first, part (some 8) [file [3, 4, 5], file [5]], last]

/-- The filtered file still contributes its failure. The later file and partition are unobserved. -/
example : hoisted filteredFailure =
    ([[some 7, some 10], [some 7, some 10], [some 7, some 20]], .readError "bad group") := rfl

example : rowwise filteredFailure =
    ([[some 7, some 10], [some 7, some 10], [some 7, some 20]], .readError "bad group") := rfl

/-- Omitting the filtered file altogether hides its error and admits later rows. -/
example : hoisted [first, last] =
    ([[some 7, some 10], [some 7, some 10], [some 7, some 20], [some 7, some 30]], .eos) := rfl

/-- A kept file retains the rows it emitted before failing. -/
example : hoisted [part (some 7) [file [3, 4, 5]], last] =
    ([[some 7, some 30]], .readError "bad group") := rfl

example : hoisted [part (some 7) [readFile (source [3, 5]) 1, file [5]], last] =
    ([[some 7, some 30]], .closed) := rfl

example : hoisted [part none [readFile (source [3, 5]) 1], last] = ([], .closed) := rfl

example : hoisted [part (some 7) [readFile (source [3]) 1], last] =
    ([[some 7, some 30]], .closeError "cleanup") := rfl

example : hoisted [part (some 8) [readFile (source [3]) 1], last] =
    ([], .closeError "cleanup") := rfl

private def noColumns : Scan.Projection (virtual.extend physical) :=
  Scan.Projection.ofArray #[]

example : (scanHoisted filteredFailure noColumns keep).rows.length = 3 := rfl
example : (scanHoisted filteredFailure noColumns keep).termination = .readError "bad group" := rfl

#print axioms readFile_eq_reader
#print axioms assemble_eof
#print axioms assemble_stops
#print axioms rows_extendTrace
#print axioms scanHoisted_equivalent

end Silmaril.Formats.Hive.ParquetScan
