module

public import Silmaril.Formats.Hive.Manifest.Pruning.Defs
import Silmaril.Formats.Hive.ParquetScan.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.Pruning

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Hive
open Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)

variable {Kind Group Error : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}
variable (opener : Opener Group physical Value Error)
variable (projection : Scan.Projection (schema.extend physical))
variable (predicate : Scan.Predicate schema.toScan Value)

private theorem scanFile_rejected (file : File schema Value)
    (reject : (predicate file.cells).getD false = false) :
    scanFile opener projection predicate file =
      ⟨[], (scanFile opener projection predicate file).termination⟩ := by
  cases opened : opener file.path.declared <;> simp
    [scanFile, opened, ParquetScan.scanPartition, reject]

private theorem scanFileSkippingRejected_eq_scanFile (file : File schema Value)
    (eof : (predicate file.cells).getD false = false →
      (scanFile opener projection predicate file).termination = .eos) :
    scanFileSkippingRejected opener projection predicate file =
      scanFile opener projection predicate file := by
  cases keep : (predicate file.cells).getD false
  · rw [scanFile_rejected opener projection predicate file keep, eof keep]
    simp [scanFileSkippingRejected, keep]
  · cases opened : opener file.path.declared <;>
      simp [scanFileSkippingRejected, keep, scanFile, opened, ParquetScan.scanPartition]

theorem scanSkippingRejected_eq_scan_filter (files : List (File schema Value)) :
    scanSkippingRejected opener projection predicate files =
      scan opener projection predicate (files.filter fun file => (predicate file.cells).getD false) := by
  unfold scanSkippingRejected scan
  induction files with
  | nil => rfl
  | cons file rest ih =>
    cases kept : (predicate file.cells).getD false with
    | false =>
      simp [ParquetScan.assemble, scanFileSkippingRejected, kept, ih]
    | true =>
      have same := scanFileSkippingRejected_eq_scanFile opener projection predicate file (by simp [kept])
      simp [ParquetScan.assemble, kept, same, ih]

theorem scanSkippingRejected_eq_scan_of_reached_eof (files : List (File schema Value))
    (safe : ReachedRejectedFilesReachEOF opener projection predicate files) :
    scanSkippingRejected opener projection predicate files = scan opener projection predicate files := by
  induction files with
  | nil => rfl
  | cons file rest ih =>
    have current := scanFileSkippingRejected_eq_scanFile opener projection predicate file
      (safe [] file rest rfl rfl)
    by_cases eof : (scanFile opener projection predicate file).termination = .eos
    · have tailSafe : ReachedRejectedFilesReachEOF opener projection predicate rest := by
        intro before next after split reached reject
        refine safe (file :: before) next after (congrArg (file :: ·) split) ?_ reject
        simpa only [scan, ParquetScan.assemble, eof] using reached
      have tail := ih tailSafe
      simp only [scan, scanSkippingRejected] at tail
      simp only [scan, scanSkippingRejected, ParquetScan.assemble, current, eof, tail]
    · have skippedStop : (scanFileSkippingRejected opener projection predicate file).termination ≠ .eos := by
        rwa [current]
      rw [scanSkippingRejected, scan, ParquetScan.assemble_stops _ _ _ skippedStop,
        ParquetScan.assemble_stops _ _ _ eof, current]

theorem scanSkippingRejected_not_equivalent_singleton (file : File schema Value)
    (reject : (predicate file.cells).getD false = false)
    (stop : (scanFile opener projection predicate file).termination ≠ .eos) :
    ¬ Events.EventStream.Equivalent
        (.ok ⟨projection.schema, scanSkippingRejected opener projection predicate [file]⟩)
        (.ok ⟨projection.schema, scan opener projection predicate [file]⟩) := by
  have strict : scan opener projection predicate [file] = scanFile opener projection predicate file := by
    cases outcome : (scanFile opener projection predicate file).termination <;>
      simp [scan, ParquetScan.assemble, outcome] at stop ⊢
  intro equivalent
  unfold Events.EventStream.Equivalent at equivalent
  simp only [scanSkippingRejected, ParquetScan.assemble, scanFileSkippingRejected,
    reject, Bool.false_eq_true, ite_false, List.nil_append, strict,
    Events.EventStream.collect, Except.map, Events.Trace.collect, Except.ok.injEq,
    Events.Observation.mk.injEq] at equivalent
  exact stop equivalent.2.symm

end Silmaril.Proofs.Formats.Hive.Manifest.Pruning
