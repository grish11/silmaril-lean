module

public import Silmaril.Formats.Hive.Manifest.Pruning.Defs

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

theorem scanSkippingRejected_eq_scan (files : List (File schema Value))
    (safe : RejectedFilesReachEOF opener projection predicate files) :
    scanSkippingRejected opener projection predicate files = scan opener projection predicate files := by
  induction files with
  | nil => rfl
  | cons file rest ih =>
    have current := scanFileSkippingRejected_eq_scanFile opener projection predicate file
      (safe file (by simp))
    have tail := ih (fun entry member => safe entry (by simp [member]))
    simp only [scan, scanSkippingRejected] at tail
    simp only [scan, scanSkippingRejected, ParquetScan.assemble, current, tail]

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
