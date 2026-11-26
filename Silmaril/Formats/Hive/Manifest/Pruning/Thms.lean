module

public import Silmaril.Formats.Hive.Manifest.Pruning.Defs
import Silmaril.Proofs.Formats.Hive.Manifest.Pruning.Correctness

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)

variable {Kind Group Error : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}
variable (opener : Opener Group physical Value Error)
variable (projection : Scan.Projection (schema.extend physical))
variable (predicate : Scan.Predicate schema.toScan Value)

theorem RejectedFilesReachEOF.reached {files : List (File schema Value)}
    (safe : RejectedFilesReachEOF opener projection predicate files) :
    ReachedRejectedFilesReachEOF opener projection predicate files := by
  intro before file after split _ reject
  exact safe file (by simp [split]) reject

/-- Rejected declarations in the strict scan's reached prefix must reach EOF.
Both policies then yield the same batches and exact terminal outcome. -/
theorem scanSkippingRejected_eq_scan_of_reached_eof (files : List (File schema Value))
    (safe : ReachedRejectedFilesReachEOF opener projection predicate files) :
    scanSkippingRejected opener projection predicate files = scan opener projection predicate files :=
  Proofs.Formats.Hive.Manifest.Pruning.scanSkippingRejected_eq_scan_of_reached_eof opener projection
    predicate files safe

/-- If every rejected occurrence would reach EOF, skipping it leaves the
reference trace unchanged, including batches and terminal outcome. -/
theorem scanSkippingRejected_eq_scan (files : List (File schema Value))
    (safe : RejectedFilesReachEOF opener projection predicate files) :
    scanSkippingRejected opener projection predicate files = scan opener projection predicate files :=
  scanSkippingRejected_eq_scan_of_reached_eof opener projection predicate files
    (RejectedFilesReachEOF.reached opener projection predicate safe)

/-- In particular, the two policies have the same ordered typed rows and
terminal outcome under the rejected-file EOF hypothesis. -/
theorem scanSkippingRejected_equivalent (files : List (File schema Value))
    (safe : RejectedFilesReachEOF opener projection predicate files) :
    Events.EventStream.Equivalent
      (.ok ⟨projection.schema, scanSkippingRejected opener projection predicate files⟩)
      (.ok ⟨projection.schema, scan opener projection predicate files⟩) := by
  rw [scanSkippingRejected_eq_scan opener projection predicate files safe]
  rfl

/-- A rejected singleton with a non-EOF reference outcome distinguishes the
two policies even when the file opened successfully. -/
theorem scanSkippingRejected_not_equivalent_singleton (file : File schema Value)
    (reject : (predicate file.cells).getD false = false)
    (stop : (scanFile opener projection predicate file).termination ≠ .eos) :
    ¬ Events.EventStream.Equivalent
        (.ok ⟨projection.schema, scanSkippingRejected opener projection predicate [file]⟩)
        (.ok ⟨projection.schema, scan opener projection predicate [file]⟩) :=
  Proofs.Formats.Hive.Manifest.Pruning.scanSkippingRejected_not_equivalent_singleton opener projection
    predicate file reject stop

end Silmaril.Formats.Hive.Manifest
