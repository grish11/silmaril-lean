module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.WritePlan.Defs
public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Rows.Defs
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Rows.Thms
import Silmaril.Formats.Hive.WritePlan.Thms
import Silmaril.Semantics.Relational.Scan.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema partitionCells)

variable {Kind : Type*} {Value : Kind → Type*} {ReadFailure EncodeFailure : Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

theorem planSnapshots_eq_reference (limits : Snapshot.Limits)
    (lookup : String → Except ReadFailure Bytes) (bind : Snapshot.Bind physical Value ReadFailure)
    (keep : Scan.Predicate schema.toScan Value) (files : List (File schema Value))
    (options : PartitionPath.Options) (encode : WritePlan.Encode Value EncodeFailure) :
    planSnapshots limits lookup bind keep files options encode =
      let observed := denoteSnapshotRows limits lookup bind files
      let selected := Scan.select (fun row => keep (partitionCells row)) observed.1
      match observed.2 with
      | .eos => (WritePlan.reference physical schema options encode selected).mapError .planning
      | stopped => .error (.scan stopped selected) := by
  have observed := scanSnapshots_collect_eq_rows limits lookup bind
    (Scan.Projection.id (schema.extend physical)) keep files
  simp only [Events.Trace.collect, Scan.Projection.scan, Scan.Projection.project_id,
    Events.Observation.mk.injEq] at observed
  have rows : (scan (snapshotOpener limits lookup bind) (Scan.Projection.id (schema.extend physical))
      keep files).rows = Scan.select (fun row => keep (partitionCells row))
        (denoteSnapshotRows limits lookup bind files).1 := by
    injection observed.1
  simp only [planSnapshots, rows, observed.2, WritePlan.plan_eq_reference]
  cases (denoteSnapshotRows limits lookup bind files).2 <;> rfl

end Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot
