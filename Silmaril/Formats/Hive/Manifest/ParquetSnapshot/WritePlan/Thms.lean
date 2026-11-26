module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.WritePlan.Defs
public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Rows.Defs
import Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.WritePlan

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema partitionCells)

variable {Kind : Type*} {Value : Kind → Type*} {ReadFailure EncodeFailure : Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

/-- After EOS, the result agrees with independent first-seen directory
grouping and stable filtering of the selected rows into payloads. Before
EOS, it carries the original terminal outcome and ordered selected prefix. -/
theorem planSnapshots_eq_reference (limits : Snapshot.Limits)
    (lookup : String → Except ReadFailure Bytes) (bind : Snapshot.Bind physical Value ReadFailure)
    (keep : Scan.Predicate schema.toScan Value) (files : List (File schema Value))
    (options : PartitionPath.Options) (encode : WritePlan.Encode Value EncodeFailure) :
    planSnapshots limits lookup bind keep files options encode =
      let observed := denoteSnapshotRows limits lookup bind files
      let selected := Scan.select (fun row => keep (partitionCells row)) observed.1
      match observed.2 with
      | .eos => (WritePlan.reference physical schema options encode selected).mapError .planning
      | stopped => .error (.scan stopped selected) :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.planSnapshots_eq_reference limits lookup bind keep files options encode

end Silmaril.Formats.Hive.Manifest
