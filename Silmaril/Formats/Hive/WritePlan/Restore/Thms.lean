module

public import Silmaril.Formats.Hive.WritePlan.Restore.Defs
import Silmaril.Proofs.Formats.Hive.WritePlan.Restore

public section

namespace Silmaril.Formats.Hive.WritePlan

open Silmaril.Relational
open Silmaril.Formats.Hive.TypedPartitions (Convert PartitionSchema)

variable {Kind : Type*} {Value : Kind → Type*} {EncodeFailure DecodeFailure : Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

/-- Recover the full original rows in first-seen directory order and in
source-relative order within each directory. Both operations use the same
path options. Successful planning supplies directory representability,
and the left inverse recovers each successfully encoded present cell. -/
theorem restore_plan_eq_groupedRows (options : PartitionPath.Options)
    (encode : Encode Value EncodeFailure) (decode : Convert Value DecodeFailure)
    (inverse : CellLeftInverse schema encode decode)
    (rows : Scan.Table (schema.extend physical) Value) (buckets : List (Bucket physical Value))
    (planned : plan physical schema options encode rows = .ok buckets) :
    restore physical schema options decode buckets = .ok (groupOriginalRows options encode rows) :=
  Proofs.Formats.Hive.WritePlan.restore_plan_eq_groupedRows options encode decode inverse rows buckets planned

end Silmaril.Formats.Hive.WritePlan
