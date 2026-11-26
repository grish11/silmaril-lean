module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Defs
public import Silmaril.Formats.Hive.WritePlan.Defs

/-!
# Write planning from a checked Hive snapshot scan

Scan the manifest in literal occurrence order with the full augmented
schema. Plan only after observed EOS. Keep the exact source termination
and selected row prefix for scans that stop before EOS.
-/

@[expose] public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)

variable {Kind : Type*} {Value : Kind → Type*} {ReadFailure EncodeFailure : Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

inductive SnapshotPlanError (selected : Scan.Schema String Kind) (Value : Kind → Type*)
    (ReadFailure EncodeFailure : Type*) where
  | scan (termination : Events.Termination (FileError (Snapshot.Error ReadFailure)))
      (rows : Scan.Table selected Value)
  | planning (reason : WritePlan.Error EncodeFailure)

/-- Use the strict checked reader, preserving every reached file's outcome.
Only a completed scan can supply rows for planning. The selected prefix of
an interrupted scan is available with its original typed termination. -/
def planSnapshots (limits : Snapshot.Limits) (lookup : String → Except ReadFailure Bytes)
    (bind : Snapshot.Bind physical Value ReadFailure) (keep : Scan.Predicate schema.toScan Value)
    (files : List (File schema Value)) (options : PartitionPath.Options)
    (encode : WritePlan.Encode Value EncodeFailure) :
    Except (SnapshotPlanError (schema.extend physical) Value ReadFailure EncodeFailure)
      (List (WritePlan.Bucket physical Value)) :=
  let trace := scan (snapshotOpener limits lookup bind) (Scan.Projection.id (schema.extend physical)) keep files
  match trace.termination with
  | .eos => (WritePlan.plan physical schema options encode trace.rows).mapError .planning
  | stopped => .error (.scan stopped trace.rows)

end Silmaril.Formats.Hive.Manifest
