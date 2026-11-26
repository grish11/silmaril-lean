module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Defs

/-! One logical action budget for a strict scan of immutable Hive snapshots. -/

@[expose] public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema extendRow)

variable {Kind Failure : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

/-- In literal manifest order, spend one action on each checked open (including
lookup), one on each row-group pull, and one on each file EOS pull. Empty
manifests give EOS. At zero budget a pending file or unread cursor gives
`.closed`, including a cursor whose last group was already emitted. Snapshot
cleanup is free. Filtering changes output batches but still spends actions
and observes failures. The budget counts logical actions. -/
def scanSnapshotsBounded (limits : Snapshot.Limits) (lookup : String → Except Failure Bytes)
    (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (keep : Scan.Predicate schema.toScan Value) :
    Nat → List (File schema Value) → Events.Trace projection.schema Value (FileError (Snapshot.Error Failure))
  | _, [] => ⟨[], .eos⟩
  | 0, _ :: _ => ⟨[], .closed⟩
  | pulls + 1, file :: rest =>
    match snapshotOpener limits lookup bind file.path.declared with
    | .error reason => ⟨[], .readError (.open file.path.declared reason)⟩
    | .ok opened =>
      let current := scanFile (fun _ => .ok { opened with fuel := pulls }) projection keep file
      match current.termination with
      | .eos =>
        -- The original fuel is the group count plus the file EOS pull.
        let tail := scanSnapshotsBounded limits lookup bind projection keep (pulls - opened.fuel) rest
        ⟨current.batches ++ tail.batches, tail.termination⟩
      | _ => current

/-- Independently open each affordable occurrence and denote its affordable
group prefix. Build one batch per successful retained group by projecting its
typed rows. Advance only after the prefix succeeds and the EOS pull fits. -/
def scanSnapshotsBoundedReference (limits : Snapshot.Limits) (lookup : String → Except Failure Bytes)
    (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (keep : Scan.Predicate schema.toScan Value) :
    Nat → List (File schema Value) → Events.Trace projection.schema Value (FileError (Snapshot.Error Failure))
  | _, [] => ⟨[], .eos⟩
  | 0, _ :: _ => ⟨[], .closed⟩
  | pulls + 1, file :: rest =>
    let path := file.path.declared
    match lookup path with
    | .error reason => ⟨[], .readError (.open path (.input reason))⟩
    | .ok bytes =>
      match Snapshot.openSource limits bind bytes with
      | .error reason => ⟨[], .readError (.open path reason)⟩
      | .ok source =>
        let groups := Reader.denoteGroups source.readGroup (source.groups.take pulls)
        let batches := if (keep file.cells).getD false then
          groups.1.map fun rows => AlignedColumns.ofRows (projection.project (rows.map fun row => extendRow row file.cells))
        else []
        match groups.2 with
        | .eos =>
          if pulls ≤ source.groups.length then ⟨batches, .closed⟩
          else
            let tail := scanSnapshotsBoundedReference limits lookup bind projection keep
              (pulls - (source.groups.length + 1)) rest
            ⟨batches ++ tail.batches, tail.termination⟩
        | .closed => ⟨batches, .closed⟩
        | .readError reason => ⟨batches, .readError (.source path reason)⟩
        | .closeError reason => ⟨batches, .closeError (.source path reason)⟩

end Silmaril.Formats.Hive.Manifest
