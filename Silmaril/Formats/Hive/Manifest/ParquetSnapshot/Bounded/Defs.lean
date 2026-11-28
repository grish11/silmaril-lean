module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Defs

/-! One logical action budget for a strict scan of immutable Hive snapshots. -/

@[expose] public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema extendRow)

variable {Kind Failure : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

/-- A fully consumed source has one pull per group and one for EOS.
Closing an immutable source succeeds without consuming an action. -/
def Opener.FullConsumption {Group Error : Type*} (opener : Opener Group physical Value Error) : Prop :=
  ∀ ⦃path opened⦄, opener path = .ok opened →
    opened.fuel = opened.source.groups.length + 1 ∧
    ∀ remaining, opened.source.close remaining = .ok ()

/-- In literal manifest order, spend one action on each checked open (including
lookup), one on each row-group pull, and one on each file EOS pull. Empty
manifests give EOS. A pending open at zero budget gives `.closed`. If the
budget ends with an open cursor, observe its close outcome even after
emitting its last group. Cleanup consumes no action. Filtering changes
output batches while preserving charges and reached failures. Charge a
completed file by its source group count plus its EOS pull. -/
def scanBounded {Group Error : Type*} (opener : Opener Group physical Value Error)
    (projection : Scan.Projection (schema.extend physical)) (keep : Scan.Predicate schema.toScan Value) :
    Nat → List (File schema Value) → Events.Trace projection.schema Value (FileError Error)
  | _, [] => ⟨[], .eos⟩
  | 0, _ :: _ => ⟨[], .closed⟩
  | pulls + 1, file :: rest =>
    match opener file.path.declared with
    | .error reason => ⟨[], .readError (.open file.path.declared reason)⟩
    | .ok opened =>
      let current := scanFile (fun _ => .ok { opened with fuel := pulls }) projection keep file
      match current.termination with
      | .eos =>
        let tail := scanBounded opener projection keep (pulls - (opened.source.groups.length + 1)) rest
        ⟨current.batches ++ tail.batches, tail.termination⟩
      | _ => current

/-- Strict budgeted traversal over checked byte snapshots. -/
def scanSnapshotsBounded (limits : Snapshot.Limits) (lookup : String → Except Failure Bytes)
    (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (keep : Scan.Predicate schema.toScan Value) :
    Nat → List (File schema Value) → Events.Trace projection.schema Value (FileError (Snapshot.Error Failure)) :=
  scanBounded (snapshotOpener limits lookup bind) projection keep

/-- Logical action witness for an ordered scan of fully consumed sources. A
failure ends the witness at the failed action, and each completed occurrence
charges its open, all group pulls, and a separate EOS pull. -/
inductive ScanCost {Group Error : Type*} (opener : Opener Group physical Value Error) :
    List (File schema Value) → Nat → Prop where
  | nil : ScanCost opener [] 0
  | openError {file rest reason} (failed : opener file.path.declared = .error reason) :
      ScanCost opener (file :: rest) 1
  | complete {file rest source rows actions}
      (opened : opener file.path.declared = .ok ⟨source, source.groups.length + 1⟩)
      (decoded : source.groups.mapM source.readGroup = .ok rows)
      (tail : ScanCost opener rest actions) :
      ScanCost opener (file :: rest) (source.groups.length + 2 + actions)
  | readError {file rest source before group after rows reason}
      (opened : opener file.path.declared = .ok ⟨source, source.groups.length + 1⟩)
      (split : source.groups = before ++ group :: after)
      (decoded : before.mapM source.readGroup = .ok rows)
      (failed : source.readGroup group = .error reason) :
      ScanCost opener (file :: rest) (before.length + 2)

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

/-- Logical actions taken by a strict scan through manifest EOS or the first
failed action. Each literal occurrence is charged independently of filtering.
Completing a file costs its checked open, all group pulls, and a separate EOS
pull. A failed open or read ends the witness at that action. -/
inductive SnapshotScanCost (limits : Snapshot.Limits) (lookup : String → Except Failure Bytes)
    (bind : Snapshot.Bind physical Value Failure) : List (File schema Value) → Nat → Prop where
  | nil : SnapshotScanCost limits lookup bind [] 0
  | openError {file rest reason}
      (failed : snapshotOpener limits lookup bind file.path.declared = .error reason) :
      SnapshotScanCost limits lookup bind (file :: rest) 1
  | complete {file rest bytes source rows actions}
      (found : lookup file.path.declared = .ok bytes)
      (opened : Snapshot.openSource limits bind bytes = .ok source)
      (decoded : source.groups.mapM source.readGroup = .ok rows)
      (tail : SnapshotScanCost limits lookup bind rest actions) :
      SnapshotScanCost limits lookup bind (file :: rest) (source.groups.length + 2 + actions)
  | readError {file rest bytes source before group after rows reason}
      (found : lookup file.path.declared = .ok bytes)
      (opened : Snapshot.openSource limits bind bytes = .ok source)
      (split : source.groups = before ++ group :: after)
      (decoded : before.mapM source.readGroup = .ok rows)
      (failed : source.readGroup group = .error reason) :
      SnapshotScanCost limits lookup bind (file :: rest) (before.length + 2)

end Silmaril.Formats.Hive.Manifest
