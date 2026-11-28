module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.FlatInt32.Defs

/-!
# Opt-in flat Int32 name alignment for a Hive manifest

The existing snapshot and PLAIN Int32 reader check the file and decode its
physical fields in wire order. The adapter resolves an explicit target in
exact, case-sensitive names once at open. A permitted absent field becomes
null. Present fields keep their physical required/optional semantics.
-/

@[expose] public section

namespace Silmaril.Formats.Hive.Manifest.AlignedInt32

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema extendRow)

abbrev Cell := Snapshot.FlatInt32.Cell

/-- Whether a target field may be absent from a file. Present nulls are still
governed by the file's physical layout. -/
abbrev AllowMissing (target : Scan.Schema String Unit) := Fin target.width → Bool

inductive Error (Failure : Type) where
  | lookup (reason : Failure)
  | physical (reason : Snapshot.FlatInt32.Error Failure)
  | duplicateTarget
  | reservedPartition (name : String)
  | unexpectedField (name : String)
  | missingRequired (name : String)
  deriving DecidableEq, Repr

def wireSchema (names : List String) : Scan.Schema String Unit :=
  ⟨names.length, fun i => (names.get i, ())⟩

def wireSlot (names : List String) (name : String) : Option (Fin names.length) :=
  (List.finRange names.length).find? fun i => names.get i == name

structure WireBinding (Failure : Type) where
  names : List String
  decode : Snapshot.DecodeGroup (wireSchema names) Cell (Error Failure)

/-- Check the flat wire schema before applying name policy. Reject duplicate
target names, target then wire collisions with partition names, extra wire
fields, and missing required target fields, in that order. Name searches
within a stage follow the corresponding schema order. -/
def bindWire {Failure : Type} (limits : Snapshot.FlatInt32.Limits)
    (target : Scan.Schema String Unit) (allowMissing : AllowMissing target)
    (partitions : PartitionSchema Unit) (metadata : Footer.Metadata) :
    Except (Error Failure) (WireBinding Failure) := do
  let fields ← (FlatScan.flatSchema limits.groups metadata.schema).mapError
    (fun reason => Error.physical (.profile reason))
  let names := fields.map (·.name)
  let wanted := List.ofFn fun i => (target.kind i).1
  if !wanted.Nodup then throw .duplicateTarget
  if let some collision := (wanted ++ names).find? partitions.keys.contains then
    throw (.reservedPartition collision)
  if let some extra := names.find? (fun name => !wanted.contains name) then
    throw (.unexpectedField extra)
  if let some missing := (List.finRange target.width).find?
      (fun i => !allowMissing i && !names.contains (target.kind i).1) then
    throw (.missingRequired (target.kind missing).1)
  let decode ← (Snapshot.FlatInt32.bind limits (wireSchema names) metadata).mapError Error.physical
  return ⟨names, fun snapshot index group => (decode snapshot index group).mapError Error.physical⟩

/-- Precompute the target-to-wire positions once per opened file. -/
def alignDecode {Failure : Type} (target : Scan.Schema String Unit) (wire : WireBinding Failure) :
    Snapshot.DecodeGroup target Cell (Error Failure) :=
  let slots := Vector.ofFn (fun i : Fin target.width => wireSlot wire.names (target.kind i).1)
  fun snapshot index group => (wire.decode snapshot index group).map
    (List.map fun row i => (slots.get i).bind (fun slot => row slot))

/-- The same checked snapshot, with aligned rows at the target schema. -/
def bind {Failure : Type} (limits : Snapshot.FlatInt32.Limits)
    (target : Scan.Schema String Unit) (allowMissing : AllowMissing target)
    (partitions : PartitionSchema Unit) : Snapshot.Bind target Cell (Error Failure) :=
  fun metadata => (bindWire limits target allowMissing partitions metadata).map (alignDecode target)

def referenceRow (target : Scan.Schema String Unit) (names : List String)
    (row : Scan.Row (wireSchema names) Cell) : Scan.Row target Cell :=
  fun i =>
    match ((List.finRange names.length).filter fun slot => names.get slot == (target.kind i).1).head? with
    | none => none
    | some slot => row slot

variable {Failure : Type} {target : Scan.Schema String Unit} {partitions : PartitionSchema Unit}

abbrev Outcome (partitions : PartitionSchema Unit) (target : Scan.Schema String Unit) (Failure : Type) :=
  Scan.Table (partitions.extend target) Cell ×
    Events.Termination (FileError (Snapshot.Error (Error Failure)))

/-- Independent single-file observation from wire-order group reads and name
lookup on each row. Retain rows of every completed group before a failure. -/
def denoteFileRows (limits : Snapshot.FlatInt32.Limits)
    (lookup : String → Except Failure Bytes) (allowMissing : AllowMissing target)
    (file : File partitions Cell) : Outcome partitions target Failure :=
  let path := file.path.declared
  match lookup path with
  | .error reason => ([], .readError (.open path (.input (.lookup reason))))
  | .ok bytes =>
    match Snapshot.check (Failure := Error Failure) limits.snapshot bytes with
    | .error reason => ([], .readError (.open path reason))
    | .ok snapshot =>
      match bindWire limits target allowMissing partitions snapshot.metadata with
      | .error reason => ([], .readError (.open path (.schema reason)))
      | .ok wire =>
        let source := snapshot.source wire.decode
        let observed := Reader.denoteGroups source.readGroup source.groups
        let rows := observed.1.flatten.map fun row =>
          extendRow (referenceRow target wire.names row) file.cells
        let termination := match observed.2 with
          | .eos => .eos
          | .closed => .closed
          | .readError reason => .readError (.source path reason)
          | .closeError reason => .closeError (.source path reason)
        (rows, termination)

/-- Reference fold over literal occurrences. Advance only when the reached
file exhausts its wire groups, retaining the full prefix at the first error. -/
def denoteRows (limits : Snapshot.FlatInt32.Limits)
    (lookup : String → Except Failure Bytes) (allowMissing : AllowMissing target) :
    List (File partitions Cell) → Outcome partitions target Failure
  | [] => ([], .eos)
  | file :: rest =>
    let current := denoteFileRows limits lookup allowMissing file
    match current.2 with
    | .eos =>
      let tail := denoteRows limits lookup allowMissing rest
      (current.1 ++ tail.1, tail.2)
    | _ => current

end Silmaril.Formats.Hive.Manifest.AlignedInt32

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)

/-- Opt in to an explicit aligned data schema. Use with the ordinary manifest
scan or its existing pruning policy. The strict opener remains available. -/
def alignedInt32SnapshotOpener {Failure : Type} {target : Scan.Schema String Unit}
    (limits : Snapshot.FlatInt32.Limits) (partitions : PartitionSchema Unit)
    (allowMissing : AlignedInt32.AllowMissing target) (lookup : String → Except Failure Bytes) :
    Opener Nat target AlignedInt32.Cell (Snapshot.Error (AlignedInt32.Error Failure)) :=
  snapshotOpener limits.snapshot (fun path => (lookup path).mapError AlignedInt32.Error.lookup)
    (AlignedInt32.bind limits target allowMissing partitions)

end Silmaril.Formats.Hive.Manifest
