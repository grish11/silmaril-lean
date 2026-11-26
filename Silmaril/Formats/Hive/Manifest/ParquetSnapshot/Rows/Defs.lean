module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Defs

/-! Ordered row denotation from the checked file sources of a Hive manifest. -/

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema extendRow)

variable {Kind Failure : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

private def denoteSnapshotFileRows (limits : Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Snapshot.Bind physical Value Failure)
    (file : File schema Value) :
    Scan.Table (schema.extend physical) Value × Events.Termination (FileError (Snapshot.Error Failure)) :=
  let path := file.path.declared
  match lookup path with
  | .error reason => ([], .readError (.open path (.input reason)))
  | .ok bytes =>
    match Snapshot.openSource limits bind bytes with
    | .error reason => ([], .readError (.open path reason))
    | .ok source =>
      let observed := Reader.denoteGroups source.readGroup source.groups
      let rows := observed.1.flatten.map fun row => extendRow row file.cells
      let termination := match observed.2 with
        | .eos => .eos
        | .closed => .closed
        | .readError reason => .readError (.source path reason)
        | .closeError reason => .closeError (.source path reason)
      (rows, termination)

/-- Look up each literal declaration and bind its bytes as a checked source.
Keep ordered rows from completed groups, with typed partition constants.
Advance to the next occurrence only on EOS. -/
def denoteSnapshotRows (limits : Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Snapshot.Bind physical Value Failure) :
    List (File schema Value) →
      Scan.Table (schema.extend physical) Value × Events.Termination (FileError (Snapshot.Error Failure))
  | [] => ([], .eos)
  | file :: rest =>
    let current := denoteSnapshotFileRows limits lookup bind file
    match current.2 with
    | .eos =>
      let tail := denoteSnapshotRows limits lookup bind rest
      (current.1 ++ tail.1, tail.2)
    | _ => current

end Silmaril.Formats.Hive.Manifest
