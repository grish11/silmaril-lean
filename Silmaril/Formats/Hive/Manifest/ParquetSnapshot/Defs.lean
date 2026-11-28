module

public import Silmaril.Formats.Hive.Manifest.Defs
public import Silmaril.Formats.Parquet.Snapshot.Defs

@[expose] public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational

/-- Look up the original declared path and bind its immutable bytes. One
extra pull after the group count lets the strict manifest observe EOF. -/
def snapshotOpener {Kind Failure : Type*} {Value : Kind → Type*}
    {physical : Scan.Schema String Kind} (limits : Parquet.Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Parquet.Snapshot.Bind physical Value Failure) :
    Opener Nat physical Value (Parquet.Snapshot.Error Failure) := fun path =>
  match lookup path with
  | .error reason => .error (.input reason)
  | .ok bytes => (Parquet.Snapshot.openSource limits bind bytes).map fun source =>
    ⟨source, source.groups.length + 1⟩

end Silmaril.Formats.Hive.Manifest
