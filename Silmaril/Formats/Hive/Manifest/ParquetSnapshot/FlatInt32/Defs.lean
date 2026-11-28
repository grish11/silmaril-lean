module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Defs
public import Silmaril.Formats.Parquet.Snapshot.FlatInt32.Defs

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational
open Silmaril.Formats.Parquet.Snapshot

variable {physical : Scan.Schema String Unit}

/-- Use the supported flat INT32 profile with the original declaration as the
byte lookup key. Lookup failures and indexed group failures remain distinct. -/
def flatInt32SnapshotOpener {InputFailure : Type} (limits : FlatInt32.Limits)
    (lookup : String → Except InputFailure Bytes) :
    Opener Nat physical FlatInt32.Cell (Parquet.Snapshot.Error (FlatInt32.Error InputFailure)) :=
  snapshotOpener limits.snapshot (fun path => (lookup path).mapError FlatInt32.Error.lookup)
    (FlatInt32.bind limits physical)

end Silmaril.Formats.Hive.Manifest
