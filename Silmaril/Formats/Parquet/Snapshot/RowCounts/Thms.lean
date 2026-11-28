module

public import Silmaril.Formats.Parquet.Snapshot.Defs
import Silmaril.Proofs.Formats.Parquet.Snapshot.RowCounts

public section

namespace Silmaril.Formats.Parquet.Snapshot

/-- The file count accounts for every dense footer ordinal exactly once. -/
theorem check_rowCounts {Failure : Type*} {limits : Limits} {source : Bytes}
    {snapshot : Checked} (checked : check (Failure := Failure) limits source = .ok snapshot) :
    snapshot.metadata.numRows.toNat = ((List.range snapshot.groupCount).map fun index =>
      ((snapshot.groupAt index).map (·.numRows.toNat)).getD 0).sum :=
  Proofs.Formats.Parquet.Snapshot.check_rowCounts checked

end Silmaril.Formats.Parquet.Snapshot
