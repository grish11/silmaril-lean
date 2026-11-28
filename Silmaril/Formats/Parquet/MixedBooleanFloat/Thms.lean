module

public import Silmaril.Formats.Parquet.MixedBooleanFloat.Defs
import Silmaril.Proofs.Formats.Parquet.MixedBooleanFloat.Wire

/-! Original snapshot, complete row groups, and positional assembly. -/

public section

namespace Silmaril.Formats.Parquet.MixedBooleanFloat

theorem openFile_snapshot {limits : Limits} {source : Bytes} {booleanName floatName : String}
    {checked : Checked booleanName floatName} (opened : openFile limits source booleanName floatName = .ok checked) :
    Snapshot.check (Failure := Failure) limits.snapshot source = .ok checked.snapshot :=
  Proofs.Formats.Parquet.MixedBooleanFloat.openFile_snapshot opened

/-- Independent page segmentation disappears after flattening each ordered
column. The assembled group has the advertised count and exact indexed slots. -/
theorem readGroup_wire {booleanName floatName : String} {checked : Checked booleanName floatName}
    {limits : FlatColumn.Limits} {index : Nat}
    {rows : Reader.RowGroup (schema booleanName floatName) Value}
    (read : checked.readGroup limits index = .ok rows) : checked.GroupWire limits index rows :=
  Proofs.Formats.Parquet.MixedBooleanFloat.readGroup_wire read

end Silmaril.Formats.Parquet.MixedBooleanFloat
