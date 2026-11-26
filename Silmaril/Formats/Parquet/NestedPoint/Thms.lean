module

public import Silmaril.Formats.Parquet.NestedPoint.Defs
import Silmaril.Proofs.Formats.Parquet.NestedPoint.Correctness

public section

namespace Silmaril.Formats.Parquet.NestedPoint

theorem readLeaf_wire {limits : Limits} {snapshot : Snapshot.Checked} {group column : Nat}
    {child : NestedPresence.Child} {physical : Footer.PhysicalType} {result : NestedPresence.Result}
    (h : readLeaf limits snapshot group column child physical = .ok result) :
    LeafWire limits snapshot group column child physical result :=
  Proofs.Formats.Parquet.NestedPoint.readLeaf_wire h

theorem assemble_parentMismatch {left right : NestedPresence.Result}
    (h : valueMask left ≠ parentMask right) : assemble left right = .error .parentPresence :=
  Proofs.Formats.Parquet.NestedPoint.assemble_parentMismatch h

theorem assemble_wire {left right : NestedPresence.Result} {rows : List Row}
    (h : assemble left right = .ok rows) : AssemblyWire left right rows :=
  Proofs.Formats.Parquet.NestedPoint.assemble_wire h

/-- Both decoded leaf pages come from the original checked group. The
paired result preserves parent validity and ordered nullable child values. -/
theorem read_wire {limits : Limits} {snapshot : Snapshot.Checked} {group : Nat} {rows : List Row}
    (h : read limits snapshot group = .ok rows) :
    ∃ left right, LeafWire limits snapshot group 0 .required .int32 left ∧
      LeafWire limits snapshot group 1 .optional .int64 right ∧ AssemblyWire left right rows :=
  Proofs.Formats.Parquet.NestedPoint.read_wire h

end Silmaril.Formats.Parquet.NestedPoint
