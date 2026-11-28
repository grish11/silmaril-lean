module

public import Silmaril.Formats.Parquet.NestedPoint.Multi.Defs
import Silmaril.Proofs.Formats.Parquet.NestedPoint.Multi.Correctness

public section

namespace Silmaril.Formats.Parquet.NestedPoint.Multi

theorem decodeFrame_wire {kind : Kind} {limits : NestedPresence.Limits} {source : Bytes}
    {frame : Page.Frame} {result : Decoded kind.Value}
    (h : decodeFrame kind limits source frame = .ok result) : FrameWire kind limits source frame result :=
  Proofs.Formats.Parquet.NestedPoint.Multi.decodeFrame_wire h

/-- The ordered slots and levels are the concatenation of the individually
decoded pages from this column, with the original group count. -/
theorem readColumn_wire {kind : Kind} {limits : Limits} {snapshot : Snapshot.Checked}
    {group : Nat} {result : Decoded kind.Value} (h : readColumn kind limits snapshot group = .ok result) :
    ColumnWire kind limits snapshot group result :=
  Proofs.Formats.Parquet.NestedPoint.Multi.readColumn_wire h

theorem read_parentMismatch {limits : Limits} {snapshot : Snapshot.Checked} {group : Nat}
    {lhs : Decoded Int32} {rhs : Decoded Int64}
    (left : readColumn .signed limits snapshot group = .ok lhs)
    (right : readColumn .wide limits snapshot group = .ok rhs)
    (different : parentMask lhs.states ≠ parentMask rhs.states) :
    read limits snapshot group = .error .parentPresence :=
  Proofs.Formats.Parquet.NestedPoint.Multi.read_parentMismatch left right different

/-- Sibling values pair by row after both independent original frame walks.
The masks agree and the paired row count equals the checked group count. -/
theorem read_wire {limits : Limits} {snapshot : Snapshot.Checked} {group : Nat} {rows : List Row}
    (h : read limits snapshot group = .ok rows) : Wire limits snapshot group rows :=
  Proofs.Formats.Parquet.NestedPoint.Multi.read_wire h

end Silmaril.Formats.Parquet.NestedPoint.Multi
