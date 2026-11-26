module

public import Silmaril.Formats.Parquet.Footer.NestedLeaf.Defs
import Silmaril.Proofs.Formats.Parquet.Footer.NestedLeaf.Correctness

public section

namespace Silmaril.Formats.Parquet.Footer.NestedLeaf

theorem checkShape_ok_iff {schema : List SchemaElement} {shape : Shape} :
    checkShape schema = .ok shape ↔
      schema = [shape.root, shape.parent, shape.first, shape.second] ∧ shape.admitted :=
  Proofs.Formats.Parquet.Footer.NestedLeaf.checkShape_ok_iff

theorem readItems_wire {limits : Limits} {snapshot : Snapshot.Checked}
    {container : ThriftCompact.Traversal.Field} {items : List ColumnOrder.Item}
    (h : readItems limits snapshot = .ok (container, items)) :
    ItemsWire limits snapshot container items :=
  Proofs.Formats.Parquet.Footer.NestedLeaf.readItems_wire h

/-- The physical and schema ordinals are bound to the selected checked
leaf and the original wire items for the leaf and its parent. -/
theorem select_wire {limits : Limits} {snapshot : Snapshot.Checked}
    {column : Nat} {selection : Selection snapshot}
    (h : select limits snapshot column = .ok selection) : Wire limits column selection :=
  Proofs.Formats.Parquet.Footer.NestedLeaf.select_wire h

theorem selectChunk_wire {snapshot : Snapshot.Checked} {selection : Selection snapshot}
    {ordinal : Nat} {group : RowGroup} {chunk : ColumnChunk}
    (h : selectChunk selection ordinal = .ok (group, chunk)) :
    snapshot.groupAt ordinal = some group ∧ group.columns[selection.columnOrdinal]? = some chunk ∧
      chunk.metadata.pathInSchema = selection.path ∧ chunk.metadata.physicalType = selection.physical :=
  Proofs.Formats.Parquet.Footer.NestedLeaf.selectChunk_wire h

end Silmaril.Formats.Parquet.Footer.NestedLeaf
