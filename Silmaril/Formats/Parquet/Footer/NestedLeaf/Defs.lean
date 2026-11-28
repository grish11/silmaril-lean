module

public import Silmaril.Formats.Parquet.Footer.ColumnOrder.Defs

/-! Footer-only selection in a root containing one optional two-leaf group. -/

public section

namespace Silmaril.Formats.Parquet.Footer.NestedLeaf

open ThriftCompact
open Traversal (Field Reader)

inductive Error where
  | unsupportedShape
  | annotatedGroup
  | columnOrdinal (ordinal : Nat)
  | footerByteLimit
  | footerExtent
  | missingSchema
  | traversal (cause : ColumnOrder.Error)
  | schemaExtent
  | groupOrdinal (ordinal : Nat)
  | chunkOrdinal (ordinal : Nat)
  | chunkAssociation
  deriving DecidableEq, Repr

structure Shape where
  root : SchemaElement
  parent : SchemaElement
  first : SchemaElement
  second : SchemaElement

/-- The root has one optional child group, with two direct, nonrepeated
physical leaves. The checked Snapshot supplies the normal schema validation. -/
@[expose] def Shape.admitted (shape : Shape) : Prop :=
  shape.root.numChildren = some 1 ∧
  shape.parent.physicalType = none ∧ shape.parent.numChildren = some 2 ∧
  shape.parent.repetition = some .optional ∧
  (shape.first.repetition = some .required ∨ shape.first.repetition = some .optional) ∧
  (shape.second.repetition = some .required ∨ shape.second.repetition = some .optional) ∧
  shape.first.physicalType.isSome = true ∧ shape.second.physicalType.isSome = true ∧
  shape.first.numChildren.getD 0 = 0 ∧ shape.second.numChildren.getD 0 = 0

instance (shape : Shape) : Decidable shape.admitted := by
  unfold Shape.admitted
  infer_instance

def checkShape (schema : List SchemaElement) : Except Error Shape :=
  match schema with
  | [root, parent, first, second] =>
    let shape : Shape := ⟨root, parent, first, second⟩
    if shape.admitted then .ok shape else .error .unsupportedShape
  | _ => .error .unsupportedShape

/-- Use the same bounded footer reader and exact struct-list traversal as
the flat order accessor. The returned field owns the entire schema list. -/
def readItems (limits : Limits) (snapshot : Snapshot.Checked) :
    Except Error (Field × List ColumnOrder.Item) := do
  if snapshot.footer.stop - snapshot.footer.start > limits.maxFooterBytes then return ← throw .footerByteLimit
  let reader := ColumnOrder.footerReader limits snapshot
  let (fields, stop) ← (Traversal.readStruct reader 0).mapError (.traversal ∘ .compact)
  if stop ≠ reader.source.length then return ← throw .footerExtent
  let some field ← (ColumnOrder.field? fields 2).mapError .traversal | throw .missingSchema
  let schema ← (ColumnOrder.readStructList reader field).mapError .traversal
  pure (field, schema)

structure Selection (snapshot : Snapshot.Checked) where
  private mk ::
  columnOrdinal : Nat
  parent : SchemaElement
  leaf : SchemaElement
  physical : PhysicalType
  container : Field
  parentItem : ColumnOrder.Item
  leafItem : ColumnOrder.Item

@[expose] def Selection.schemaOrdinal {snapshot : Snapshot.Checked} (selection : Selection snapshot) : Nat :=
  selection.columnOrdinal + 2

@[expose] def Selection.path {snapshot : Snapshot.Checked} (selection : Selection snapshot) : List String :=
  [selection.parent.name, selection.leaf.name]

/-- Select physical ordinal 0 or 1. The corresponding original schema
ordinal is 2 or 3. The intermediate group carries no logical annotation. -/
def select (limits : Limits) (snapshot : Snapshot.Checked) (column : Nat) :
    Except Error (Selection snapshot) := do
  if 2 ≤ column then return ← throw (.columnOrdinal column)
  let shape ← checkShape snapshot.metadata.schema
  let leaf := if column = 0 then shape.first else shape.second
  let some physical := leaf.physicalType | throw .unsupportedShape
  let (container, items) ← readItems limits snapshot
  let [_, parentItem, first, second] := items | throw .schemaExtent
  let leafItem := if column = 0 then first else second
  if parentItem.fields.any (fun field => field.id == 6 || field.id == 10) then return ← throw .annotatedGroup
  let reader := ColumnOrder.footerReader limits snapshot
  if ¬ (ColumnOrder.Slot.within reader ⟨container, parentItem⟩ ∧
        ColumnOrder.Slot.within reader ⟨container, leafItem⟩) then return ← throw .schemaExtent
  pure ⟨column, shape.parent, leaf, physical, container, parentItem, leafItem⟩

/-- Resolve metadata only. The checked snapshot and ordinal come from
the selection, and name/type are matched against the exact chunk. -/
def selectChunk {snapshot : Snapshot.Checked} (selection : Selection snapshot) (groupOrdinal : Nat) :
    Except Error (RowGroup × ColumnChunk) := do
  let some group := snapshot.groupAt groupOrdinal | throw (.groupOrdinal groupOrdinal)
  let some chunk := group.columns[selection.columnOrdinal]? | throw (.chunkOrdinal selection.columnOrdinal)
  if ¬ (chunk.metadata.pathInSchema = selection.path ∧
        chunk.metadata.physicalType = selection.physical) then return ← throw .chunkAssociation
  pure (group, chunk)

structure ItemsWire (limits : Limits) (snapshot : Snapshot.Checked) (container : Field)
    (items : List ColumnOrder.Item) : Prop where
  cap : snapshot.footer.stop - snapshot.footer.start ≤ limits.maxFooterBytes
  parsed : ∃ fields,
    let reader := ColumnOrder.footerReader limits snapshot
    Traversal.readStruct reader 0 = .ok (fields, reader.source.length) ∧
    fields.filter (·.id == 2) = [container] ∧ ColumnOrder.StructListWire reader container items

structure Wire {snapshot : Snapshot.Checked} (limits : Limits) (column : Nat)
    (selection : Selection snapshot) : Prop where
  ordinal : selection.columnOrdinal = column
  bound : column < 2
  shape : ∃ shape : Shape, shape.admitted ∧
    snapshot.metadata.schema = [shape.root, shape.parent, shape.first, shape.second]
  parentAt : snapshot.metadata.schema[1]? = some selection.parent
  leafAt : snapshot.metadata.schema[selection.schemaOrdinal]? = some selection.leaf
  physical : selection.leaf.physicalType = some selection.physical
  unannotated : ∀ field ∈ selection.parentItem.fields, field.id ≠ 6 ∧ field.id ≠ 10
  parentExtent : ColumnOrder.Slot.within (ColumnOrder.footerReader limits snapshot)
    ⟨selection.container, selection.parentItem⟩
  leafExtent : ColumnOrder.Slot.within (ColumnOrder.footerReader limits snapshot)
    ⟨selection.container, selection.leafItem⟩
  items : ∃ items, ItemsWire limits snapshot selection.container items ∧ items.length = 4 ∧
    items[1]? = some selection.parentItem ∧ items[selection.schemaOrdinal]? = some selection.leafItem

end Silmaril.Formats.Parquet.Footer.NestedLeaf
