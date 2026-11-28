module

public import Silmaril.Formats.Parquet.Snapshot.Defs
public import Silmaril.Formats.ThriftCompact.Traversal.List.Defs

/-! Opt-in ColumnOrder selection from the exact footer of a checked flat snapshot. -/

public section

namespace Silmaril.Formats.Parquet.Footer.ColumnOrder

open ThriftCompact
open Traversal (Field Reader ListTrace)

inductive Error where
  | footerByteLimit
  | compact (cause : Traversal.Error)
  | footerExtent
  | missingSchema
  | duplicateField (id : Int)
  | fieldType (id : Int)
  | fieldExtent (id : Int)
  | nonFlatSchema
  | schemaCount (expected actual : Nat)
  | leafOrdinal (index : Nat)
  | orderCount (expected actual : Nat)
  | orderOrdinal (index : Nat)
  | itemExtent (id : Int)
  | orderUnion
  | markerPayload (tag : Int)
  | logicalUnion
  deriving DecidableEq, Repr

/-- A struct item includes its own STOP. Offsets are relative to the footer. -/
structure Item where
  start : Nat
  stop : Nat
  fields : List Field

structure Slot where
  container : Field
  item : Item

structure Selection where
  reader : Reader
  leaf : Slot
  order : Option Slot

inductive Marker where
  | typeOrder
  | ieee754TotalOrder
  | int96TimestampOrder
  | unknown (tag : Int)
  deriving DecidableEq, Repr

@[expose] def Marker.ofTag : Int → Marker
  | 1 => .typeOrder
  | 2 => .ieee754TotalOrder
  | 3 => .int96TimestampOrder
  | tag => .unknown tag

structure FlatLeaf where
  leaf : Footer.SchemaElement
  selection : Selection
  order : Option Marker

@[expose] def footerReader (limits : Footer.Limits) (snapshot : Snapshot.Checked) : Reader :=
  ⟨Footer.fileBytes snapshot.bytes snapshot.footer.start snapshot.footer.stop,
    limits.compact, limits.varintMode⟩

@[expose] def field? (fields : List Field) (id : Int) : Except Error (Option Field) :=
  match fields.filter (·.id == id) with
  | [] => .ok none
  | [field] => .ok (some field)
  | _ => .error (.duplicateField id)

@[expose] def readItem (reader : Reader) (start : Nat) : Except Error (Item × Nat) :=
  ((Traversal.readStruct reader start).map
    fun (fields, stop) => (⟨start, stop, fields⟩, stop)).mapError .compact

def readStructList (reader : Reader) (field : Field) : Except Error (List Item) := do
  if field.type ≠ .payload .list then throw (.fieldType field.id)
  let (items, next) ← Traversal.readList reader Error.compact .struct (readItem reader) field.start
  if next ≠ field.stop then throw (.fieldExtent field.id)
  pure items

/-- Select raw items at schema ordinal `column + 1` and order ordinal `column`.
Callers that already have a checked flat binding can interpret these raw fields
in stages. The flat schema check for new callers is in `readFlat`. -/
@[expose] def readSelection (limits : Footer.Limits) (snapshot : Snapshot.Checked) (column : Nat) :
    Except Error Selection := do
  if snapshot.footer.stop - snapshot.footer.start > limits.maxFooterBytes then throw .footerByteLimit
  let reader := footerReader limits snapshot
  let (fields, stop) ← (Traversal.readStruct reader 0).mapError .compact
  if stop ≠ reader.source.length then throw .footerExtent
  let some schemaField ← field? fields 2 | throw .missingSchema
  let schema ← readStructList reader schemaField
  if schema.length ≠ snapshot.metadata.schema.length then
    throw (.schemaCount snapshot.metadata.schema.length schema.length)
  let some leaf := schema[column + 1]? | throw (.leafOrdinal (column + 1))
  let some orderField ← field? fields 7 | return ⟨reader, ⟨schemaField, leaf⟩, none⟩
  let orders ← readStructList reader orderField
  if orders.length + 1 ≠ schema.length then throw (.orderCount (schema.length - 1) orders.length)
  let some order := orders[column]? | throw (.orderOrdinal column)
  pure ⟨reader, ⟨schemaField, leaf⟩, some ⟨orderField, order⟩⟩

@[expose] def Slot.within (reader : Reader) (slot : Slot) : Prop :=
  slot.container.start ≤ slot.item.start ∧ slot.item.start < slot.item.stop ∧
    slot.item.stop ≤ slot.container.stop ∧ slot.container.stop ≤ reader.source.length

instance (reader : Reader) (slot : Slot) : Decidable (slot.within reader) := by
  unfold Slot.within
  infer_instance

/-- Interpret only the IDL marker. The selected physical/logical type and
statistics semantics are the caller's responsibility. -/
def readMarker (reader : Reader) (item : Item) : Except Error Marker := do
  let [member] := item.fields | throw .orderUnion
  if member.type ≠ .payload .struct then throw (.fieldType member.id)
  let (fields, stop) ← (Traversal.readStruct reader member.start).mapError .compact
  if stop ≠ member.stop then throw (.fieldExtent member.id)
  if (member.id = 1 ∨ member.id = 2 ∨ member.id = 3) ∧ !fields.isEmpty then
    throw (.markerPayload member.id)
  pure (Marker.ofTag member.id)

@[expose] def isFlat (root : Footer.SchemaElement) (leaves : List Footer.SchemaElement) : Bool :=
  root.numChildren == some (leaves.length : Int) &&
    leaves.all (fun leaf => leaf.physicalType.isSome && leaf.numChildren.getD 0 == 0 &&
      (leaf.repetition == some .required || leaf.repetition == some .optional))

/-- Read a required or optional physical leaf of a flat schema and its
optional ColumnOrder. A missing order list produces `none`. -/
def readFlat (limits : Footer.Limits) (snapshot : Snapshot.Checked) (column : Nat) :
    Except Error FlatLeaf := do
  let root :: leaves := snapshot.metadata.schema | throw .nonFlatSchema
  if !isFlat root leaves then throw .nonFlatSchema
  let some leaf := leaves[column]? | throw (.leafOrdinal (column + 1))
  let selected ← readSelection limits snapshot column
  if ¬ selected.leaf.within selected.reader then throw (.itemExtent 2)
  let marker ← selected.order.mapM fun slot => do
    if ¬ slot.within selected.reader then throw (.itemExtent 7)
    readMarker selected.reader slot.item
  pure ⟨leaf, selected, marker⟩

/-- Read only the legacy converted code from the selected original field. -/
def FlatLeaf.convertedType (leaf : FlatLeaf) : Except Error (Option Int) := do
  let some field ← field? leaf.selection.leaf.item.fields 6 | return none
  if field.type ≠ .payload .i32 then throw (.fieldType 6)
  let reader := leaf.selection.reader
  let (value, stop) ← (readSigned .i32 reader.mode reader.source field.start).mapError (.compact ∘ .compact)
  if stop ≠ field.stop then throw (.fieldExtent 6)
  pure (some value)

/-- Read the selected logical union member and its original payload span.
Its type-specific interpretation belongs to the consumer. -/
def FlatLeaf.logicalMember (leaf : FlatLeaf) : Except Error (Option Field) := do
  let some field ← field? leaf.selection.leaf.item.fields 10 | return none
  if field.type ≠ .payload .struct then throw (.fieldType 10)
  let (members, stop) ← (Traversal.readStruct leaf.selection.reader field.start).mapError .compact
  if stop ≠ field.stop then throw (.fieldExtent 10)
  let [member] := members | throw .logicalUnion
  pure (some member)

/-- Exact list payload from its original collection header through its last
item's STOP, in original list order. -/
@[expose] def StructListWire (reader : Reader) (field : Field) (items : List Item) : Prop :=
  field.type = .payload .list ∧ ∃ header first,
    readCollectionHeader reader.mode reader.limits.maxCollectionSize reader.source field.start =
      .ok (header, first) ∧ header.elementType = .struct ∧ header.size = items.length ∧
      ListTrace (readItem reader) first items field.stop

/-- Source, original container fields, and the two original list ordinals. -/
structure SelectionWire (limits : Footer.Limits) (snapshot : Snapshot.Checked) (column : Nat)
    (result : Selection) : Prop where
  cap : snapshot.footer.stop - snapshot.footer.start ≤ limits.maxFooterBytes
  reader : result.reader = footerReader limits snapshot
  fields : ∃ root schema,
    Traversal.readStruct result.reader 0 = .ok (root, result.reader.source.length) ∧
    root.filter (·.id == 2) = [result.leaf.container] ∧
    StructListWire result.reader result.leaf.container schema ∧
    schema.length = snapshot.metadata.schema.length ∧
    schema[column + 1]? = some result.leaf.item ∧
    match result.order with
    | none => root.filter (·.id == 7) = []
    | some order => ∃ orders, root.filter (·.id == 7) = [order.container] ∧
      StructListWire result.reader order.container orders ∧ orders.length + 1 = schema.length ∧
      orders[column]? = some order.item

structure MarkerWire (reader : Reader) (item : Item) (marker : Marker) : Prop where
  payload : ∃ member fields, item.fields = [member] ∧ marker = Marker.ofTag member.id ∧
    member.type = .payload .struct ∧ Traversal.readStruct reader member.start = .ok (fields, member.stop) ∧
    (member.id = 1 ∨ member.id = 2 ∨ member.id = 3 → fields = [])

structure FlatWire (limits : Footer.Limits) (snapshot : Snapshot.Checked) (column : Nat)
    (result : FlatLeaf) : Prop where
  selection : SelectionWire limits snapshot column result.selection
  shape : ∃ root leaves, snapshot.metadata.schema = root :: leaves ∧ isFlat root leaves = true
  leafAt : snapshot.metadata.schema[column + 1]? = some result.leaf
  leafExtent : result.selection.leaf.within result.selection.reader
  leafStruct : Traversal.readStruct result.selection.reader result.selection.leaf.item.start =
    .ok (result.selection.leaf.item.fields, result.selection.leaf.item.stop)
  order : match result.selection.order, result.order with
    | none, none => True
    | some slot, some marker => slot.within result.selection.reader ∧
      Traversal.readStruct result.selection.reader slot.item.start = .ok (slot.item.fields, slot.item.stop) ∧
      MarkerWire result.selection.reader slot.item marker
    | _, _ => False

end Silmaril.Formats.Parquet.Footer.ColumnOrder
