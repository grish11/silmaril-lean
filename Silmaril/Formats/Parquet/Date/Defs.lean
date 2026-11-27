module

public import Silmaril.Formats.DateInterop.Defs
public import Silmaril.Formats.Parquet.FlatScan.Scalar.Defs
public import Silmaril.Formats.Parquet.Snapshot.Defs

/-! # Checked DATE observations from a one-column Parquet snapshot -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date

open ThriftCompact
open ThriftCompact.Traversal (Reader Field)
open Silmaril.Numeric.Gregorian (CivilDate)

inductive Annotation where
  | logical | logicalAndConverted | converted
  deriving DecidableEq, Repr

structure Limits where
  snapshot : Snapshot.Limits := {}
  scan : FlatScan.Limits := {}
  page : ScalarPage.Limits :=
    ⟨16 * 1024 * 1024, 16 * 1024 * 1024, ⟨1024 * 1024, 16 * 1024 * 1024⟩, 0⟩

inductive Error where
  | snapshot (cause : Snapshot.Error Unit)
  | traversal (cause : Traversal.Error)
  | schemaShape
  | notFlatInt32
  | duplicateField (id : Int)
  | fieldType (id : Int)
  | fieldExtent (id : Int)
  | trailingMetadata
  | logicalDate
  | convertedType (code : Int)
  | missingAnnotation
  | groupIndex (index : Nat)
  | scan (cause : FlatScan.Error FlatScan.AdapterError)
  deriving DecidableEq, Repr

/-- The typed leaf and the accepted annotation come from the same schema index. -/
structure Binding where
  leaf : Footer.SchemaElement
  annotation : Annotation

structure RowGroup where
  binding : Binding
  rowCount : Nat
  column : FlatScan.ColumnValues rowCount

def RowGroup.date32Slots (group : RowGroup) : List (Option DateInterop.Date32.Payload) :=
  group.column.cells.toList

def RowGroup.civilSlots (group : RowGroup) : List (Option CivilDate) :=
  group.date32Slots.map (Option.map DateInterop.ParquetDate.toCivil)

namespace Internal

abbrev Read (α : Type) := Nat → Except Error (α × Nat)

def structFields (reader : Reader) : Read (List Field) := fun offset =>
  (Traversal.readStruct reader offset).mapError .traversal

def optionalField (fields : List Field) (id : Int) : Except Error (Option Field) :=
  match fields.filter (·.id == id) with
  | [] => .ok none
  | [field] => .ok (some field)
  | _ => .error (.duplicateField id)

def payload {α : Type} (field : Field) (type : ValueType) (read : Read α) : Except Error α := do
  if field.type ≠ .payload type then throw (.fieldType field.id)
  let (value, stop) ← read field.start
  if stop ≠ field.stop then throw (.fieldExtent field.id)
  return value

/-- Recover the one leaf's raw fields from the serialized schema list, at index one. -/
def leafFields (reader : Reader) : Except Error (List Field) := do
  let (metadata, stop) ← structFields reader 0
  if stop ≠ reader.source.length then throw .trailingMetadata
  let some schema ← optionalField metadata 2 | throw .schemaShape
  let [_, leaf] ← payload schema .list
    (Traversal.readList reader .traversal .struct (structFields reader)) | throw .schemaShape
  return leaf

def convertedCode (reader : Reader) (field : Field) : Except Error Int :=
  payload field .i32 fun offset =>
    (readSigned .i32 reader.mode reader.source offset).mapError (.traversal ∘ .compact)

/-- IDL LogicalType member 6 is DATE and its payload is an empty struct. -/
def checkLogicalDate (reader : Reader) (field : Field) : Except Error Unit := do
  let [member] ← payload field .struct (structFields reader) | throw .logicalDate
  if member.id ≠ 6 then throw .logicalDate
  let [] ← payload member .struct (structFields reader) | throw .logicalDate
  return ()

/-- The boolean indicates a present and already validated modern DATE. -/
def classify (logical : Bool) (converted : Option Int) : Except Error Annotation :=
  match logical, converted with
  | true, none => .ok .logical
  | false, none => .error .missingAnnotation
  | _, some code =>
    if code = 6 then
      .ok (if logical then .logicalAndConverted else .converted)
    else .error (.convertedType code)

/-- The modern field is checked before considering any legacy annotation. -/
def readAnnotation (reader : Reader) (fields : List Field) : Except Error Annotation := do
  let logical ← optionalField fields 10
  let _ ← logical.mapM (checkLogicalDate reader)
  let legacy ← optionalField fields 6
  let converted ← legacy.mapM (convertedCode reader)
  classify logical.isSome converted

def annotationReader (limits : Footer.Limits) (snapshot : Snapshot.Checked) : Reader :=
  ⟨Footer.fileBytes snapshot.bytes snapshot.footer.start snapshot.footer.stop,
    limits.compact, limits.varintMode⟩

end Internal

def IsDateLeaf (leaf : Footer.SchemaElement) : Prop :=
  leaf.physicalType = some .int32 ∧ leaf.numChildren.getD 0 = 0 ∧
    (leaf.repetition = some .required ∨ leaf.repetition = some .optional)

instance (leaf : Footer.SchemaElement) : Decidable (IsDateLeaf leaf) := by
  unfold IsDateLeaf
  infer_instance

/-- Resolve index one in the typed and raw views of this checked footer. -/
def bind (limits : Footer.Limits) (snapshot : Snapshot.Checked) : Except Error Binding := do
  let [_, leaf] := snapshot.metadata.schema | throw .schemaShape
  if ¬ IsDateLeaf leaf then throw .notFlatInt32
  let reader := Internal.annotationReader limits snapshot
  let fields ← Internal.leafFields reader
  let annotation ← Internal.readAnnotation reader fields
  return ⟨leaf, annotation⟩

/-- Associate the chosen group's one chunk with the annotated flat leaf. -/
def checkColumn (binding : Binding) (group : Footer.RowGroup) : Except Error Unit := do
  let [chunk] := group.columns | throw (.scan .columnArity)
  let path := chunk.metadata.pathInSchema
  if path ≠ [binding.leaf.name] then throw (.scan (.columnPath binding.leaf.name path))

end Silmaril.Formats.Parquet.Date
end

public section

namespace Silmaril.Formats.Parquet.Date

/-- A DATE binding and the immutable checked snapshot from which it was read. -/
structure Checked where
  private mk ::
  snapshot : Snapshot.Checked
  binding : Binding

def openChecked (limits : Limits) (source : Bytes) : Except Error Checked := do
  let snapshot ← (Snapshot.check (Failure := Unit) limits.snapshot source).mapError .snapshot
  let binding ← bind limits.snapshot.footer snapshot
  return ⟨snapshot, binding⟩

/-- Opt in to the pinned zero-page footer profile before the same DATE
annotation binding. Strict `openChecked` still uses the original validator. -/
def openCheckedPageLess (limits : Limits) (source : Bytes) :
    Except (Footer.PageLessInt32.Error ⊕ Error) Checked := do
  let snapshot ← (Snapshot.checkPageLessInt32 limits.snapshot source).mapError Sum.inl
  let binding ← (bind limits.snapshot.footer snapshot).mapError Sum.inr
  return ⟨snapshot, binding⟩

/-- Read one group from the retained snapshot without reopening its footer. -/
@[expose] def Checked.readGroup (checked : Checked) (limits : Limits) (index : Nat) : Except Error RowGroup := do
  let some group := checked.snapshot.groupAt index | throw (.groupIndex index)
  checkColumn checked.binding group
  let snapshot := checked.snapshot
  let batch ← (FlatScan.scanRowGroup limits.scan (FlatScan.decodeInt32Page limits.page)
    snapshot.bytes snapshot.footer.start snapshot.metadata.schema group).mapError .scan
  let [(_, values)] := batch.columns | throw (.scan .columnArity)
  return ⟨checked.binding, batch.rowCount, values⟩

/-- Open a one-column DATE file and read its selected group. -/
@[expose] def readGroup (limits : Limits) (source : Bytes) (index : Nat) : Except Error RowGroup := do
  let checked ← openChecked limits source
  checked.readGroup limits index

end Silmaril.Formats.Parquet.Date
