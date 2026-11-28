module

public import Silmaril.Formats.Parquet.Date.Defs
public import Silmaril.Formats.Parquet.Footer.ColumnOrder.Defs

/-! Select one physical DATE leaf in a strict, checked flat Parquet snapshot. -/

public section

namespace Silmaril.Formats.Parquet.Date.Leaf

inductive Error where
  | snapshot (cause : Snapshot.Error Unit)
  | footer (cause : Footer.ColumnOrder.Error)
  | annotation (cause : Date.Error)
  | groupIndex (index : Nat)
  | chunkIndex (column : Nat)
  | association (path : List String) (physical : Footer.PhysicalType)
  | bounds
  | overlap
  | scan (cause : FlatScan.Error FlatScan.AdapterError)
  deriving DecidableEq, Repr

/-- A caller cannot substitute the original bytes, physical ordinal or binding. -/
structure Bound where
  private mk ::
  snapshot : Snapshot.Checked
  ordinal : Nat
  binding : Date.Binding

structure Chunk where
  group : Footer.RowGroup
  column : Footer.ColumnChunk
  span : Footer.Span

abbrev Slots := List (Option DateInterop.Date32.Payload)

@[expose] section

def Bound.nullable (bound : Bound) : Bool :=
  bound.binding.leaf.repetition == some .optional

def Bound.field (bound : Bound) : FlatScan.Field :=
  ⟨bound.binding.leaf.name, if bound.nullable then .optional else .required⟩

namespace Internal

def bindSelection (limits : Footer.Limits) (snapshot : Snapshot.Checked) (ordinal : Nat) :
    Except Error Date.Binding := do
  let selected ← (Footer.ColumnOrder.readFlat limits snapshot ordinal).mapError .footer
  if ¬ Date.IsDateLeaf selected.leaf then throw (.annotation .notFlatInt32)
  let raw := selected.selection
  let annotation ← (Date.Internal.readAnnotation raw.reader raw.leaf.item.fields).mapError .annotation
  return ⟨selected.leaf, annotation⟩

/-- No other original chunk may intersect the selected in-file range. -/
def disjoint (snapshot : Snapshot.Checked) (groupIndex columnIndex : Nat) (span : Footer.Span) :
    Bool :=
  snapshot.metadata.rowGroups.zipIdx.all fun (group, groupOrdinal) =>
    group.columns.zipIdx.all fun (column, columnOrdinal) =>
      (groupOrdinal == groupIndex && columnOrdinal == columnIndex) ||
        match Page.columnSpan snapshot.footer.start column.metadata with
        | none => false
        | some other => decide (span.stop ≤ other.start ∨ other.stop ≤ span.start)

end Internal
end

/-- The scalar callback consumes this frame's original payload bytes. -/
@[expose] def PageWire (limits : ScalarPage.Limits) (bound : Bound)
    (frame : Page.Frame) (slots : Slots) : Prop :=
  frame.value.crc = none ∧ FlatScan.decodeInt32Page limits bound.field frame.value
    (Footer.fileBytes bound.snapshot.bytes frame.payload.start frame.payload.stop) = .ok slots

/-- Use zero-based physical column ordinals. Raw schema selection accounts for the root. -/
def bind (limits : Footer.Limits) (snapshot : Snapshot.Checked) (ordinal : Nat) : Except Error Bound :=
  (Internal.bindSelection limits snapshot ordinal).map fun binding => ⟨snapshot, ordinal, binding⟩

@[expose] def openLeaf (limits : Snapshot.Limits) (source : Bytes) (ordinal : Nat) :
    Except Error Bound := do
  let snapshot ← (Snapshot.check (Failure := Unit) limits source).mapError .snapshot
  bind limits.footer snapshot ordinal

/-- Check the original row group, chunk ordinal, flat path and byte range. -/
@[expose] def selectChunk (bound : Bound) (index : Nat) : Except Error Chunk := do
  let some group := bound.snapshot.groupAt index | throw (.groupIndex index)
  let some column := group.columns[bound.ordinal]? | throw (.chunkIndex bound.ordinal)
  let metadata := column.metadata
  if metadata.pathInSchema ≠ [bound.binding.leaf.name] ∨ metadata.physicalType ≠ .int32 then
    throw (.association metadata.pathInSchema metadata.physicalType)
  let some span := Page.columnSpan bound.snapshot.footer.start metadata | throw .bounds
  if !Internal.disjoint bound.snapshot index bound.ordinal span then throw .overlap
  return ⟨group, column, span⟩

/-- Decode only the selected chunk with the existing strict flat INT32 scanner. -/
@[expose] def readGroup (limits : Date.Limits) (bound : Bound) (index : Nat) : Except Error Slots := do
  let selected ← selectChunk bound index
  let values ← (FlatScan.scanColumn limits.scan (FlatScan.decodeInt32Page limits.page)
    bound.snapshot.bytes bound.snapshot.footer.start bound.field selected.group.numRows.toNat
    selected.column).mapError .scan
  return values.cells.toList

end Silmaril.Formats.Parquet.Date.Leaf
