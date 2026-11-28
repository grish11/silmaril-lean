module

public import Silmaril.Formats.Parquet.FlatColumn.Defs

/-! Read one bound flat PLAIN BYTE_ARRAY leaf as opaque byte strings in footer
group order. -/

public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.File

open Silmaril.Relational Silmaril.Formats.Arrow

structure Limits where
  snapshot : Snapshot.Limits := {}
  column : FlatColumn.Limits := {}
  maxFileBytes : Nat := 256 * 1024 * 1024
  maxFileRows : Nat := 1024 * 1024
  maxValueBytes : Nat := 16 * 1024 * 1024

/-- Apply the column caps to the scalar page and the exact value extent. -/
@[expose] def Limits.scalar (limits : Limits) : ScalarPage.Limits :=
  ⟨limits.column.maxPageBytes, limits.column.maxPageBytes,
    ⟨limits.column.maxRows, limits.column.maxPageBytes⟩, 0⟩

@[expose] def Limits.values (limits : Limits) : ByteArray.Limits :=
  ⟨limits.column.maxPageBytes, limits.maxValueBytes⟩

inductive PageError where
  | nonDataPage
  | scalar (reason : ScalarPage.Error)
  deriving DecidableEq, Repr

inductive Error where
  | fileByteLimit (maximum actual : Nat)
  | fileRowLimit (maximum actual : Nat)
  | snapshot (reason : Snapshot.Error Unit)
  | schema (reason : FlatColumn.BindError)
  | column (reason : FlatColumn.Error PageError)
  deriving DecidableEq, Repr

@[expose] def policy : FlatColumn.Policy := ⟨0, .v1AndV2⟩

/-- The layout comes from the checked selection. ScalarPage consumes the
entire original body and reconstructs nullable slots from its checked mask. -/
def decodePage (limits : Limits) (layout : FlatColumn.Layout) : FlatColumn.DecodePage Bytes PageError :=
  fun _ metadata header body => do
    let some params := FlatColumn.pageParameters layout metadata.codec header | throw .nonDataPage
    (ScalarPage.decode (.byteArray limits.values) params limits.scalar body).mapError .scalar

structure Checked (name : String) (layout : FlatColumn.Layout) where
  private mk ::
  snapshot : Snapshot.Checked
  binding : FlatColumn.Binding snapshot ⟨name, .byteArray, layout⟩

/-- Cap the file bytes before parsing the footer and the total declared rows
before binding or decoding a group. -/
def openFile (limits : Limits) (source : Bytes) (name : String) (layout : FlatColumn.Layout) :
    Except Error (Checked name layout) :=
  if limits.maxFileBytes < source.length then .error (.fileByteLimit limits.maxFileBytes source.length)
  else do
    let snapshot ← (Snapshot.check limits.snapshot source).mapError .snapshot
    let rows := snapshot.metadata.numRows.toNat
    if limits.maxFileRows < rows then .error (.fileRowLimit limits.maxFileRows rows)
    else
      (FlatColumn.bindColumn snapshot ⟨name, .byteArray, layout⟩).map (Checked.mk snapshot) |>.mapError .schema

/-- The indexed consumer preserves the original column or page failure. -/
@[expose] def Checked.readGroup {name : String} {layout : FlatColumn.Layout}
    (checked : Checked name layout) (limits : Limits) (index : Nat) :
    Except (FlatColumn.Error PageError) (List (Option Bytes)) :=
  FlatColumn.readColumn checked.binding limits.column policy (decodePage limits layout) index

/-- The field kind records the selected leaf's nullability. Both layouts
carry the same opaque bytes for present cells. -/
abbrev Value (_ : FlatColumn.Layout) := Bytes

@[expose] def schema (name : String) (layout : FlatColumn.Layout) : Scan.Schema String FlatColumn.Layout :=
  ⟨1, fun _ => (name, layout)⟩

@[expose] def rows (name : String) (layout : FlatColumn.Layout) (slots : List (Option Bytes)) :
    Reader.RowGroup (schema name layout) Value :=
  slots.map fun slot _ => slot

@[expose] def Checked.source {name : String} {layout : FlatColumn.Layout}
    (checked : Checked name layout) (limits : Limits) : Reader.Source Nat (schema name layout) Value Error :=
  ⟨List.range checked.snapshot.groupCount,
    fun index => (checked.readGroup limits index).map (rows name layout) |>.mapError .column,
    fun _ => .ok ()⟩

/-- Emit a batch only after the selected column's entire group has succeeded.
The first read error retains the preceding batches and ends the stream. -/
@[expose] def readAll (limits : Limits) (input : Bytes) (name : String) (layout : FlatColumn.Layout) :
    Events.EventStream String Value Error :=
  Reader.readAll ((openFile limits input name layout).map fun checked => ⟨schema name layout, checked.source limits⟩)

/-- The exact framed body prepares the definition mask and the PLAIN suffix.
Each present value is the original opaque octet string in that suffix. -/
@[expose] def PageWire (limits : Limits) (layout : FlatColumn.Layout) (metadata : Footer.ColumnMetadata)
    (source : Bytes) (frame : Page.Frame) (slots : List (Option Bytes)) : Prop :=
  let body := FlatColumn.frameBody source frame
  ∃ (params : ScalarPage.Parameters) (levels : FlatPage.Layout)
    (page : ScalarPage.Prepared) (values : List Bytes),
    FlatColumn.pageParameters layout metadata.codec frame.value = some params ∧
    ScalarPage.validate params limits.scalar body = .ok levels ∧
    ScalarPage.PreparedWire params limits.scalar levels body page ∧
    slots.map Option.isSome = page.mask ∧ slots.filterMap id = values ∧
    slots.length = params.numValues ∧
    page.scalars.toList = ByteArray.wire values ∧ values.length = page.mask.count true ∧
    page.scalars.length ≤ limits.values.totalBytes ∧
    ∀ value ∈ values, value.length < ByteArray.lengthLimit ∧ value.length ≤ limits.maxValueBytes

/-- Refine the selected column's callback relation with the PLAIN wire facts. -/
@[expose] def GroupWire {name : String} {layout : FlatColumn.Layout} (checked : Checked name layout)
    (limits : Limits) (index : Nat) (group : Footer.RowGroup) (slots : List (Option Bytes)) : Prop :=
  ∃ column chunk frames pages,
    checked.snapshot.groupAt index = some group ∧
    group.columns[checked.binding.columnOrdinal]? = some column ∧
    column.metadata.pathInSchema = [checked.binding.leaf.name] ∧
    column.metadata.physicalType = .byteArray ∧ column.metadata.numValues = group.numRows ∧
    column.metadata.codec = 0 ∧
    Page.columnSpan checked.snapshot.footer.start column.metadata = some chunk ∧
    Page.readChunk limits.column.framing checked.snapshot.bytes chunk = .ok frames ∧
    (frames.map (FlatColumn.pageSlots ∘ Page.Frame.value)).sum = group.numRows.toNat ∧
    List.Forall₂ (PageWire limits layout column.metadata checked.snapshot.bytes) frames pages ∧
    slots = pages.flatten ∧ slots.length = group.numRows.toNat

end Silmaril.Formats.Parquet.Plain.ByteArray.File
