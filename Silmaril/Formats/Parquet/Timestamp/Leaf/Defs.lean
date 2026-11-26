module

public import Silmaril.Formats.Parquet.Snapshot.Defs
public import Silmaril.Formats.Parquet.Page.Defs
public import Silmaril.Formats.Parquet.Timestamp.Page.Defs

/-! # Checked selection of one flat INT64 TIMESTAMP column in a Parquet snapshot -/

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf

structure Limits where
  framing : Parquet.Page.Limits := {}
  page : ScalarPage.Limits :=
    ⟨16 * 1024 * 1024, 16 * 1024 * 1024, ⟨1024 * 1024, 16 * 1024 * 1024⟩, 0⟩
  maxRows : Nat := 1024 * 1024
  allowSnappy : Bool := false

/-- Admit uncompressed chunks and, if requested, raw Snappy blocks. -/
def Limits.admitsCodec (limits : Limits) (code : Int) : Bool :=
  code == 0 || (limits.allowSnappy && code == 1)

inductive Error where
  | snapshot (cause : Snapshot.Error Unit)
  | schemaShape
  | annotation (cause : Timestamp.Error)
  | leafMismatch
  | schemaLevels
  | groupIndex (index : Nat)
  | chunkIndex (index : Nat)
  | chunkPath (expected : String) (actual : List String)
  | chunkType
  | rowLimit
  | chunkCount (expected actual : Int)
  | chunkCodec (code : Int)
  | chunkEncoding
  | chunkBounds
  | chunkOverlap
  | framing (cause : Parquet.Page.Error)
  | rowCount (expected actual : Nat)
  | crcUnsupported (pageIndex : Nat)
  | page (pageIndex : Nat) (cause : Timestamp.Page.Error)
  deriving DecidableEq, Repr

/-- The caller cannot substitute new bytes, a different annotation, or new levels. -/
structure Bound where
  private mk ::
  snapshot : Snapshot.Checked
  ordinal : Nat
  binding : Timestamp.Binding
  levels : FlatPage.LevelSchema

abbrev Slots (bound : Bound) := List (Option (Timestamp.Page.Value bound.binding))

structure Chunk where
  group : Footer.RowGroup
  column : Footer.ColumnChunk
  span : Footer.Span

@[expose] section

namespace Internal

def metadataBytes (snapshot : Snapshot.Checked) : Bytes :=
  Footer.fileBytes snapshot.bytes snapshot.footer.start snapshot.footer.stop

def isFlat : List Footer.SchemaElement → Bool
  | [] => false
  | root :: children =>
    root.numChildren == some (Int.ofNat children.length) &&
      children.all fun leaf => leaf.physicalType.isSome && leaf.numChildren.getD 0 == 0

def leafFields (leaf : Footer.SchemaElement) :
    Option Footer.PhysicalType × Option Int × Option Footer.Repetition × String × Option Int :=
  (leaf.physicalType, leaf.typeLength, leaf.repetition, leaf.name, leaf.numChildren)

def bindSelectionWith (profile : AnnotationProfile) (limits : Footer.Limits)
    (snapshot : Snapshot.Checked) (ordinal : Nat) : Except Error (Timestamp.Binding × FlatPage.LevelSchema) := do
  if !isFlat snapshot.metadata.schema then Except.error .schemaShape
  let some leaf := snapshot.metadata.schema[ordinal]? | Except.error (.annotation (.schemaIndex ordinal))
  let binding ← (Timestamp.readMetadataWith profile limits ordinal (metadataBytes snapshot)).mapError .annotation
  if leafFields leaf ≠ leafFields binding.leaf then Except.error .leafMismatch
  let some levels := Timestamp.Page.leafLevels? binding.leaf | Except.error .schemaLevels
  return (binding, levels)

def disjoint (snapshot : Snapshot.Checked) (groupIndex columnIndex : Nat) (span : Footer.Span) : Bool :=
  snapshot.metadata.rowGroups.zipIdx.all fun (group, groupOrdinal) =>
    group.columns.zipIdx.all fun (column, columnOrdinal) =>
      (groupOrdinal == groupIndex && columnOrdinal == columnIndex) ||
        match Parquet.Page.columnSpan snapshot.footer.start column.metadata with
        | none => false
        | some other => decide (span.stop ≤ other.start ∨ other.stop ≤ span.start)

def pageSlots (frame : Parquet.Page.Frame) : Nat :=
  match frame.value.kind with
  | .dataV1 info => info.numValues
  | .dataV2 info => info.numValues
  | _ => 0

def body (bound : Bound) (frame : Parquet.Page.Frame) : Bytes :=
  Footer.fileBytes bound.snapshot.bytes frame.payload.start frame.payload.stop

def decodeFrame (limits : ScalarPage.Limits) (bound : Bound) (codec : Int)
    (frame : Parquet.Page.Frame) (index : Nat) : Except Error (Slots bound) :=
  if frame.value.crc.isSome then .error (.crcUnsupported index)
  else if limits.compressedBytes < frame.value.compressedSize then
    .error (.page index (.scalar (.payload .compressedLimit)))
  else (Timestamp.Page.decode bound.binding bound.levels codec frame.value limits
    (body bound frame)).mapError (.page index)

end Internal

/-- Raw INT64 slots are decoded with this frame's header and its payload
slice in the retained snapshot. -/
def PhysicalFrame (limits : ScalarPage.Limits) (bound : Bound) (codec : Int)
    (frame : Parquet.Page.Frame) (slots : List (Option Int64)) : Prop :=
  frame.value.crc = none ∧
    ∃ params, Timestamp.Page.parameters bound.binding.leaf bound.levels codec frame.value = .ok params ∧
      ScalarPage.decode .int64 params limits (Internal.body bound frame) = .ok slots

end

/-- Resolve the flat leaf in both the checked schema and the original footer
using the supplied annotation profile. -/
def bindWith (profile : AnnotationProfile) (limits : Footer.Limits) (snapshot : Snapshot.Checked)
    (ordinal : Nat) : Except Error Bound :=
  (Internal.bindSelectionWith profile limits snapshot ordinal).map fun (binding, levels) =>
    ⟨snapshot, ordinal, binding, levels⟩

theorem bindWith_observation (profile : AnnotationProfile) (limits : Footer.Limits)
    (snapshot : Snapshot.Checked) (ordinal : Nat) :
    (bindWith profile limits snapshot ordinal).map
        (fun bound => (bound.snapshot, bound.ordinal, bound.binding, bound.levels)) =
      (Internal.bindSelectionWith profile limits snapshot ordinal).map
        (fun selection => (snapshot, ordinal, selection)) := by
  cases read : Internal.bindSelectionWith profile limits snapshot ordinal <;>
    simp [bindWith, read, Except.map]

/-- Bind only a modern TIMESTAMP annotation. -/
@[expose] def bind (limits : Footer.Limits) (snapshot : Snapshot.Checked) (ordinal : Nat) : Except Error Bound :=
  bindWith .modernOnly limits snapshot ordinal

abbrev Internal.bindSelection := Internal.bindSelectionWith .modernOnly

theorem bind_observation (limits : Footer.Limits) (snapshot : Snapshot.Checked) (ordinal : Nat) :
    (bind limits snapshot ordinal).map (fun bound => (bound.snapshot, bound.ordinal, bound.binding, bound.levels)) =
      (Internal.bindSelection limits snapshot ordinal).map (fun selection => (snapshot, ordinal, selection)) :=
  bindWith_observation .modernOnly limits snapshot ordinal

@[expose] def openLeafWith (profile : AnnotationProfile) (limits : Snapshot.Limits) (source : Bytes)
    (ordinal : Nat) : Except Error Bound := do
  let snapshot ← (Snapshot.check (Failure := Unit) limits source).mapError .snapshot
  bindWith profile limits.footer snapshot ordinal

@[expose] def openLeaf (limits : Snapshot.Limits) (source : Bytes) (ordinal : Nat) : Except Error Bound :=
  openLeafWith .modernOnly limits source ordinal

/-- Associate the group's actual chunk ordinal and path with the annotated leaf.
Admit PLAIN with optional RLE levels and the selected codec policy. -/
@[expose] def selectChunk (limits : Limits) (bound : Bound) (index : Nat) : Except Error Chunk := do
  let some group := bound.snapshot.groupAt index | Except.error (.groupIndex index)
  let columnIndex := bound.ordinal - 1
  let some column := group.columns[columnIndex]? | Except.error (.chunkIndex columnIndex)
  let metadata := column.metadata
  let name := bound.binding.leaf.name
  if metadata.pathInSchema ≠ [name] then Except.error (.chunkPath name metadata.pathInSchema)
  if metadata.physicalType ≠ .int64 then Except.error .chunkType
  if group.numRows.toNat > limits.maxRows then Except.error .rowLimit
  if metadata.numValues ≠ group.numRows then Except.error (.chunkCount group.numRows metadata.numValues)
  if !limits.admitsCodec metadata.codec then Except.error (.chunkCodec metadata.codec)
  if !metadata.encodings.all (fun id => id == 0 || id == 3) ||
      (group.numRows != 0 && !metadata.encodings.contains 0) ||
      metadata.dictionaryPageOffset.isSome || metadata.indexPageOffset.isSome then
    Except.error .chunkEncoding
  let some span := Parquet.Page.columnSpan bound.snapshot.footer.start metadata | Except.error .chunkBounds
  if !Internal.disjoint bound.snapshot index columnIndex span then Except.error .chunkOverlap
  return ⟨group, column, span⟩

/-- Decode exactly the selected chunk from the retained source. The declared
slot total is checked before any page allocates its decoded values. -/
@[expose] def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except Error (Slots bound) := do
  let chunk ← selectChunk limits bound index
  let frames ← (Parquet.Page.readChunk limits.framing bound.snapshot.bytes chunk.span).mapError .framing
  let expected := chunk.group.numRows.toNat
  let actual := (frames.map Internal.pageSlots).sum
  if actual ≠ expected then Except.error (.rowCount expected actual)
  let pages ← frames.zipIdx.mapM fun (frame, pageIndex) =>
    Internal.decodeFrame limits.page bound chunk.column.metadata.codec frame pageIndex
  return pages.flatten

end Silmaril.Formats.Parquet.Timestamp.Leaf
