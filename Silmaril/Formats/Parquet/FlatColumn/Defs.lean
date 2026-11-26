module

public import Silmaril.Formats.Parquet.Page.Defs
public import Silmaril.Formats.Parquet.ScalarPage.Defs
public import Silmaril.Formats.Parquet.Snapshot.Defs

/-! Selected flat columns of one immutable checked snapshot. Admission of a
page and interpretation of its exact body are separate. -/

public section

namespace Silmaril.Formats.Parquet.FlatColumn

inductive Layout where
  | required
  | optional
  deriving DecidableEq, Repr

def Layout.repetition : Layout → Footer.Repetition
  | .required => .required
  | .optional => .optional

def Layout.levels : Layout → FlatPage.LevelSchema
  | .required => ⟨0, 0⟩
  | .optional => ⟨0, 1⟩

structure Selection where
  name : String
  physical : Footer.PhysicalType
  layout : Layout
  deriving DecidableEq, Repr

inductive BindError where
  | nonFlatSchema
  | unknownLeaf (name : String)
  | leafMismatch (column : Nat) (expected : Selection)
  deriving DecidableEq, Repr

/-- The snapshot index prevents substituting metadata or payloads from a
different file. The serialized schema has its root at ordinal zero. -/
structure Binding (snapshot : Snapshot.Checked) (selection : Selection) where
  private mk ::
  columnOrdinal : Nat
  leaf : Footer.SchemaElement
  leafAt : snapshot.metadata.schema[columnOrdinal + 1]? = some leaf
  leafName : leaf.name = selection.name
  leafPhysical : leaf.physicalType = some selection.physical
  leafRepetition : leaf.repetition = some selection.layout.repetition

@[expose] def Binding.leafOrdinal {snapshot : Snapshot.Checked} {selection : Selection} (binding : Binding snapshot selection) : Nat :=
  binding.columnOrdinal + 1

/-- Bind by exact leaf name, physical type and flat nullability. The checked
footer enforces distinct names; the flat shape makes leaf and chunk order agree. -/
def bindColumn (snapshot : Snapshot.Checked) (selection : Selection) : Except BindError (Binding snapshot selection) := do
  let root :: leaves := snapshot.metadata.schema | throw .nonFlatSchema
  if root.numChildren != some (leaves.length : Int) ||
      !leaves.all (fun leaf => leaf.physicalType.isSome && leaf.numChildren.getD 0 == 0 &&
        (leaf.repetition == some .required || leaf.repetition == some .optional)) then
    throw .nonFlatSchema
  let some ordinal := leaves.findIdx? (·.name == selection.name) | throw (.unknownLeaf selection.name)
  match present : snapshot.metadata.schema[ordinal + 1]? with
  | none => throw (.unknownLeaf selection.name)
  | some leaf =>
    if matched : leaf.name = selection.name ∧ leaf.physicalType = some selection.physical ∧
        leaf.repetition = some selection.layout.repetition then
      pure ⟨ordinal, leaf, present, matched.1, matched.2.1, matched.2.2⟩
    else throw (.leafMismatch ordinal selection)

inductive Versions where
  | v1AndV2
  | v2Only
  deriving DecidableEq, Repr

/-- One raw data-page encoding, with optional V1 RLE-level admission.
Codec 0 is the only codec in this column walk. -/
structure Policy where
  encoding : Int
  versions : Versions := .v1AndV2
  deriving DecidableEq, Repr

structure Limits where
  framing : Page.Limits := {}
  maxChunkBytes : Nat := 64 * 1024 * 1024
  maxPageBytes : Nat := 16 * 1024 * 1024
  maxRows : Nat := 1024 * 1024

abbrev DecodePage (α ε : Type) :=
  Footer.SchemaElement → Footer.ColumnMetadata → Page.Header → Bytes → Except ε (List (Option α))

inductive ColumnError where
  | missing
  | association
  | codec (actual : Int)
  | encodings
  | unsupportedOffsets
  | chunkLimit
  | bounds
  | framing (reason : Page.Error)
  | rowLimit (maximum actual : Nat)
  | declaredCount (expected actual : Nat)
  | outputCount (expected actual : Nat)
  deriving DecidableEq, Repr

inductive PageError (ε : Type) where
  | crcUnsupported
  | byteLimit
  | sizeMismatch
  | unsupportedKind
  | unsupportedVersion
  | encoding (actual : Int)
  | levels
  | cardinality
  | slotLimit (maximum actual : Nat)
  | outputCount (expected actual : Nat)
  | nullCount
  | decode (reason : ε)
  deriving DecidableEq, Repr

inductive Error (ε : Type) where
  | groupIndex (group : Nat)
  | column (group column : Nat) (name : String) (reason : ColumnError)
  | page (group column : Nat) (name : String) (page headerOffset : Nat) (reason : PageError ε)
  deriving DecidableEq, Repr

/-- Preserve the resolved V2 compression flag and all wire counts. A
callback may obtain the levels from the matched flat leaf. -/
def pageParameters (layout : Layout) (codec : Int) (header : Page.Header) : Option ScalarPage.Parameters :=
  let make := fun count encoding version =>
    ⟨⟨header.compressedSize, header.uncompressedSize⟩, layout.levels, count, codec, encoding, version⟩
  match header.kind with
  | .dataV1 h => some (make h.numValues h.encoding (.v1 h.definitionLevelEncoding h.repetitionLevelEncoding))
  | .dataV2 h => some (make h.numValues h.encoding
      (.v2 h.numNulls h.numRows h.repetitionBytes h.definitionBytes (some h.isCompressed)))
  | .dictionary _ | .skipped _ => none

private def admitPage {ε : Type} (limits : Limits) (policy : Policy) (layout : Layout)
    (header : Page.Header) : Except (PageError ε) Unit := do
  if header.crc.isSome then throw .crcUnsupported
  if limits.maxPageBytes < header.compressedSize || limits.maxPageBytes < header.uncompressedSize then
    throw .byteLimit
  if header.compressedSize != header.uncompressedSize then throw .sizeMismatch
  let some params := pageParameters layout 0 header | throw .unsupportedKind
  if params.encoding != policy.encoding then throw (.encoding params.encoding)
  if limits.maxRows < params.numValues || Hybrid.runLimit ≤ params.numValues then
    throw (.slotLimit (min limits.maxRows (Hybrid.runLimit - 1)) params.numValues)
  match params.version with
  | .v1 definitions repetitions =>
    if policy.versions == .v2Only then throw .unsupportedVersion
    if definitions != 3 || repetitions != 3 then throw .levels
  | .v2 nulls rows repetitions definitions _ =>
    if repetitions != 0 || header.compressedSize < definitions ||
        (layout == .required && definitions != 0) then throw .levels
    if rows != params.numValues || params.numValues < nulls ||
        (layout == .required && nulls != 0) then throw .cardinality
  pure ()

@[expose] def frameBody (source : Bytes) (frame : Page.Frame) : Bytes :=
  Footer.fileBytes source frame.payload.start frame.payload.stop

/-- Raw number of slots declared by a data frame. Other kinds declare no slots. -/
def pageSlots (header : Page.Header) : Nat :=
  match header.kind with
  | .dataV1 h => h.numValues
  | .dataV2 h => h.numValues
  | .dictionary _ | .skipped _ => 0

private def wrongNullCount {α : Type} (leaf : Footer.SchemaElement) (header : Page.Header)
    (slots : List (Option α)) : Bool :=
  let wrongV2Nulls := match header.kind with
    | .dataV2 h => slots.countP Option.isNone != h.numNulls
    | _ => false
  wrongV2Nulls || (leaf.repetition == some .required && !slots.all Option.isSome)

private def runPage {α ε : Type} (decode : DecodePage α ε) (leaf : Footer.SchemaElement)
    (metadata : Footer.ColumnMetadata) (source : Bytes) (frame : Page.Frame) :
    Except (PageError ε) (List (Option α)) := do
  let slots ← (decode leaf metadata frame.value (frameBody source frame)).mapError .decode
  if slots.length ≠ pageSlots frame.value then .error (.outputCount (pageSlots frame.value) slots.length)
  else if wrongNullCount leaf frame.value slots then .error .nullCount
  else .ok slots

private def locateChunk (limits : Limits) (policy : Policy) (selection : Selection)
    (leaf : Footer.SchemaElement) (group : Footer.RowGroup) (metadata : Footer.ColumnMetadata)
    (footerStart : Nat) : Except ColumnError Footer.Span :=
  if ¬ (metadata.pathInSchema = [leaf.name] ∧ metadata.physicalType = selection.physical ∧
      metadata.numValues = group.numRows) then .error .association
  else if metadata.codec ≠ 0 then .error (.codec metadata.codec)
  else if !metadata.encodings.contains policy.encoding ||
      !metadata.encodings.all (fun tag => tag == policy.encoding || tag == 3) then .error .encodings
  else if metadata.dictionaryPageOffset.isSome || metadata.indexPageOffset.isSome then .error .unsupportedOffsets
  else if metadata.totalCompressedSize > (limits.maxChunkBytes : Int) ||
      metadata.totalUncompressedSize > (limits.maxChunkBytes : Int) then .error .chunkLimit
  else
    match Page.columnSpan footerStart metadata with
    | none => .error .bounds
    | some chunk => .ok chunk

/-- Select the group and chunk by ordinal from the original snapshot. All
page admission and declared slot counts are checked before body callbacks.
The callback owns the encoding-specific level and value interpretation. -/
def readColumn {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    (binding : Binding snapshot selection) (limits : Limits) (policy : Policy)
    (decode : DecodePage α ε) (groupIndex : Nat) : Except (Error ε) (List (Option α)) := do
  let columnFailure := Error.column groupIndex binding.columnOrdinal selection.name
  let some group := snapshot.groupAt groupIndex | throw (.groupIndex groupIndex)
  let rows := group.numRows.toNat
  if limits.maxRows < rows then .error (columnFailure (.rowLimit limits.maxRows rows))
  else do
    let some column := group.columns[binding.columnOrdinal]? | throw (columnFailure .missing)
    let metadata := column.metadata
    let chunk ← (locateChunk limits policy selection binding.leaf group metadata snapshot.footer.start).mapError
      columnFailure
    let frames ← (Page.readChunk limits.framing snapshot.bytes chunk).mapError (columnFailure ∘ .framing)
    let pageFailure := fun (entry : Page.Frame × Nat) =>
      Error.page groupIndex binding.columnOrdinal selection.name entry.2 entry.1.header.start
    let entries := frames.zipIdx
    entries.forM fun entry =>
      (admitPage limits policy selection.layout entry.1.value).mapError (pageFailure entry)
    let declared := (frames.map (pageSlots ∘ Page.Frame.value)).sum
    if declared ≠ rows then .error (columnFailure (.declaredCount rows declared))
    else do
      let pages ← entries.mapM fun entry =>
        (runPage decode binding.leaf metadata snapshot.bytes entry.1).mapError (pageFailure entry)
      let slots := pages.flatten
      if slots.length = rows then pure slots
      else throw (columnFailure (.outputCount rows slots.length))

/-- Successful column reads keep the original frame order, exact body extent
and the advertised slot count in every callback invocation. -/
@[expose] def CallbackWire {α ε : Type} (decode : DecodePage α ε) (leaf : Footer.SchemaElement)
    (metadata : Footer.ColumnMetadata) (source : Bytes)
    (frame : Page.Frame) (slots : List (Option α)) : Prop :=
  decode leaf metadata frame.value (frameBody source frame) = .ok slots ∧
    slots.length = pageSlots frame.value

@[expose] def ColumnWire {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    (binding : Binding snapshot selection) (limits : Limits) (decode : DecodePage α ε)
    (index : Nat) (group : Footer.RowGroup) (slots : List (Option α)) : Prop :=
  ∃ column chunk frames pages,
    snapshot.groupAt index = some group ∧
    group.columns[binding.columnOrdinal]? = some column ∧
    column.metadata.pathInSchema = [binding.leaf.name] ∧
    column.metadata.physicalType = selection.physical ∧
    column.metadata.numValues = group.numRows ∧ column.metadata.codec = 0 ∧
    Page.columnSpan snapshot.footer.start column.metadata = some chunk ∧
    Page.readChunk limits.framing snapshot.bytes chunk = .ok frames ∧
    (frames.map (pageSlots ∘ Page.Frame.value)).sum = group.numRows.toNat ∧
    List.Forall₂ (CallbackWire decode binding.leaf column.metadata snapshot.bytes) frames pages ∧
    slots = pages.flatten ∧ slots.length = group.numRows.toNat

end Silmaril.Formats.Parquet.FlatColumn
