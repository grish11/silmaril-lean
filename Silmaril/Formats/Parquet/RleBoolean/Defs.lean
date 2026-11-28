module

public import Silmaril.Formats.Parquet.Page.Defs
public import Silmaril.Formats.Parquet.RleBooleanPage.Defs
public import Silmaril.Formats.Parquet.Snapshot.Defs

/-! Selected row groups of a plaintext file with one optional RLE BOOLEAN leaf. -/

public section

namespace Silmaril.Formats.Parquet.RleBoolean

structure Limits where
  snapshot : Snapshot.Limits := {}
  framing : Page.Limits := {}
  decode : RleBooleanPage.Limits :=
    ⟨⟨16 * 1024 * 1024, 16 * 1024 * 1024, ⟨1024 * 1024, 16 * 1024 * 1024⟩, 0⟩,
      ⟨1024 * 1024, 16 * 1024 * 1024⟩⟩
  maxFileBytes : Nat := 256 * 1024 * 1024
  maxChunkBytes : Nat := 64 * 1024 * 1024
  maxRows : Nat := 1024 * 1024

inductive ColumnFailure where
  | arity
  | mismatch
  | codec (actual : Int)
  | encodings
  | unsupportedOffsets
  | byteLimit
  | bounds
  | framing (reason : Page.Error)
  deriving DecidableEq, Repr

inductive PageFailure where
  | crcUnsupported
  | byteLimit
  | sizeMismatch
  | unsupportedKind
  | encoding (actual : Int)
  | slotLimit
  | decode (reason : RleBooleanPage.Error)
  deriving DecidableEq, Repr

inductive Error where
  | fileByteLimit
  | snapshot (reason : Snapshot.Error Unit)
  | schema
  | leafName (expected actual : String)
  | groupIndex (index : Nat)
  | rowLimit (group : Nat)
  | column (group : Nat) (reason : ColumnFailure)
  | groupCount (group expected actual : Nat)
  | atPage (group page headerOffset : Nat) (reason : PageFailure)
  deriving DecidableEq, Repr

@[expose] def IsOptionalBoolean (leaf : Footer.SchemaElement) : Prop :=
  leaf.physicalType = some .boolean ∧ leaf.repetition = some .optional ∧ leaf.numChildren.getD 0 = 0

instance (leaf : Footer.SchemaElement) : Decidable (IsOptionalBoolean leaf) := by
  unfold IsOptionalBoolean
  infer_instance

@[expose] def ColumnMatches (leaf : Footer.SchemaElement) (group : Footer.RowGroup)
    (column : Footer.ColumnChunk) : Prop :=
  column.metadata.pathInSchema = [leaf.name] ∧ column.metadata.physicalType = .boolean ∧
    column.metadata.numValues = group.numRows

instance (leaf : Footer.SchemaElement) (group : Footer.RowGroup) (column : Footer.ColumnChunk) :
    Decidable (ColumnMatches leaf group column) := by
  unfold ColumnMatches
  infer_instance

private def selectLeaf (name : String) (schema : List Footer.SchemaElement) : Except Error Footer.SchemaElement :=
  match schema with
  | [_, leaf] =>
    if ¬ IsOptionalBoolean leaf then .error .schema
    else if leaf.name ≠ name then .error (.leafName name leaf.name)
    else .ok leaf
  | _ => .error .schema

private def selectColumn (limits : Limits) (leaf : Footer.SchemaElement) (group : Footer.RowGroup) :
    Except ColumnFailure Footer.ColumnChunk :=
  match group.columns with
  | [column] =>
    let metadata := column.metadata
    if ¬ ColumnMatches leaf group column then .error .mismatch
    else if metadata.codec ≠ 0 then .error (.codec metadata.codec)
    else if !metadata.encodings.contains 3 || !metadata.encodings.all (· == 3) then .error .encodings
    else if metadata.dictionaryPageOffset.isSome || metadata.indexPageOffset.isSome then .error .unsupportedOffsets
    else if metadata.totalCompressedSize > (limits.maxChunkBytes : Int) then .error .byteLimit
    else .ok column
  | _ => .error .arity

/-- Keep the checked header fields and use the matched optional, uncompressed layout. -/
@[expose] def pageParameters (header : Page.Header) : Option ScalarPage.Parameters :=
  let params := fun count encoding version =>
    ⟨⟨header.compressedSize, header.uncompressedSize⟩, ⟨0, 1⟩, count, 0, encoding, version⟩
  match header.kind with
  | .dataV1 h => some (params h.numValues h.encoding (.v1 h.definitionLevelEncoding h.repetitionLevelEncoding))
  | .dataV2 h => some (params h.numValues h.encoding
      (.v2 h.numNulls h.numRows h.repetitionBytes h.definitionBytes (some h.isCompressed)))
  | .dictionary _ | .skipped _ => none

private structure Plan where
  frame : Page.Frame
  index : Nat
  params : ScalarPage.Parameters

private def planPage (limits : Limits) (group : Nat) (entry : Page.Frame × Nat) : Except Error Plan :=
  let (frame, index) := entry
  let failure := Error.atPage group index frame.header.start
  let header := frame.value
  if header.crc.isSome then .error (failure .crcUnsupported)
  else if header.compressedSize > limits.decode.page.compressedBytes ||
      header.uncompressedSize > limits.decode.page.uncompressedBytes then .error (failure .byteLimit)
  else if header.compressedSize ≠ header.uncompressedSize then .error (failure .sizeMismatch)
  else
    match pageParameters header with
    | none => .error (failure .unsupportedKind)
    | some params =>
      if params.encoding ≠ 3 then .error (failure (.encoding params.encoding))
      else if params.numValues > limits.decode.page.levels.values then .error (failure .slotLimit)
      else .ok ⟨frame, index, params⟩

private def decodePage (limits : Limits) (source : Bytes) (group : Nat) (plan : Plan) :
    Except Error (List (Option Bool)) :=
  let frame := plan.frame
  let body := Footer.fileBytes source frame.payload.start frame.payload.stop
  (RleBooleanPage.decode .boolean plan.params limits.decode body).mapError
    (Error.atPage group plan.index frame.header.start ∘ PageFailure.decode)

/-- Read the selected footer group. Check the sum of declared page slots
before slicing any body. Each page decoder checks its exact level and value extents. -/
def readGroup (limits : Limits) (source : Bytes) (name : String) (index : Nat) :
    Except Error (List (Option Bool)) :=
  if source.length > limits.maxFileBytes then .error .fileByteLimit
  else do
    let snapshot ← (Snapshot.check (Failure := Unit) limits.snapshot source).mapError .snapshot
    let leaf ← selectLeaf name snapshot.metadata.schema
    let some group := snapshot.groupAt index | throw (.groupIndex index)
    let rows := group.numRows.toNat
    if rows > limits.maxRows then .error (.rowLimit index)
    else do
      let column ← (selectColumn limits leaf group).mapError (.column index)
      let some chunk := Page.columnSpan snapshot.footer.start column.metadata |
        throw (.column index .bounds)
      let frames ← (Page.readChunk limits.framing snapshot.bytes chunk).mapError (.column index ∘ .framing)
      let plans ← frames.zipIdx.mapM (planPage limits index)
      let declared := (plans.map (·.params.numValues)).sum
      if declared ≠ rows then .error (.groupCount index rows declared)
      else do
        let pages ← plans.mapM (decodePage limits snapshot.bytes index)
        let slots := pages.flatten
        if slots.length = rows then .ok slots
        else .error (.groupCount index rows slots.length)

/-- The exact source body yields the definition mask and a length-prefixed
width-one hybrid value stream. The present slots follow that stream's order. -/
@[expose] def PageWire (limits : Limits) (source : Bytes) (frame : Page.Frame)
    (slots : List (Option Bool)) : Prop :=
  let body := Footer.fileBytes source frame.payload.start frame.payload.stop
  ∃ (params : ScalarPage.Parameters) (layout : FlatPage.Layout) (prepared : ScalarPage.Prepared),
    pageParameters frame.value = some params ∧ params.encoding = 3 ∧
    ScalarPage.validateFor 3 params limits.decode.page body = .ok layout ∧
    ScalarPage.PreparedWire params limits.decode.page layout body prepared ∧
    slots.map Option.isSome = prepared.mask ∧
    RleBooleanPage.ValuesWire (prepared.mask.count true) limits.decode.values prepared.scalars (slots.filterMap id) ∧
    slots.length = params.numValues ∧
    match params.version with
    | .v1 _ _ => True
    | .v2 nulls _ _ _ _ => (slots.filterMap id).length = params.numValues - nulls

end Silmaril.Formats.Parquet.RleBoolean
