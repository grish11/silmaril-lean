module

public import Silmaril.Formats.Parquet.ByteStreamSplitPage.Defs
public import Silmaril.Formats.Parquet.Page.Defs
public import Silmaril.Formats.Parquet.Snapshot.Defs

/-! A checked row group of one optional FLOAT column, as raw IEEE 754 words. -/

public section

namespace Silmaril.Formats.Parquet.FloatByteStreamSplit

structure Limits where
  snapshot : Snapshot.Limits := {}
  framing : Page.Limits := {}
  decode : ByteStreamSplitPage.Limits :=
    ⟨⟨16 * 1024 * 1024, 16 * 1024 * 1024, ⟨1024 * 1024, 16 * 1024 * 1024⟩, 0⟩,
      ⟨1024 * 1024, 16 * 1024 * 1024, 4⟩⟩
  maxFileBytes : Nat := 256 * 1024 * 1024
  maxChunkBytes : Nat := 64 * 1024 * 1024
  maxRows : Nat := 1024 * 1024

inductive PageFailure where
  | crcUnsupported
  | compressedLimit
  | outputLimit
  | sizeMismatch
  | unsupportedKind
  | encoding (actual : Int)
  | slotLimit
  | levels
  | decode (reason : ByteStreamSplitPage.Error)
  | physicalKind
  deriving DecidableEq, Repr

inductive Error where
  | fileByteLimit
  | snapshot (reason : Snapshot.Error Unit)
  | schema
  | leafName (expected actual : String)
  | groupIndex (index : Nat)
  | rowLimit (group : Nat)
  | columnArity (group : Nat)
  | columnPath (group : Nat) (actual : List String)
  | columnPhysical (group : Nat)
  | columnCount (group : Nat) (expected actual : Int)
  | columnCodec (group : Nat) (actual : Int)
  | columnEncodings (group : Nat)
  | unsupportedOffsets (group : Nat)
  | chunkByteLimit (group : Nat)
  | chunkBounds (group : Nat)
  | framing (group : Nat) (reason : Page.Error)
  | groupCount (group expected actual : Nat)
  | atPage (group page headerOffset : Nat) (reason : PageFailure)
  deriving DecidableEq, Repr

/-- The checked footer's root has exactly one flat, optional numeric leaf. -/
@[expose] def IsFlatFloat (root leaf : Footer.SchemaElement) : Prop :=
  root.physicalType = none ∧ root.numChildren = some 1 ∧
    (root.repetition = none ∨ root.repetition = some .required) ∧
    leaf.physicalType = some .float ∧ leaf.repetition = some .optional ∧
    leaf.numChildren.getD 0 = 0 ∧ leaf.typeLength = none

instance (root leaf : Footer.SchemaElement) : Decidable (IsFlatFloat root leaf) := by
  unfold IsFlatFloat
  infer_instance

private def bindLeaf (name : String) (schema : List Footer.SchemaElement) : Except Error Footer.SchemaElement :=
  match schema with
  | [root, leaf] =>
    if ¬ IsFlatFloat root leaf then .error .schema
    else if leaf.name ≠ name then .error (.leafName name leaf.name)
    else .ok leaf
  | _ => .error .schema

private def matchColumn (limits : Limits) (index : Nat) (leaf : Footer.SchemaElement)
    (group : Footer.RowGroup) : Except Error Footer.ColumnChunk :=
  match group.columns with
  | [column] =>
    let metadata := column.metadata
    if metadata.pathInSchema ≠ [leaf.name] then .error (.columnPath index metadata.pathInSchema)
    else if metadata.physicalType ≠ .float then .error (.columnPhysical index)
    else if metadata.numValues ≠ group.numRows then .error (.columnCount index group.numRows metadata.numValues)
    else if metadata.codec ≠ 0 then .error (.columnCodec index metadata.codec)
    else if !metadata.encodings.contains 9 || !metadata.encodings.all (fun id => id == 9 || id == 3) then
      .error (.columnEncodings index)
    else if metadata.dictionaryPageOffset.isSome || metadata.indexPageOffset.isSome then
      .error (.unsupportedOffsets index)
    else if metadata.totalCompressedSize > (limits.maxChunkBytes : Int) then .error (.chunkByteLimit index)
    else .ok column
  | _ => .error (.columnArity index)

/-- The original lengths, value tag and V1/V2 fields are projected unchanged.
This reader has maximum repetition zero, maximum definition one and codec zero. -/
@[expose] def pageParameters (header : Page.Header) : Option ScalarPage.Parameters :=
  let params := fun count encoding version =>
    ⟨⟨header.compressedSize, header.uncompressedSize⟩, ⟨0, 1⟩, count, 0, encoding, version⟩
  match header.kind with
  | .dataV1 h => some (params h.numValues h.encoding (.v1 h.definitionLevelEncoding h.repetitionLevelEncoding))
  | .dataV2 h => some (params h.numValues h.encoding
      (.v2 h.numNulls h.numRows h.repetitionBytes h.definitionBytes (some h.isCompressed)))
  | .dictionary _ | .skipped _ => none

private def supportedLevels (count : Nat) : ScalarPage.Version → Bool
  | .v1 defs reps => defs == 3 && reps == 3
  | .v2 _ rows reps _ _ => rows == count && reps == 0

private structure Plan where
  frame : Page.Frame
  index : Nat
  params : ScalarPage.Parameters

private def planFrame (limits : Limits) (group : Nat) (entry : Page.Frame × Nat) : Except Error Plan :=
  let (frame, index) := entry
  let failure := Error.atPage group index frame.header.start
  let header := frame.value
  if header.crc.isSome then .error (failure .crcUnsupported)
  else if header.compressedSize > limits.decode.page.compressedBytes then .error (failure .compressedLimit)
  else if header.uncompressedSize > limits.decode.page.uncompressedBytes then .error (failure .outputLimit)
  else if header.compressedSize ≠ header.uncompressedSize then .error (failure .sizeMismatch)
  else
    match pageParameters header with
    | none => .error (failure .unsupportedKind)
    | some params =>
      if params.encoding ≠ 9 then .error (failure (.encoding params.encoding))
      else if params.numValues > limits.decode.page.levels.values then .error (failure .slotLimit)
      else if !(supportedLevels params.numValues params.version) then .error (failure .levels)
      else .ok ⟨frame, index, params⟩

private def decodeFrame (limits : Limits) (source : Bytes) (leaf : Footer.SchemaElement)
    (group : Nat) (plan : Plan) : Except Error (List (Option UInt32)) := do
  let frame := plan.frame
  let failure := Error.atPage group plan.index frame.header.start
  let body := Footer.fileBytes source frame.payload.start frame.payload.stop
  let decoded ← (ByteStreamSplitPage.decode leaf .float plan.params limits.decode body).mapError (failure ∘ .decode)
  match decoded with
  | ⟨.floatBits, slots⟩ => pure slots
  | _ => throw (failure .physicalKind)

/-- Open the immutable source and read only the requested footer group. Check
the sum of the declared page slot counts before slicing or decoding any body. -/
def readGroup (limits : Limits) (source : Bytes) (name : String) (index : Nat) :
    Except Error (List (Option UInt32)) :=
  if source.length > limits.maxFileBytes then .error .fileByteLimit
  else do
    let snapshot ← (Snapshot.check (Failure := Unit) limits.snapshot source).mapError .snapshot
    let leaf ← bindLeaf name snapshot.metadata.schema
    let some group := snapshot.groupAt index | throw (.groupIndex index)
    let rows := group.numRows.toNat
    if rows > limits.maxRows then .error (.rowLimit index)
    else do
      let column ← matchColumn limits index leaf group
      let some chunk := Page.columnSpan snapshot.footer.start column.metadata | throw (.chunkBounds index)
      let frames ← (Page.readChunk limits.framing snapshot.bytes chunk).mapError (.framing index)
      let plans ← frames.zipIdx.mapM (planFrame limits index)
      let declared := (plans.map (·.params.numValues)).sum
      if declared ≠ rows then .error (.groupCount index rows declared)
      else do
        let pages ← plans.mapM (decodeFrame limits snapshot.bytes leaf index)
        let slots := pages.flatten
        if slots.length = rows then .ok slots
        else .error (.groupCount index rows slots.length)

/-- The original frame determines the definition mask and the exact bytes
of each present FLOAT word. Little-endian assembly returns those raw bits. -/
@[expose] def PageWire (limits : Limits) (source : Bytes) (frame : Page.Frame)
    (slots : List (Option UInt32)) : Prop :=
  let body := Footer.fileBytes source frame.payload.start frame.payload.stop
  ∃ (params : ScalarPage.Parameters) (layout : FlatPage.Layout) (prepared : ScalarPage.Prepared)
      (words : List (List UInt8)),
    pageParameters frame.value = some params ∧ params.encoding = 9 ∧
    ScalarPage.validateFor 9 params limits.decode.page body = .ok layout ∧
    ScalarPage.PreparedWire params limits.decode.page layout body prepared ∧
    ByteStreamSplit.Admission limits.decode.scalars 4 (prepared.mask.count true) prepared.scalars ∧
    ByteStreamSplit.LaneOrder 4 (prepared.mask.count true) prepared.scalars words ∧
    slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words.map Plain.readUInt32Word ∧
    slots.length = params.numValues ∧
    match params.version with
    | .v1 _ _ => True
    | .v2 nulls _ _ _ _ => (slots.filterMap id).length = params.numValues - nulls

end Silmaril.Formats.Parquet.FloatByteStreamSplit
