module

public import Silmaril.Formats.Parquet.DictionaryIndex.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.File.Defs

/-! One selected flat optional BYTE_ARRAY chunk with an optional leading
dictionary and explicit RLE_DICTIONARY or PLAIN data-page dispatch. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback

structure Limits where
  file : Plain.ByteArray.File.Limits := {}
  maxDictionaryEntries : Nat := 1024 * 1024
  maxDictionaryBytes : Nat := 4 * 1024 * 1024

def Limits.dictionary (limits : Limits) : Plain.ByteArray.Limits :=
  ⟨min limits.maxDictionaryBytes limits.file.column.maxPageBytes, limits.file.maxValueBytes⟩

def Limits.indices (limits : Limits) : Hybrid.Limits :=
  ⟨limits.file.column.maxRows, limits.file.column.maxPageBytes⟩

inductive DecodeError where
  | missingDictionary
  | dictionaryEncoding (actual : Int)
  | unadvertisedEncoding (actual : Int)
  | dictionaryEntryLimit (maximum actual : Nat)
  | dictionaryBody (reason : Plain.Error)
  | plain (reason : ScalarPage.Error)
  | indices (reason : DictionaryIndex.Error)
  deriving DecidableEq, Repr

abbrev Error := FlatColumn.Error DecodeError
abbrev Checked (name : String) := Plain.ByteArray.File.Checked name .optional

/-- Bind the existing checked byte-array selection, with its file and total
row caps. The per-group profile is selected separately by `readGroup`. -/
def openFile (limits : Limits) (input : Bytes) (name : String) :
    Except Plain.ByteArray.File.Error (Checked name) :=
  Plain.ByteArray.File.openFile limits.file input name .optional

def locate (limits : Limits) (leaf : Footer.SchemaElement) (group : Footer.RowGroup)
    (metadata : Footer.ColumnMetadata) (footerStart : Nat) : Except FlatColumn.ColumnError Footer.Span :=
  if ¬ (metadata.pathInSchema = [leaf.name] ∧ metadata.physicalType = .byteArray ∧
      metadata.numValues = group.numRows) then .error .association
  else if metadata.codec ≠ 0 then .error (.codec metadata.codec)
  else if !metadata.encodings.all (fun tag => tag == 0 || tag == 3 || tag == 8) then .error .encodings
  else if metadata.indexPageOffset.isSome then .error .unsupportedOffsets
  else if metadata.totalCompressedSize > (limits.file.column.maxChunkBytes : Int) ||
      metadata.totalUncompressedSize > (limits.file.column.maxChunkBytes : Int) then .error .chunkLimit
  else
    match Page.columnSpan footerStart metadata with
    | none => .error .bounds
    | some span => .ok span

def splitLeading : List Page.Frame → Option Page.Frame × List Page.Frame
  | frame :: rest =>
    match frame.value.kind with
    | .dictionary _ => (some frame, rest)
    | _ => (none, frame :: rest)
  | [] => (none, [])

def bodyLimits (maxBytes : Nat) (header : Page.Header) : Except (FlatColumn.PageError DecodeError) Unit :=
  if header.crc ≠ none then .error .crcUnsupported
  else if maxBytes < header.compressedSize ∨ maxBytes < header.uncompressedSize then .error .byteLimit
  else if header.compressedSize ≠ header.uncompressedSize then .error .sizeMismatch
  else .ok ()

/-- Decode exact PLAIN length-prefixed entries in original dictionary order.
Both entry count and byte caps apply before the slice is copied. -/
def readDictionary (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes) (frame : Page.Frame) :
    Except (FlatColumn.PageError DecodeError) (Array Bytes) := do
  let .dictionary header := frame.value.kind | throw .unsupportedKind
  bodyLimits limits.dictionary.totalBytes frame.value
  if header.encoding ≠ 0 then .error (.decode (.dictionaryEncoding header.encoding))
  else if !metadata.encodings.contains 0 then .error (.decode (.unadvertisedEncoding 0))
  else if limits.maxDictionaryEntries < header.numValues then
    .error (.decode (.dictionaryEntryLimit limits.maxDictionaryEntries header.numValues))
  else do
    let body := FlatColumn.frameBody source frame
    let entries ← (Plain.ByteArray.decode limits.dictionary header.numValues body).mapError (.decode ∘ .dictionaryBody)
    return entries.toArray

def decodeData (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (dictionary : Option (Array Bytes)) (frame : Page.Frame) :
    Except (FlatColumn.PageError DecodeError) (List (Option Bytes)) := do
  bodyLimits limits.file.column.maxPageBytes frame.value
  let some params := FlatColumn.pageParameters .optional 0 frame.value | throw .unsupportedKind
  let cap := min limits.file.column.maxRows (Hybrid.runLimit - 1)
  if params.encoding ≠ 0 ∧ params.encoding ≠ 8 then .error (.encoding params.encoding)
  else if !metadata.encodings.contains params.encoding then .error (.decode (.unadvertisedEncoding params.encoding))
  else if cap < params.numValues then .error (.slotLimit cap params.numValues)
  else if params.encoding = 0 then
    (ScalarPage.decode (.byteArray limits.file.values) params limits.file.scalar
      (FlatColumn.frameBody source frame)).mapError (.decode ∘ .plain)
  else do
    let some entries := dictionary | throw (.decode .missingDictionary)
    (DictionaryIndex.decode entries params limits.file.scalar limits.indices
      (FlatColumn.frameBody source frame)).mapError (.decode ∘ .indices)

def declaredSlots (frame : Page.Frame) : Nat :=
  ((FlatColumn.pageParameters .optional 0 frame.value).map (·.numValues)).getD 0

def readFrames (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (group column : Nat) (name : String) (rows : Nat) (frames : List Page.Frame) :
    Except Error (List (Option Bytes)) := do
  let failColumn := FlatColumn.Error.column group column name
  let failPage := fun (page : Nat) (frame : Page.Frame) =>
    FlatColumn.Error.page group column name page frame.header.start
  let (dictionary, data) := splitLeading frames
  let declared := (data.map declaredSlots).sum
  if dictionary.map (fun frame => (frame.header.start : Int)) ≠ metadata.dictionaryPageOffset ∨
      data.head?.map (fun frame => (frame.header.start : Int)) ≠ some metadata.dataPageOffset then
    .error (failColumn .unsupportedOffsets)
  else if declared ≠ rows then .error (failColumn (.declaredCount rows declared))
  else do
    let entries ← dictionary.mapM fun frame => (readDictionary limits metadata source frame).mapError (failPage 0 frame)
    let pages ← (data.zipIdx (if dictionary.isSome then 1 else 0)).mapM fun (frame, ordinal) =>
      (decodeData limits metadata source entries frame).mapError (failPage ordinal frame)
    return pages.flatten

/-- Read the selected group from the same snapshot as its binding. Dictionary
state is local to this chunk and publication waits for all frames to succeed. -/
def readGroup {name : String} (checked : Checked name) (limits : Limits) (index : Nat) :
    Except Error (List (Option Bytes)) := do
  let ordinal := checked.binding.columnOrdinal
  let failColumn := FlatColumn.Error.column index ordinal name
  let some group := checked.snapshot.groupAt index | throw (.groupIndex index)
  let rows := group.numRows.toNat
  if limits.file.column.maxRows < rows then .error (failColumn (.rowLimit limits.file.column.maxRows rows))
  else do
    let some column := group.columns[ordinal]? | throw (failColumn .missing)
    let metadata := column.metadata
    let span ← (locate limits checked.binding.leaf group metadata checked.snapshot.footer.start).mapError failColumn
    let frames ← (Page.readChunk limits.file.column.framing checked.snapshot.bytes span).mapError (failColumn ∘ .framing)
    readFrames limits metadata checked.snapshot.bytes index ordinal name rows frames

/-- Every present dictionary entry is the result of an exact bounded PLAIN
stream from the original leading frame. -/
def DictionaryWire (limits : Limits) (source : Bytes) (frame : Page.Frame) (entries : Array Bytes) : Prop :=
  ∃ header values,
    frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧
    frame.value.crc = none ∧ frame.value.compressedSize = frame.value.uncompressedSize ∧
    header.numValues ≤ limits.maxDictionaryEntries ∧ frame.value.compressedSize ≤ limits.dictionary.totalBytes ∧
    Plain.ByteArray.decode limits.dictionary header.numValues (FlatColumn.frameBody source frame) = .ok values ∧
    values.length = header.numValues ∧ (FlatColumn.frameBody source frame).toList = Plain.ByteArray.wire values ∧
    entries = values.toArray

/-- A frame's own typed header selects its checked body interpretation. The
dictionary branch uses only entries from this chunk's leading frame. -/
def PageWire (limits : Limits) (source : Bytes) (dictionary : Option (Array Bytes))
    (frame : Page.Frame) (slots : List (Option Bytes)) : Prop :=
  let body := FlatColumn.frameBody source frame
  ∃ params : ScalarPage.Parameters, ∃ layout : FlatPage.Layout, ∃ page : ScalarPage.Prepared,
    FlatColumn.pageParameters .optional 0 frame.value = some params ∧
    ScalarPage.validateFor params.encoding params limits.file.scalar body = .ok layout ∧
    ScalarPage.PreparedWire params limits.file.scalar layout body page ∧
    slots.map Option.isSome = page.mask ∧ slots.length = declaredSlots frame ∧
    ((params.encoding = 0 ∧ page.scalars.toList = Plain.ByteArray.wire (slots.filterMap id)) ∨
      (params.encoding = 8 ∧ ∃ entries indices, dictionary = some entries ∧
        DictionaryIndex.readIndices limits.indices (page.mask.count true) page.scalars = .ok indices ∧
        indices.map (fun index => entries[index]?) = (slots.filterMap id).map some))

def LeadingWire (limits : Limits) (source : Bytes) :
    Option Page.Frame → Option (Array Bytes) → Prop
  | none, none => True
  | some frame, some entries => DictionaryWire limits source frame entries
  | _, _ => False

def FramesWire (limits : Limits) (source : Bytes) (metadata : Footer.ColumnMetadata)
    (rows : Nat) (frames : List Page.Frame) (slots : List (Option Bytes)) : Prop :=
  ∃ dictionary data entries pages,
    frames = dictionary.toList ++ data ∧
    dictionary.map (fun frame : Page.Frame => (frame.header.start : Int)) = metadata.dictionaryPageOffset ∧
    data.head?.map (fun frame : Page.Frame => (frame.header.start : Int)) = some metadata.dataPageOffset ∧
    LeadingWire limits source dictionary entries ∧
    List.Forall₂ (PageWire limits source entries) data pages ∧ slots = pages.flatten ∧ slots.length = rows

def GroupWire {name : String} (checked : Checked name) (limits : Limits)
    (index : Nat) (slots : List (Option Bytes)) : Prop :=
  ∃ group column span frames,
    checked.snapshot.metadata.schema[checked.binding.leafOrdinal]? = some checked.binding.leaf ∧
    checked.snapshot.groupAt index = some group ∧
    group.columns[checked.binding.columnOrdinal]? = some column ∧
    column.metadata.pathInSchema = [checked.binding.leaf.name] ∧ column.metadata.physicalType = .byteArray ∧
    column.metadata.numValues = group.numRows ∧ column.metadata.codec = 0 ∧
    Page.columnSpan checked.snapshot.footer.start column.metadata = some span ∧
    Page.readChunk limits.file.column.framing checked.snapshot.bytes span = .ok frames ∧
    FramesWire limits checked.snapshot.bytes column.metadata group.numRows.toNat frames slots

end Silmaril.Formats.Parquet.ByteArrayFallback
