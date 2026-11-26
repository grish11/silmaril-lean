module

public import Silmaril.Formats.Parquet.FlatScan.Defs
public import Silmaril.Formats.Parquet.DictionaryIndex.Defs

/-! Bounded dictionary state for one local, flat, uncompressed INT32 column chunk. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.DictionaryChunk

structure Limits where
  page : Page.Limits := {}
  scalar : ScalarPage.Limits := ⟨16 * 1024 * 1024, 16 * 1024 * 1024, ⟨1024 * 1024, 16 * 1024 * 1024⟩, 0⟩
  indices : Hybrid.Limits := ⟨1024 * 1024, 16 * 1024 * 1024⟩
  maxRows : Nat := 1024 * 1024
  maxEntries : Nat := 1024 * 1024
  maxDictionaryBytes : Nat := 4 * 1024 * 1024

inductive Error where
  | columnPath | columnType | columnCodec | columnBounds | rowCount | rowLimit
  | page (reason : Page.Error)
  | skippedPage | misplacedDictionary | dictionaryOffset | dataOffset | missingDictionary
  | crcUnsupported | dictionaryEncoding | pageEncoding | levelEncoding
  | entryLimit | dictionaryByteLimit | pageByteLimit | pageSize | requiredNull
  | dictionaryBody (reason : Plain.Error)
  | plainPage (reason : ScalarPage.Error)
  | dictionaryPage (reason : DictionaryIndex.Error)
  deriving DecidableEq, Repr

structure Dictionary where
  frame : Page.Frame
  entries : Array Int32
  deriving DecidableEq, Repr

structure DataPage where
  frame : Page.Frame
  params : ScalarPage.Parameters
  deriving Repr

/-- An optional typed dictionary followed by data pages, in original wire order. -/
structure Chunk where
  span : Footer.Span
  dictionary : Option Dictionary
  data : List DataPage
  deriving Repr

/-- The original frame order, including the dictionary when present. -/
def Chunk.frames (chunk : Chunk) : List Page.Frame :=
  chunk.dictionary.toList.map (·.frame) ++ chunk.data.map (·.frame)

/-- All offsets are absolute in the snapshot that yielded the frame. -/
def body (source : Bytes) (frame : Page.Frame) : Bytes :=
  Footer.fileBytes source frame.payload.start frame.payload.stop

/-- The dictionary holds the exact PLAIN words in their original order. -/
def Dictionary.Exact (limits : Limits) (source : Bytes) (dictionary : Dictionary) : Prop :=
  ∃ header entries,
    dictionary.frame.value.kind = .dictionary header ∧
    (header.encoding = 0 ∨ header.encoding = 2) ∧
    dictionary.frame.value.crc = none ∧ header.numValues ≤ limits.maxEntries ∧
    dictionary.frame.value.compressedSize ≤ limits.maxDictionaryBytes ∧
    dictionary.frame.value.compressedSize = dictionary.frame.value.uncompressedSize ∧
    Plain.decodeInt32 header.numValues (body source dictionary.frame) = .ok entries ∧
    dictionary.entries = entries.toArray ∧ entries.length = header.numValues

/-- A checked data page is either PLAIN or refers to the chunk's one dictionary. -/
def DataPage.Admitted (limits : Limits) (layout : FlatPage.Layout) (dictionary : Option Dictionary)
    (page : DataPage) : Prop :=
  ((∃ header, page.frame.value.kind = .dataV1 header) ∨
    (∃ header, page.frame.value.kind = .dataV2 header)) ∧
  page.params.sizes = ⟨page.frame.value.compressedSize, page.frame.value.uncompressedSize⟩ ∧
  page.params.schema = ⟨0, if layout == .required then 0 else 1⟩ ∧
  page.frame.value.crc = none ∧
  page.params.sizes.compressed ≤ limits.scalar.compressedBytes ∧
  page.params.sizes.uncompressed ≤ limits.scalar.uncompressedBytes ∧
  (page.params.encoding = 0 ∨
    ((page.params.encoding = 2 ∨ page.params.encoding = 8) ∧ dictionary.isSome))

/-- Ordered nullable slots from the checked physical decoder for this page. -/
def DataPage.Decodes (limits : Limits) (source : Bytes) (dictionary : Option Dictionary)
    (page : DataPage) (slots : List (Option Int32)) : Prop :=
  (page.params.encoding = 0 ∧
    ScalarPage.decode .int32 page.params limits.scalar (body source page.frame) = .ok slots) ∨
  (∃ d, dictionary = some d ∧
    DictionaryIndex.decode d.entries page.params limits.scalar limits.indices
      (body source page.frame) = .ok slots)

/-- Successful admission preserves the framed bytes, validates declared offsets,
and counts only data slots. -/
structure Admitted (limits : Limits) (source : Bytes) (footerStart rowCount : Nat)
    (layout : FlatPage.Layout) (column : Footer.ColumnMetadata) (chunk : Chunk) : Prop where
  interval : Page.columnSpan footerStart column = some chunk.span
  frames : Page.readChunk limits.page source chunk.span = .ok chunk.frames
  dictionaryOffset : chunk.dictionary.map (fun d => (d.frame.header.start : Int)) =
    column.dictionaryPageOffset
  dataOffset : chunk.data.head?.map (fun p => (p.frame.header.start : Int)) = some column.dataPageOffset
  dictionary : ∀ d, chunk.dictionary = some d → d.Exact limits source
  data : ∀ page ∈ chunk.data, page.Admitted limits layout chunk.dictionary
  slots : (chunk.data.map (·.params.numValues)).sum = rowCount

namespace Internal

/-- A dictionary in any later position is left for data-page admission to reject. -/
def splitLeading : List Page.Frame → Option Page.Frame × List Page.Frame
  | frame :: rest =>
    match frame.value.kind with
    | .dictionary _ => (some frame, rest)
    | _ => (none, frame :: rest)
  | [] => (none, [])

def readDictionary (limits : Limits) (source : Bytes) (frame : Page.Frame) :
    Except Error Dictionary :=
  match frame.value.kind with
  | .dictionary header =>
    if frame.value.crc ≠ none then .error .crcUnsupported
    else if header.encoding ≠ 0 ∧ header.encoding ≠ 2 then .error .dictionaryEncoding
    else if limits.maxEntries < header.numValues then .error .entryLimit
    else if limits.maxDictionaryBytes < frame.value.compressedSize then .error .dictionaryByteLimit
    else if frame.value.compressedSize ≠ frame.value.uncompressedSize then .error .pageSize
    else do
      let entries ← (Plain.decodeInt32 header.numValues (body source frame)).mapError .dictionaryBody
      pure ⟨frame, entries.toArray⟩
  | _ => .error .misplacedDictionary

/-- Some legacy writers use BIT_PACKED for an absent level section. Normalizing
that tag at maximum level zero never admits a bit-packed level stream. -/
def levelTag (maximum : Nat) (tag : Int) : Int :=
  if maximum == 0 && tag == 4 then 3 else tag

def dataParameters (layout : FlatPage.Layout) (header : Page.Header) :
    Except Error ScalarPage.Parameters :=
  let definition := if layout == .required then 0 else 1
  let levels : FlatPage.LevelSchema := ⟨0, definition⟩
  let sizes : ScalarPage.Sizes := ⟨header.compressedSize, header.uncompressedSize⟩
  match header.kind with
  | .dictionary _ => .error .misplacedDictionary
  | .skipped _ => .error .skippedPage
  | .dataV1 info =>
    let defTag := levelTag definition info.definitionLevelEncoding
    let repTag := levelTag 0 info.repetitionLevelEncoding
    if defTag ≠ 3 ∨ repTag ≠ 3 then .error .levelEncoding
    else .ok ⟨sizes, levels, info.numValues, 0, info.encoding, .v1 defTag repTag⟩
  | .dataV2 info =>
    .ok ⟨sizes, levels, info.numValues, 0, info.encoding,
      .v2 info.numNulls info.numRows info.repetitionBytes info.definitionBytes (some info.isCompressed)⟩

def admitData (limits : Limits) (layout : FlatPage.Layout) (dictionary : Option Dictionary)
    (frame : Page.Frame) : Except Error DataPage := do
  let params ← dataParameters layout frame.value
  if frame.value.crc ≠ none then .error .crcUnsupported
  else if limits.scalar.compressedBytes < params.sizes.compressed ∨
      limits.scalar.uncompressedBytes < params.sizes.uncompressed then .error .pageByteLimit
  else if params.sizes.compressed ≠ params.sizes.uncompressed then .error .pageSize
  else if params.encoding ≠ 0 ∧ params.encoding ≠ 2 ∧ params.encoding ≠ 8 then .error .pageEncoding
  else if params.encoding ≠ 0 ∧ dictionary = none then .error .missingDictionary
  else .ok ⟨frame, params⟩

def admit (limits : Limits) (source : Bytes) (span : Footer.Span) (layout : FlatPage.Layout)
    (rowCount : Nat) (column : Footer.ColumnMetadata) (frames : List Page.Frame) : Except Error Chunk :=
  let (leading, rest) := splitLeading frames
  if leading.map (fun frame => (frame.header.start : Int)) ≠ column.dictionaryPageOffset then
    .error .dictionaryOffset
  else if rest.head?.map (fun frame => (frame.header.start : Int)) ≠ some column.dataPageOffset then
    .error .dataOffset
  else do
    let dictionary ← leading.mapM (readDictionary limits source)
    let data ← rest.mapM (admitData limits layout dictionary)
    let slots := (data.map (·.params.numValues)).sum
    if slots ≠ rowCount then .error .rowCount
    else .ok ⟨span, dictionary, data⟩

/-- Dispatch only the supported PLAIN and dictionary data encodings. -/
def decodePage (limits : Limits) (source : Bytes) (dictionary : Option Dictionary)
    (page : DataPage) : Except Error (List (Option Int32)) :=
  if page.params.encoding = 0 then
    (ScalarPage.decode .int32 page.params limits.scalar (body source page.frame)).mapError .plainPage
  else
    match dictionary with
    | none => .error .missingDictionary
    | some dictionary =>
      (DictionaryIndex.decode dictionary.entries page.params limits.scalar limits.indices
        (body source page.frame)).mapError .dictionaryPage

end Internal

/-- Check one chunk for a schema field from the same footer and snapshot.
The caller supplies the row group's declared count. No data body is copied here. -/
def read (limits : Limits) (source : Bytes) (footerStart : Nat) (field : FlatScan.Field)
    (rowCount : Nat) (column : Footer.ColumnMetadata) : Except Error Chunk :=
  if column.pathInSchema ≠ [field.name] then .error .columnPath
  else if column.physicalType ≠ .int32 then .error .columnType
  else if column.codec ≠ 0 then .error .columnCodec
  else if column.numValues ≠ (rowCount : Int) then .error .rowCount
  else if limits.maxRows < rowCount then .error .rowLimit
  else if column.indexPageOffset.isSome then .error .skippedPage
  else match Page.columnSpan footerStart column with
    | none => .error .columnBounds
    | some span => do
      let frames ← (Page.readChunk limits.page source span).mapError .page
      Internal.admit limits source span field.layout rowCount column frames

/-- Decode the admitted data pages in wire order using one dictionary scoped
only to this chunk. Dictionary entries never count as data slots. -/
def scanColumn (limits : Limits) (source : Bytes) (footerStart : Nat) (field : FlatScan.Field)
    (rowCount : Nat) (column : Footer.ColumnMetadata) : Except Error (List (Option Int32)) := do
  let chunk ← read limits source footerStart field rowCount column
  let pages ← chunk.data.mapM (Internal.decodePage limits source chunk.dictionary)
  let slots := pages.flatten
  if slots.length ≠ rowCount then .error .rowCount
  else if field.layout = .required ∧ slots.any Option.isNone then .error .requiredNull
  else .ok slots

end Silmaril.Formats.Parquet.DictionaryChunk
