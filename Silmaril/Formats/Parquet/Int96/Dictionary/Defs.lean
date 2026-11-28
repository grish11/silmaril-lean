module

public import Silmaril.Formats.Parquet.Page.Defs
public import Silmaril.Formats.Parquet.DictionaryIndex.Defs
public import Silmaril.Formats.Parquet.Int96.Page.Defs

/-! One leading PLAIN INT96 dictionary and uncompressed RLE_DICTIONARY data pages. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Int96.Dictionary

structure Limits where
  framing : Parquet.Page.Limits := {}
  scalar : ScalarPage.Limits := ⟨16 * 1024 * 1024, 16 * 1024 * 1024, ⟨1024 * 1024, 16 * 1024 * 1024⟩, 0⟩
  indices : Hybrid.Limits := ⟨1024 * 1024, 16 * 1024 * 1024⟩
  maxChunkBytes : Nat := 64 * 1024 * 1024
  maxRows : Nat := 1024 * 1024
  maxEntries : Nat := 1024 * 1024
  maxDictionaryBytes : Nat := 4 * 1024 * 1024

inductive PageError where
  | expectedDictionary
  | misplacedDictionary
  | dataOffset
  | checksum
  | sizeMismatch
  | dictionaryEncoding (encoding : Int)
  | dataEncoding (encoding : Int)
  | entryLimit
  | dictionaryByteLimit
  | dictionaryBody (cause : Plain.Error)
  | dictionaryEntry (cause : Int96.Page.Error)
  | parameters (cause : Int96.Page.Error)
  | scalar (cause : ScalarPage.Error)
  | indices (cause : DictionaryIndex.Error)
  | mask (cause : FlatPage.Error)
  | reference (slot index : Nat)
  deriving DecidableEq, Repr

inductive Cause where
  | leaf
  | column
  | codec (actual : Int)
  | encodingMetadata
  | unsupportedIndexPage
  | rowLimit
  | chunkLimit
  | chunkBounds
  | missingDictionary
  | missingData
  | framing (cause : Parquet.Page.Error)
  | slotCount (expected actual : Nat)
  | page (ordinal headerOffset : Nat) (cause : PageError)
  deriving DecidableEq, Repr

structure Error where
  chunkOffset : Int
  cause : Cause
  deriving DecidableEq, Repr

abbrev Slots (policy : Policy) := List (Option (Int96.Page.Value policy))

def frameBody (source : Bytes) (frame : Parquet.Page.Frame) : Bytes :=
  Footer.fileBytes source frame.payload.start frame.payload.stop

/-- Both byte and entry limits apply before reading the original PLAIN body. -/
def readDictionary (limits : Limits) (policy : Policy) (source : Bytes)
    (frame : Parquet.Page.Frame) : Except PageError (Array (Int96.Page.Value policy)) :=
  match frame.value.kind with
  | .dictionary header =>
    if frame.value.crc.isSome then .error .checksum
    else if frame.value.compressedSize ≠ frame.value.uncompressedSize then .error .sizeMismatch
    else if header.encoding ≠ 0 then .error (.dictionaryEncoding header.encoding)
    else if limits.maxEntries < header.numValues then .error .entryLimit
    else if limits.maxDictionaryBytes < frame.value.compressedSize then .error .dictionaryByteLimit
    else do
      let words ← (Plain.decodeFixedLenBytes 12 header.numValues (frameBody source frame)).mapError .dictionaryBody
      let entries ← (Int96.Page.decodeSlots 0 (words.map some)).mapError .dictionaryEntry
      return ((entries.filterMap id).map (·.toTicks policy)).toArray
  | _ => .error .expectedDictionary

def dataParameters (leaf : Footer.SchemaElement) (header : Parquet.Page.Header) :
    Except PageError ScalarPage.Parameters := do
  if let .dictionary _ := header.kind then Except.error .misplacedDictionary
  if header.compressedSize ≠ header.uncompressedSize then Except.error .sizeMismatch
  let params ← (Int96.Page.parameters leaf 0 header).mapError .parameters
  if params.encoding ≠ 8 then Except.error (.dataEncoding params.encoding)
  return params

def selectSlot {α : Type} (dictionary : Array α) (ordinal : Nat) :
    Option Nat → Except PageError (Option α)
  | none => .ok none
  | some index =>
    match dictionary[index]? with
    | some value => .ok (some value)
    | none => .error (.reference ordinal index)

/-- The reference check runs on reconstructed logical slots, so its index
counts nulls as well as present entries. -/
def selectSlots {α : Type} (dictionary : Array α) (start : Nat) (slots : List (Option Nat)) :
    Except PageError (List (Option α)) :=
  (slots.zipIdx start).mapM fun (slot, ordinal) => selectSlot dictionary ordinal slot

/-- A null has no reference. A present slot uses the original dictionary entry. -/
def SlotMatches {α : Type} (dictionary : Array α) (reference : Option Nat) (output : Option α) : Prop :=
  match reference with
  | none => output = none
  | some index => ∃ value, dictionary[index]? = some value ∧ output = some value

def decodeData (limits : Limits) {policy : Policy} (dictionary : Array (Int96.Page.Value policy))
    (params : ScalarPage.Parameters) (body : Bytes) : Except PageError (Slots policy) := do
  let prepared ← (ScalarPage.prepareFor 8 params limits.scalar body).mapError .scalar
  let references ← (DictionaryIndex.readIndices limits.indices (prepared.mask.count true) prepared.scalars).mapError
    .indices
  let slots ← (FlatPage.reconstruct prepared.mask references).mapError .mask
  selectSlots dictionary 0 slots

def locate (limits : Limits) (footerStart rowCount : Nat) (leaf : Footer.SchemaElement)
    (column : Footer.ColumnMetadata) : Except Cause Footer.Span :=
  if (Int96.Page.leafLevels? leaf).isNone then .error .leaf
  else if column.physicalType ≠ .int96 ∨ column.pathInSchema ≠ [leaf.name] ∨ column.numValues ≠ rowCount ∨
      column.totalUncompressedSize ≠ column.totalCompressedSize then .error .column
  else if column.codec ≠ 0 then .error (.codec column.codec)
  else if !column.encodings.contains 8 || !column.encodings.all (fun tag => tag == 0 || tag == 3 || tag == 8) then
    .error .encodingMetadata
  else if column.indexPageOffset.isSome then .error .unsupportedIndexPage
  else if limits.maxRows < rowCount then .error .rowLimit
  else if column.dictionaryPageOffset.isNone then .error .missingDictionary
  else if column.totalCompressedSize > limits.maxChunkBytes then .error .chunkLimit
  else
    match Parquet.Page.columnSpan footerStart column with
    | some span => .ok span
    | none => .error .chunkBounds

def atPage (ordinal : Nat) (frame : Parquet.Page.Frame) (cause : PageError) : Cause :=
  .page ordinal frame.header.start cause

def checkDataOffset (column : Footer.ColumnMetadata) : List Parquet.Page.Frame → Except Cause Unit
  | [] => .error .missingData
  | data :: _ =>
    if (data.header.start : Int) = column.dataPageOffset then .ok ()
    else .error (atPage 1 data .dataOffset)

def checkSlotCount (expected actual : Nat) : Except Cause Unit :=
  if actual = expected then .ok () else .error (.slotCount expected actual)

/-- Check one declared local chunk from the supplied source. The dictionary
is constructed here and cannot be supplied by another chunk or row group. -/
def read (limits : Limits) (policy : Policy) (source : Bytes) (footerStart rowCount : Nat)
    (leaf : Footer.SchemaElement) (column : Footer.ColumnMetadata) : Except Error (Slots policy) :=
  readChunk.mapError (Error.mk (column.dictionaryPageOffset.getD column.dataPageOffset))
where
  readChunk : Except Cause (Slots policy) := do
    let span ← locate limits footerStart rowCount leaf column
    let frames ← (Parquet.Page.readChunk limits.framing source span).mapError .framing
    let first :: rest := frames | Except.error .missingDictionary
    let dictionary ← (readDictionary limits policy source first).mapError (atPage 0 first)
    checkDataOffset column rest
    let planned ← (rest.zipIdx 1).mapM fun (frame, ordinal) =>
      (dataParameters leaf frame.value).map (fun params => (frame, ordinal, params))
        |>.mapError (atPage ordinal frame)
    let count := (planned.map (fun (_, _, params) => params.numValues)).sum
    checkSlotCount rowCount count
    let pages ← planned.mapM fun (frame, ordinal, params) =>
      (decodeData limits dictionary params (frameBody source frame)).mapError (atPage ordinal frame)
    return pages.flatten

end Silmaril.Formats.Parquet.Int96.Dictionary
