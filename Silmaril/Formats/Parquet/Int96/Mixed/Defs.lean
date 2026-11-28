module

public import Silmaril.Formats.Parquet.Int96.Dictionary.Defs

/-! One bounded INT96 chunk with a leading dictionary and PLAIN or
RLE_DICTIONARY data frames. -/

public section

namespace Silmaril.Formats.Parquet.Int96.Mixed

inductive Encoding where
  | plain
  | dictionary
  deriving DecidableEq, Repr

inductive PageError where
  | misplacedDictionary
  | dataOffset
  | sizeMismatch
  | header (cause : Int96.Page.Error)
  | encoding (actual : Int)
  | plain (cause : Int96.Page.Error)
  | dictionary (cause : Dictionary.PageError)
  deriving DecidableEq, Repr

inductive Cause where
  | locate (cause : Dictionary.Cause)
  | framing (cause : Parquet.Page.Error)
  | missingDictionary
  | missingData
  | slotCount (expected actual : Nat)
  | page (ordinal headerOffset : Nat) (cause : PageError)
  deriving DecidableEq, Repr

structure Error where
  chunkOffset : Int
  cause : Cause
  deriving DecidableEq, Repr

/-- A header-admitted data frame and its original chunk ordinal. -/
structure DataPage where
  private mk ::
  frame : Parquet.Page.Frame
  ordinal : Nat
  params : ScalarPage.Parameters
  encoding : Encoding

/-- Admit a data frame using its original header. The dictionary frame has
already been removed from the data sequence. -/
def planData (leaf : Footer.SchemaElement) (frame : Parquet.Page.Frame) (ordinal : Nat) :
    Except PageError DataPage :=
  match frame.value.kind with
  | .dictionary _ => .error .misplacedDictionary
  | _ =>
    if frame.value.compressedSize ≠ frame.value.uncompressedSize then .error .sizeMismatch
    else do
      let params ← (Int96.Page.parameters leaf 0 frame.value).mapError .header
      if params.encoding = 0 then .ok ⟨frame, ordinal, params, .plain⟩
      else if params.encoding = 8 then .ok ⟨frame, ordinal, params, .dictionary⟩
      else .error (.encoding params.encoding)

/-- Dispatch the admitted tag once. Either branch returns its original
decoder error, with no retry under a different encoding. -/
def decodePage (limits : Dictionary.Limits) (policy : Policy) (source : Bytes)
    (leaf : Footer.SchemaElement) (dictionary : Array (Int96.Page.Value policy))
    (page : DataPage) : Except Cause (Dictionary.Slots policy) :=
  let body := Dictionary.frameBody source page.frame
  let atFrame := Cause.page page.ordinal page.frame.header.start
  match page.encoding with
  | .plain =>
    (Int96.Page.decode policy leaf 0 page.frame.value limits.scalar body).mapError (atFrame ∘ .plain)
  | .dictionary =>
    (Dictionary.decodeData limits dictionary page.params body).mapError (atFrame ∘ .dictionary)

/-- A data frame denotes the ordered slots of the branch selected by its
checked header. The branch reads the original payload slice. -/
def DataWire (limits : Dictionary.Limits) {policy : Policy} (source : Bytes)
    (leaf : Footer.SchemaElement) (dictionary : Array (Int96.Page.Value policy))
    (frame : Parquet.Page.Frame) (slots : Dictionary.Slots policy) : Prop :=
  ∃ params, Int96.Page.parameters leaf 0 frame.value = .ok params ∧
    slots.length = params.numValues ∧
    ((params.encoding = 0 ∧
        Int96.Page.decode policy leaf 0 frame.value limits.scalar (Dictionary.frameBody source frame) = .ok slots) ∨
      (params.encoding = 8 ∧
        Dictionary.decodeData limits dictionary params (Dictionary.frameBody source frame) = .ok slots))

private def plan (leaf : Footer.SchemaElement) (frames : List Parquet.Page.Frame) :
    Except Cause (List DataPage) :=
  (frames.zipIdx 1).mapM fun (frame, ordinal) =>
    (planData leaf frame ordinal).mapError (.page ordinal frame.header.start)

/-- Check one chunk from the supplied bytes. The sole dictionary is the
leading PLAIN frame, and every data frame selects its own encoding. -/
def read (limits : Dictionary.Limits) (policy : Policy) (source : Bytes) (footerStart rowCount : Nat)
    (leaf : Footer.SchemaElement) (column : Footer.ColumnMetadata) :
    Except Error (Dictionary.Slots policy) :=
  readChunk.mapError (Error.mk (column.dictionaryPageOffset.getD column.dataPageOffset))
where
  readChunk : Except Cause (Dictionary.Slots policy) := do
    let span ← (Dictionary.locate limits footerStart rowCount leaf column).mapError .locate
    let frames ← (Parquet.Page.readChunk limits.framing source span).mapError .framing
    let first :: rest := frames | Except.error .missingDictionary
    let dictionary ← (Dictionary.readDictionary limits policy source first).mapError
      (.page 0 first.header.start ∘ .dictionary)
    match rest with
    | [] => .error .missingData
    | data :: _ =>
      if (data.header.start : Int) ≠ column.dataPageOffset then
        .error (.page 1 data.header.start .dataOffset)
      else do
        let planned ← plan leaf rest
        let count := (planned.map (·.params.numValues)).sum
        if count ≠ rowCount then .error (.slotCount rowCount count)
        else do
          let pages ← planned.mapM (decodePage limits policy source leaf dictionary)
          return pages.flatten

end Silmaril.Formats.Parquet.Int96.Mixed
