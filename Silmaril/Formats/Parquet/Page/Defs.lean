module

public import Silmaril.Formats.Parquet.Page.Header.Defs
public import Silmaril.Formats.Parquet.Footer.Validation.Defs

/-! Bounded page framing over the bytes of an in-file plaintext column chunk. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Page

/-- Absolute offsets in the source snapshot. The compressed payload follows its header. -/
structure Frame where
  value : Header
  header : Footer.Span
  payload : Footer.Span
  deriving Repr, DecidableEq

structure Limits where
  maxHeaderBytes : Nat := 65536
  maxPages : Nat := 65536
  header : HeaderLimits := {}

inductive Error where
  | chunkBounds
  | cursorBounds
  | header (error : HeaderError)
  | payloadBounds
  | pageLimit
  deriving Repr, DecidableEq

/-- Compute the page region of a local column from a checked footer start. -/
def columnSpan (footerStart : Nat) (column : Footer.ColumnMetadata) : Option Footer.Span :=
  Footer.checkDataSpan footerStart (column.dictionaryPageOffset.getD column.dataPageOffset)
    column.totalCompressedSize

/-- The bounded lookahead window ends inside the declared chunk. -/
def headerWindowStop (limits : Limits) (chunk : Footer.Span) (cursor : Nat) : Nat :=
  min chunk.stop (cursor + limits.maxHeaderBytes)

/-- Read one header at a checked absolute cursor and bound its advertised payload.
No payload buffer is allocated. The cursor for the next page is `frame.payload.stop`. -/
def readPage (limits : Limits) (source : Bytes) (chunk : Footer.Span) (cursor : Nat) :
    Except Error Frame := do
  if ¬ (chunk.start ≤ cursor ∧ cursor < chunk.stop ∧ chunk.stop ≤ source.length) then
    throw .cursorBounds
  let window := Footer.fileBytes source cursor (headerWindowStop limits chunk cursor)
  let (value, consumed) ← (readHeaderPrefix limits.header window).mapError .header
  let payloadStart := cursor + consumed
  let payloadStop := payloadStart + value.compressedSize
  if chunk.stop < payloadStop then throw .payloadBounds
  pure ⟨value, ⟨cursor, payloadStart⟩, ⟨payloadStart, payloadStop⟩⟩

/-- Scan exactly the declared chunk, including skipped pages, in wire order. -/
def readChunk (limits : Limits) (source : Bytes) (chunk : Footer.Span) :
    Except Error (List Frame) :=
  if chunk.start ≤ chunk.stop ∧ chunk.stop ≤ source.length then
    go limits.maxPages chunk.start []
  else .error .chunkBounds
where
  go (budget cursor : Nat) (reversed : List Frame) : Except Error (List Frame) :=
    if cursor = chunk.stop then .ok reversed.reverse else
      match budget with
      | 0 => .error .pageLimit
      | budget + 1 =>
        match readPage limits source chunk cursor with
        | .error e => .error e
        | .ok frame => go budget frame.payload.stop (frame :: reversed)

/-- The header and payload of a frame are adjacent, with the advertised byte count. -/
structure FrameWithin (chunk : Footer.Span) (cursor : Nat) (frame : Frame) : Prop where
  chunkStart : chunk.start ≤ cursor
  headerStart : frame.header.start = cursor
  headerProgress : cursor < frame.header.stop
  adjacent : frame.header.stop = frame.payload.start
  payloadWidth : frame.payload.stop = frame.payload.start + frame.value.compressedSize
  chunkStop : frame.payload.stop ≤ chunk.stop

/-- A contiguous chain from the initial cursor to the final cursor. -/
inductive Chain (chunk : Footer.Span) : Nat → Nat → List Frame → Prop where
  | nil (cursor : Nat) : Chain chunk cursor cursor []
  | cons {start stop : Nat} {frame : Frame} {rest : List Frame}
      (within : FrameWithin chunk start frame)
      (next : Chain chunk frame.payload.stop stop rest) : Chain chunk start stop (frame :: rest)

/-- Absolute V2 payload spans in wire order. `levels` supplies lengths from the
same frame's data-page header and addresses the compressed on-disk value section. -/
structure V2Spans where
  repetition : Footer.Span
  definition : Footer.Span
  values : Footer.Span
  deriving Repr, DecidableEq

/-- Obtain V2 repetition, definition and value spans. The guard also applies
when callers construct a `Frame` themselves. -/
def Frame.v2Spans (frame : Frame) : Option V2Spans := do
  let .dataV2 levels := frame.value.kind | none
  let definition := frame.payload.start + levels.repetitionBytes
  let values := definition + levels.definitionBytes
  if values ≤ frame.payload.stop then
    some ⟨⟨frame.payload.start, definition⟩, ⟨definition, values⟩, ⟨values, frame.payload.stop⟩⟩
  else none

end Silmaril.Formats.Parquet.Page
