module

public import Silmaril.Formats.Parquet.NestedPoint.Defs

/-! Bounded sibling alignment by row position, with independent V1 page cuts. -/

public section

namespace Silmaril.Formats.Parquet.NestedPoint.Multi

open NestedPresence (Child Presence Result)

structure Limits where
  leaf : NestedPoint.Limits := {}
  maxChunkBytes : Nat := 64 * 1024 * 1024
  maxRows : Nat := 1024 * 1024

inductive Kind where
  | signed
  | wide

abbrev Kind.Value : Kind → Type
  | .signed => Int32
  | .wide => Int64

@[expose] def Kind.column : Kind → Nat
  | .signed => 0
  | .wide => 1

@[expose] def Kind.child : Kind → Child
  | .signed => .required
  | .wide => .optional

@[expose] def Kind.physical : Kind → Footer.PhysicalType
  | .signed => .int32
  | .wide => .int64

@[expose] def Kind.decodePlain : (kind : Kind) → Nat → Bytes → Except Plain.Error (List kind.Value)
  | .signed => Plain.decodeInt32
  | .wide => Plain.decodeInt64

inductive PageError where
  | bodyLimit
  | payloadBounds
  | presence (cause : NestedPresence.Error)
  | plain (cause : Plain.Error)
  | reconstruct (cause : FlatPage.Error)
  deriving DecidableEq, Repr

inductive ColumnError where
  | metadata (cause : Footer.NestedLeaf.Error)
  | profile
  | codec (actual : Int)
  | unsupportedOffsets
  | chunkBounds
  | chunkLimit
  | rowLimit
  | rowCount (expected actual : Int)
  | framing (cause : Page.Error)
  | page (headerOffset : Nat) (cause : PageError)
  deriving DecidableEq, Repr

inductive Error where
  | column (ordinal : Nat) (cause : ColumnError)
  | parentPresence
  deriving DecidableEq, Repr

structure Decoded (α : Type) where
  states : List Presence
  slots : List (Option α)

@[expose] def frameSlots (frame : Page.Frame) : Nat :=
  match frame.value.kind with
  | .dataV1 info => info.numValues
  | _ => 0

/-- The enclosing column reader has already admitted the codec and
obtained the frame from the immutable source. -/
def decodeFrame (kind : Kind) (limits : NestedPresence.Limits) (source : Bytes) (frame : Page.Frame) :
    Except PageError (Decoded kind.Value) := do
  if limits.maxBodyBytes < frame.value.compressedSize then return ← throw .bodyLimit
  let some body := source.slice? frame.payload.start (some frame.payload.stop) | throw .payloadBounds
  let decoded ← (NestedPresence.decodeV1 kind.child limits frame.value body).mapError .presence
  let mask := valueMask decoded
  let values ← (kind.decodePlain (mask.count true) decoded.scalars).mapError .plain
  let slots ← (FlatPage.reconstruct mask values).mapError .reconstruct
  pure ⟨decoded.states, slots⟩

private def decodeColumnFrame (kind : Kind) (limits : NestedPresence.Limits)
    (source : Bytes) (frame : Page.Frame) : Except ColumnError (Decoded kind.Value) :=
  (decodeFrame kind limits source frame).mapError (.page frame.header.start)

@[expose] def concatenate {α : Type} (pages : List (Decoded α)) : Decoded α :=
  ⟨pages.flatMap Decoded.states, pages.flatMap Decoded.slots⟩

/-- Walk one selected chunk in its own frame order. Check total advertised
slots before decoding values or allocating row lists. -/
def readColumn (kind : Kind) (limits : Limits) (snapshot : Snapshot.Checked) (group : Nat) :
    Except ColumnError (Decoded kind.Value) := do
  let selected ← (Footer.NestedLeaf.select limits.leaf.footer snapshot kind.column).mapError .metadata
  if ¬ (NestedPresence.childOf selected = some kind.child ∧ selected.physical = kind.physical) then
    return ← throw .profile
  let (rowGroup, chunk) ← (Footer.NestedLeaf.selectChunk selected group).mapError .metadata
  let metadata := chunk.metadata
  if metadata.codec ≠ 0 then return ← throw (.codec metadata.codec)
  if metadata.dictionaryPageOffset.isSome || metadata.indexPageOffset.isSome then
    return ← throw .unsupportedOffsets
  if limits.maxRows < rowGroup.numRows.toNat then return ← throw .rowLimit
  if metadata.numValues ≠ rowGroup.numRows then return ← throw (.rowCount rowGroup.numRows metadata.numValues)
  let some span := Page.columnSpan snapshot.footer.start metadata | throw .chunkBounds
  if limits.maxChunkBytes < span.stop - span.start then return ← throw .chunkLimit
  let frames ← (Page.readChunk limits.leaf.framing snapshot.bytes span).mapError .framing
  let declared := (frames.map frameSlots).sum
  if (declared : Int) ≠ rowGroup.numRows then return ← throw (.rowCount rowGroup.numRows declared)
  let pages ← frames.mapM (decodeColumnFrame kind limits.leaf.presence snapshot.bytes)
  pure (concatenate pages)

@[expose] def parentMask (states : List Presence) : List Bool :=
  states.map (· != .parentAbsent)

private def pair (left : Decoded Int32) (right : Decoded Int64) : Except Error (List Row) :=
  if parentMask left.states = parentMask right.states then
    .ok (pairSlots left.slots right.slots)
  else .error .parentPresence

/-- Align the concatenated row streams after both columns have been
checked. The two columns can have different page cuts and page counts. -/
def read (limits : Limits) (snapshot : Snapshot.Checked) (group : Nat) : Except Error (List Row) := do
  let left ← (readColumn .signed limits snapshot group).mapError (.column 0)
  let right ← (readColumn .wide limits snapshot group).mapError (.column 1)
  pair left right

structure FrameWire (kind : Kind) (limits : NestedPresence.Limits) (source : Bytes) (frame : Page.Frame)
    (result : Decoded kind.Value) : Prop where
  slotCount : result.slots.length = frameSlots frame
  stateCount : result.states.length = frameSlots frame
  wire : ∃ body decoded values,
    source.slice? frame.payload.start (some frame.payload.stop) = some body ∧
    NestedPresence.PageWire kind.child limits frame.value body decoded ∧
    result.states = decoded.states ∧
    kind.decodePlain ((valueMask decoded).count true) decoded.scalars = .ok values ∧
    result.slots.map Option.isSome = valueMask decoded ∧ result.slots.filterMap id = values

structure ColumnWire (kind : Kind) (limits : Limits) (snapshot : Snapshot.Checked) (group : Nat)
    (result : Decoded kind.Value) : Prop where
  source : ∃ (selected : Footer.NestedLeaf.Selection snapshot), ∃ rowGroup chunk span frames pages,
    Footer.NestedLeaf.Wire limits.leaf.footer kind.column selected ∧
    NestedPresence.childOf selected = some kind.child ∧ selected.physical = kind.physical ∧
    snapshot.groupAt group = some rowGroup ∧ rowGroup.columns[kind.column]? = some chunk ∧
    chunk.metadata.pathInSchema = selected.path ∧ chunk.metadata.physicalType = kind.physical ∧
    chunk.metadata.codec = 0 ∧ chunk.metadata.numValues = rowGroup.numRows ∧
    Page.columnSpan snapshot.footer.start chunk.metadata = some span ∧
    Page.readChunk limits.leaf.framing snapshot.bytes span = .ok frames ∧
    Page.Chain span span.start span.stop frames ∧
    List.Forall₂ (FrameWire kind limits.leaf.presence snapshot.bytes) frames pages ∧
    result = concatenate pages ∧ result.states.length = rowGroup.numRows.toNat ∧
    result.slots.length = rowGroup.numRows.toNat

structure Wire (limits : Limits) (snapshot : Snapshot.Checked) (group : Nat)
    (rows : List Row) : Prop where
  aligned : ∃ lhs rhs,
    ColumnWire .signed limits snapshot group lhs ∧ ColumnWire .wide limits snapshot group rhs ∧
    parentMask lhs.states = parentMask rhs.states ∧ rows = pairSlots lhs.slots rhs.slots
  count : ∃ rowGroup, snapshot.groupAt group = some rowGroup ∧ rows.length = rowGroup.numRows.toNat

end Silmaril.Formats.Parquet.NestedPoint.Multi
