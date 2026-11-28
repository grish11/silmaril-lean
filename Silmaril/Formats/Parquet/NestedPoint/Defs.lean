module

public import Silmaril.Formats.Parquet.NestedPresence.Defs
public import Silmaril.Formats.Parquet.Page.Defs
public import Silmaril.Formats.Parquet.Plain.Defs

/-! Same-snapshot V1 reads for one optional struct with a required INT32
and an optional INT64 leaf, one data page per chunk. -/

public section

namespace Silmaril.Formats.Parquet.NestedPoint

open NestedPresence (Child Presence Result)

structure Limits where
  footer : Footer.Limits := {}
  framing : Page.Limits := {}
  presence : NestedPresence.Limits := {}

inductive LeafError where
  | metadata (cause : Footer.NestedLeaf.Error)
  | profile
  | codec (actual : Int)
  | unsupportedOffsets
  | chunkBounds
  | framing (cause : Page.Error)
  | pageCount
  | bodyLimit
  | payloadBounds
  | presence (cause : NestedPresence.Error)
  | rowCount
  deriving DecidableEq, Repr

/-- Resolve the original leaf, row group, chunk, and singleton page before
passing its exact body slice to the checked presence decoder. -/
def readLeaf (limits : Limits) (snapshot : Snapshot.Checked) (group column : Nat)
    (child : Child) (physical : Footer.PhysicalType) : Except LeafError Result := do
  let leaf ← (Footer.NestedLeaf.select limits.footer snapshot column).mapError .metadata
  if ¬ (NestedPresence.childOf leaf = some child ∧ leaf.physical = physical) then
    return ← throw .profile
  let (selected, chunk) ← (Footer.NestedLeaf.selectChunk leaf group).mapError .metadata
  let metadata := chunk.metadata
  if metadata.codec ≠ 0 then return ← throw (.codec metadata.codec)
  if metadata.dictionaryPageOffset.isSome || metadata.indexPageOffset.isSome then
    return ← throw .unsupportedOffsets
  let some span := Page.columnSpan snapshot.footer.start metadata | throw .chunkBounds
  let [frame] ← (Page.readChunk limits.framing snapshot.bytes span).mapError .framing | throw .pageCount
  if limits.presence.maxBodyBytes < frame.value.compressedSize then return ← throw .bodyLimit
  let some body := snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) | throw .payloadBounds
  let result ← (NestedPresence.decodeV1 child limits.presence frame.value body).mapError .presence
  if ¬ (selected.numRows = (result.states.length : Int) ∧ metadata.numValues = selected.numRows) then
    return ← throw .rowCount
  pure result

structure LeafWire (limits : Limits) (snapshot : Snapshot.Checked) (group column : Nat)
    (child : Child) (physical : Footer.PhysicalType) (result : Result) : Prop where
  source : ∃ leaf selected chunk span frame body,
    Footer.NestedLeaf.select limits.footer snapshot column = .ok leaf ∧
    Footer.NestedLeaf.Wire limits.footer column leaf ∧
    NestedPresence.childOf leaf = some child ∧ leaf.physical = physical ∧
    snapshot.groupAt group = some selected ∧ selected.columns[column]? = some chunk ∧
    chunk.metadata.pathInSchema = leaf.path ∧ chunk.metadata.physicalType = physical ∧
    chunk.metadata.codec = 0 ∧ chunk.metadata.dictionaryPageOffset = none ∧ chunk.metadata.indexPageOffset = none ∧
    Page.columnSpan snapshot.footer.start chunk.metadata = some span ∧
    Page.readChunk limits.framing snapshot.bytes span = .ok [frame] ∧
    Page.Chain span span.start span.stop [frame] ∧
    snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some body ∧
    NestedPresence.PageWire child limits.presence frame.value body result ∧
    selected.numRows = (result.states.length : Int) ∧ chunk.metadata.numValues = selected.numRows

abbrev Row := Option (Int32 × Option Int64)

inductive Error where
  | leaf (column : Nat) (cause : LeafError)
  | plain (column : Nat) (cause : Plain.Error)
  | reconstruct (column : Nat) (cause : FlatPage.Error)
  | parentPresence
  deriving DecidableEq, Repr

@[expose] def valueMask (result : Result) : List Bool :=
  result.states.map Presence.valuePresent

@[expose] def parentMask (result : Result) : List Bool :=
  result.states.map (· != .parentAbsent)

@[expose] def pairSlots (left : List (Option Int32)) (right : List (Option Int64)) : List Row :=
  List.zipWith (fun lhs rhs => lhs.map (·, rhs)) left right

/-- The two streams have one slot per row and must agree on parent validity.
If the left stream is from the required child, its value mask is exactly
its parent mask. Decode each PLAIN suffix at the count of its value states. -/
def assemble (left right : Result) : Except Error (List Row) := do
  let leftMask := valueMask left
  let rightMask := valueMask right
  if leftMask ≠ parentMask right then return ← throw .parentPresence
  let ints ← (Plain.decodeInt32 (leftMask.count true) left.scalars).mapError (.plain 0)
  let longs ← (Plain.decodeInt64 (rightMask.count true) right.scalars).mapError (.plain 1)
  let lhs ← (FlatPage.reconstruct leftMask ints).mapError (.reconstruct 0)
  let rhs ← (FlatPage.reconstruct rightMask longs).mapError (.reconstruct 1)
  pure (pairSlots lhs rhs)

def read (limits : Limits) (snapshot : Snapshot.Checked) (group : Nat) : Except Error (List Row) := do
  let left ← (readLeaf limits snapshot group 0 .required .int32).mapError (.leaf 0)
  let right ← (readLeaf limits snapshot group 1 .optional .int64).mapError (.leaf 1)
  assemble left right

structure AssemblyWire (left right : Result) (rows : List Row) : Prop where
  parents : valueMask left = parentMask right
  count : rows.length = left.states.length
  data : ∃ ints longs lhs rhs,
    Plain.decodeInt32 ((valueMask left).count true) left.scalars = .ok ints ∧
    Plain.decodeInt64 ((valueMask right).count true) right.scalars = .ok longs ∧
    lhs.map Option.isSome = valueMask left ∧ lhs.filterMap id = ints ∧
    rhs.map Option.isSome = valueMask right ∧ rhs.filterMap id = longs ∧
    rows = pairSlots lhs rhs

end Silmaril.Formats.Parquet.NestedPoint
