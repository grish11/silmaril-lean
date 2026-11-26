module

public import Silmaril.Formats.Parquet.FlatPage.Defs
public import Silmaril.Formats.Parquet.Page.Header.Defs
public import Silmaril.Formats.Parquet.Plain.Defs

/-! One complete V1 page for the canonical nullable LIST of nullable INT32. -/

public section

namespace Silmaril.Formats.Parquet.ListPage

abbrev Row := Option (List (Option Int32))

inductive Event where
  | nullList
  | emptyList
  | first (item : Option Int32)
  | next (item : Option Int32)
  deriving DecidableEq, Repr

@[expose] def Event.wire : Event → Nat × Nat × Option Int32
  | .nullList => (0, 0, none)
  | .emptyList => (0, 1, none)
  | .first item => (0, if item.isSome then 3 else 2, item)
  | .next item => (1, if item.isSome then 3 else 2, item)

inductive Error where
  | codec (actual : Int)
  | pageKind
  | crc
  | encoding
  | bodySize
  | bodyLimit
  | rowLimit
  | repetitionSection (cause : FlatPage.Error)
  | definitionSection (cause : FlatPage.Error)
  | repetition (cause : Hybrid.Error)
  | definition (cause : Hybrid.Error)
  | plain (cause : Plain.Error)
  | reconstruct (cause : FlatPage.Error)
  | levelPair
  | continuationWithoutList
  | rowCount (expected actual : Nat)
  deriving DecidableEq, Repr

private def eventFor (entry : Nat × Nat × Option Int32) : Event :=
  let (rep, defn, item) := entry
  if rep = 0 then
    if defn = 0 then Event.nullList else if defn = 1 then .emptyList else .first item
  else .next item

def readEvent (entry : Nat × Nat × Option Int32) : Except Error Event :=
  let event := eventFor entry
  if event.wire = entry then .ok event else .error .levelPair

@[expose] def rowEvents : Row → List Event
  | none => [.nullList]
  | some [] => [.emptyList]
  | some (item :: rest) => .first item :: rest.map Event.next

private abbrev OpenList := Option Int32 × List (Option Int32)

private def flush (active : Option OpenList) (closed : List Row) : List Row :=
  match active with
  | none => closed
  | some (item, reverseTail) => some (item :: reverseTail.reverse) :: closed

/-- A continuation can extend only an open nonempty list. Starts close
the previous row. The page starts with no open list. -/
def reconstruct (events : List Event) : Except Error (List Row) := go events none []
where
  go (events : List Event) (active : Option OpenList) (closed : List Row) : Except Error (List Row) :=
    match events with
    | [] => .ok (flush active closed).reverse
    | .nullList :: rest => go rest none (none :: flush active closed)
    | .emptyList :: rest => go rest none (some [] :: flush active closed)
    | .first item :: rest => go rest (some (item, [])) (flush active closed)
    | .next item :: rest =>
      match active with
      | none => .error .continuationWithoutList
      | some (head, reverseTail) => go rest (some (head, item :: reverseTail)) closed

structure Limits where
  maxBodyBytes : Nat := 16 * 1024 * 1024
  maxRows : Nat := 1024 * 1024
  levels : Hybrid.Limits := ⟨1024 * 1024, 16 * 1024 * 1024⟩

@[expose] def valueMask (definitions : List Nat) : List Bool :=
  definitions.map (· == 3)

/-- Both level streams are exact V1 length-prefixed sections. The remaining
bytes are exactly the PLAIN INT32 words for definition level 3. -/
def decodeBody (limits : Limits) (expectedRows slots : Nat) (body : Bytes) :
    Except Error (List Row) := do
  if limits.maxBodyBytes < body.length then return ← throw .bodyLimit
  if limits.maxRows < expectedRows then return ← throw .rowLimit
  let first ← (FlatPage.splitV1Optional limits.levels.bytes body).mapError .repetitionSection
  let second ← (FlatPage.splitV1Optional limits.levels.bytes first.scalars).mapError .definitionSection
  let reps ← (Hybrid.decode 1 slots limits.levels first.definitions).mapError .repetition
  let defs ← (Hybrid.decode 2 slots limits.levels second.definitions).mapError .definition
  let mask := valueMask defs
  let values ← (Plain.decodeInt32 (mask.count true) second.scalars).mapError .plain
  let entries ← (FlatPage.reconstruct mask values).mapError .reconstruct
  let events ← (reps.zip (defs.zip entries)).mapM readEvent
  let rows ← reconstruct events
  if rows.length ≠ expectedRows then return ← throw (.rowCount expectedRows rows.length)
  pure rows

/-- The caller supplies a matching header and body, a checked canonical LIST
schema and the expected number of complete rows. Codec 0 is UNCOMPRESSED.
No carry-in or carry-out partial row is supported. -/
def decodeV1 (limits : Limits) (codec : Int) (header : Page.Header) (expectedRows : Nat)
    (body : Bytes) : Except Error (List Row) := do
  if codec ≠ 0 then return ← throw (.codec codec)
  let .dataV1 info := header.kind | throw .pageKind
  if header.crc.isSome then return ← throw .crc
  if ¬ (info.encoding = 0 ∧ info.repetitionLevelEncoding = 3 ∧ info.definitionLevelEncoding = 3) then
    return ← throw .encoding
  if ¬ (header.compressedSize = body.length ∧ header.uncompressedSize = body.length) then
    return ← throw .bodySize
  decodeBody limits expectedRows info.numValues body

/-- A data stream witnesses both complete level sections, every source
scalar, and a canonical event sequence for exactly the returned rows. -/
structure Wire (limits : Limits) (expectedRows slots : Nat) (body : Bytes) (rows : List Row) : Prop where
  rowCount : rows.length = expectedRows
  caps : body.length ≤ limits.maxBodyBytes ∧ expectedRows ≤ limits.maxRows
  data : ∃ (repLength defLength : List UInt8) (repBytes defBytes scalarBytes : Bytes)
      (reps defs : List Nat) (values : List Int32) (entries : List (Option Int32)),
    repLength.length = 4 ∧ defLength.length = 4 ∧
    KBytes.leVal repLength = repBytes.length ∧ KBytes.leVal defLength = defBytes.length ∧
    body.toList = repLength ++ repBytes.toList ++ defLength ++ defBytes.toList ++ scalarBytes.toList ∧
    Hybrid.Wire 1 slots repBytes.toList reps ∧ Hybrid.Wire 2 slots defBytes.toList defs ∧
    reps.length = slots ∧ defs.length = slots ∧ entries.length = slots ∧
    Plain.decodeInt32 ((valueMask defs).count true) scalarBytes = .ok values ∧
    entries.map Option.isSome = valueMask defs ∧ entries.filterMap id = values ∧
    (rows.flatMap rowEvents).map Event.wire = reps.zip (defs.zip entries)

structure PageWire (limits : Limits) (codec : Int) (header : Page.Header) (expectedRows : Nat)
    (body : Bytes) (rows : List Row) : Prop where
  codec : codec = 0
  crc : header.crc = none
  compressedSize : header.compressedSize = body.length
  uncompressedSize : header.uncompressedSize = body.length
  page : ∃ info, header.kind = .dataV1 info ∧ info.encoding = 0 ∧ info.repetitionLevelEncoding = 3 ∧
    info.definitionLevelEncoding = 3 ∧ Wire limits expectedRows info.numValues body rows

end Silmaril.Formats.Parquet.ListPage
