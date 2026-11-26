module

public import Silmaril.Formats.Parquet.FlatPage.Defs
public import Silmaril.Formats.Parquet.Footer.NestedLeaf.Defs
public import Silmaril.Formats.Parquet.Page.Header.Defs

/-! Definition levels for a leaf of one optional, unannotated two-leaf struct. -/

public section

namespace Silmaril.Formats.Parquet.NestedPresence

inductive Child where
  | required
  | optional
  deriving DecidableEq, Repr

/-- Derive the profile from a leaf selected by the checked nested footer. -/
def childOf {snapshot : Snapshot.Checked} (selection : Footer.NestedLeaf.Selection snapshot) : Option Child :=
  match selection.leaf.repetition with
  | some .required => some .required
  | some .optional => some .optional
  | _ => none

@[expose] def Child.maxDefinition : Child → Nat
  | .required => 1
  | .optional => 2

/-- The profile's maximum definition levels 1 and 2 need one and two bits. -/
abbrev Child.width (child : Child) : Nat := child.maxDefinition

inductive Presence where
  | parentAbsent
  | childNull
  | value
  deriving DecidableEq, Repr

/-- Executable map used only after the level is checked against maxDefinition. -/
@[expose] def classify (child : Child) (level : Nat) : Presence :=
  if level = 0 then .parentAbsent
  else if level = child.maxDefinition then .value
  else .childNull

@[expose] def Presence.valuePresent : Presence → Bool
  | .value => true
  | _ => false

structure Limits where
  maxBodyBytes : Nat := 16 * 1024 * 1024
  levels : Hybrid.Limits := ⟨1024 * 1024, 16 * 1024 * 1024⟩

inductive Error where
  | pageKind
  | crc
  | encoding
  | bodySize
  | bodyLimit
  | section (cause : FlatPage.Error)
  | hybrid (cause : Hybrid.Error)
  | definitionLevel
  deriving DecidableEq, Repr

structure Result where
  states : List Presence
  scalars : Bytes
  deriving DecidableEq

/-- For this zero-repetition profile, the uncompressed V1 body starts with
a length-prefixed definition section. Preserve the complete scalar suffix. -/
def decode (child : Child) (slots : Nat) (limits : Limits) (body : Bytes) : Except Error Result := do
  if limits.maxBodyBytes < body.length then return ← throw .bodyLimit
  let sections ← (FlatPage.splitV1Optional limits.levels.bytes body).mapError .section
  let levels ← (Hybrid.decode child.width slots limits.levels sections.definitions).mapError .hybrid
  if !levels.all (fun level => decide (level ≤ child.maxDefinition)) then return ← throw .definitionLevel
  pure ⟨levels.map (classify child), sections.scalars⟩

/-- A page-local contract for caller-paired, uncompressed CRC-free V1 PLAIN
bodies. The column codec must already be known to be UNCOMPRESSED. -/
def decodeV1 (child : Child) (limits : Limits) (header : Page.Header) (body : Bytes) :
    Except Error Result := do
  let .dataV1 info := header.kind | throw .pageKind
  if header.crc.isSome then return ← throw .crc
  if ¬ (info.encoding = 0 ∧ info.definitionLevelEncoding = 3 ∧ info.repetitionLevelEncoding = 3) then
    return ← throw .encoding
  if ¬ (header.compressedSize = body.length ∧ header.uncompressedSize = body.length) then
    return ← throw .bodySize
  decode child info.numValues limits body

structure Wire (child : Child) (slots : Nat) (limits : Limits) (body : Bytes) (result : Result) : Prop where
  bodyCap : body.length ≤ limits.maxBodyBytes
  slotCount : result.states.length = slots
  definitions : ∃ (word : List UInt8) (definitions : Bytes) (levels : List Nat),
    word.length = 4 ∧ KBytes.leVal word = definitions.length ∧ definitions.length ≤ limits.levels.bytes ∧
    body.toList = word ++ definitions.toList ++ result.scalars.toList ∧
    Hybrid.Wire child.width slots definitions.toList levels ∧
    (∀ level ∈ levels, level ≤ child.maxDefinition) ∧
    result.states = levels.map (classify child)

structure PageWire (child : Child) (limits : Limits) (header : Page.Header) (body : Bytes)
    (result : Result) : Prop where
  crc : header.crc = none
  compressedSize : header.compressedSize = body.length
  uncompressedSize : header.uncompressedSize = body.length
  page : ∃ info, header.kind = .dataV1 info ∧ info.encoding = 0 ∧ info.definitionLevelEncoding = 3 ∧
    info.repetitionLevelEncoding = 3 ∧ Wire child info.numValues limits body result

end Silmaril.Formats.Parquet.NestedPresence
