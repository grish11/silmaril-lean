module

public import Silmaril.Formats.Parquet.Hybrid.Defs

/-! Checked definition sections and nullable slot reconstruction for flat scalar pages.
The caller supplies the schema levels, exact body or slices, and value counts. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.FlatPage

inductive Layout where
  | required
  | optional
  deriving DecidableEq, Repr

structure LevelSchema where
  maxRepetition : Nat
  maxDefinition : Nat
  deriving DecidableEq, Repr

def LevelSchema.layout? (schema : LevelSchema) : Option Layout :=
  if schema.maxRepetition = 0 then
    match schema.maxDefinition with
    | 0 => some .required
    | 1 => some .optional
    | _ => none
  else none

/-- V1 carries the decompressed body. V2 carries separate, already bounded
definition and scalar slices, with the two advertised level lengths. -/
inductive Body where
  | v1 (source : Bytes)
  | v2 (repetitionBytes definitionBytes : Nat) (definitions scalars : Bytes)

inductive Error where
  | unsupportedLevels
  | unexpectedRepetitionSection
  | unexpectedDefinitionSection
  | countLimit
  | definitionByteLimit
  | truncatedDefinitionLength
  | truncatedDefinitions
  | invalidDefinitionLength
  | hybrid (error : Hybrid.Error)
  | presentCountMismatch
  | scalarCountMismatch
  deriving DecidableEq, Repr

structure Sections where
  definitions : Bytes
  scalars : Bytes
  deriving DecidableEq

/-- Read the V1 unsigned four-octet length and split exactly at its boundary. -/
def splitV1Optional (byteLimit : Nat) (source : Bytes) : Except Error Sections :=
  if source.length < 4 then .error .truncatedDefinitionLength
  else
    let bytes := source.toList
    let size := KBytes.leVal (bytes.take 4)
    if byteLimit < size then .error .definitionByteLimit
    else if source.length < 4 + size then .error .truncatedDefinitions
    else
      let tail := bytes.drop 4
      .ok ⟨Bytes.ofList (tail.take size), Bytes.ofList (tail.drop size)⟩

def split (layout : Layout) (byteLimit : Nat) : Body → Except Error Sections
  | .v1 source =>
    match layout with
    | .required => .ok ⟨.empty, source⟩
    | .optional => splitV1Optional byteLimit source
  | .v2 repetitionBytes definitionBytes definitions scalars =>
    if repetitionBytes ≠ 0 then .error .unexpectedRepetitionSection
    else if definitionBytes ≠ definitions.length ∨ Hybrid.runLimit ≤ definitionBytes then
      .error .invalidDefinitionLength
    else if byteLimit < definitionBytes then .error .definitionByteLimit
    else .ok ⟨definitions, scalars⟩

/-- Wire-level interpretation of a bounded definition section. -/
def MaskWire (layout : Layout) (slots : Nat) (definitions : Bytes) (mask : List Bool) : Prop :=
  match layout with
  | .required => definitions = .empty ∧ mask = List.replicate slots true
  | .optional =>
    ∃ levels : List Nat, Hybrid.Wire 1 slots definitions.toList levels ∧
      mask = levels.map (· == 1)

/-- Every flat row has one output slot. Optional pages use width-one hybrid
definition levels, where 1 means that a scalar is present. -/
def readMask (layout : Layout) (slots : Nat) (limits : Hybrid.Limits)
    (definitions : Bytes) : Except Error (List Bool) :=
  if Hybrid.runLimit ≤ slots ∨ limits.values < slots then .error .countLimit
  else if limits.bytes < definitions.length then .error .definitionByteLimit
  else
    match layout with
    | .required =>
      if definitions.length = 0 then .ok (List.replicate slots true)
      else .error .unexpectedDefinitionSection
    | .optional =>
      match Hybrid.decode 1 slots limits definitions with
      | .error error => .error (.hybrid error)
      | .ok levels => .ok (levels.map (· == 1))

structure Plan where
  mask : List Bool
  scalars : Bytes
  deriving DecidableEq

/-- Separate levels from values and validate the declared present count before
invoking any physical scalar reader. -/
def plan (schema : LevelSchema) (slots present : Nat) (limits : Hybrid.Limits)
    (body : Body) : Except Error Plan := do
  let some layout := schema.layout? | throw .unsupportedLevels
  if slots < present then throw .presentCountMismatch
  else
    let sections ← split layout limits.bytes body
    let mask ← readMask layout slots limits sections.definitions
    if mask.count true = present then pure ⟨mask, sections.scalars⟩
    else throw .presentCountMismatch

/-- Consume one scalar for each present slot, keeping both sequences in order. -/
def reconstructLoop {α : Type} :
    List Bool → List α → List (Option α) → Except Error (List (Option α))
  | [], [], acc => .ok acc.reverse
  | [], _ :: _, _ => .error .scalarCountMismatch
  | false :: mask, values, acc => reconstructLoop mask values (none :: acc)
  | true :: _, [], _ => .error .scalarCountMismatch
  | true :: mask, value :: values, acc => reconstructLoop mask values (some value :: acc)

def reconstruct {α : Type} (mask : List Bool) (values : List α) : Except Error (List (Option α)) :=
  reconstructLoop mask values []

inductive DecodeError (ε : Type) where
  | page (error : Error)
  | scalar (error : ε)
  deriving DecidableEq, Repr

/-- The physical decoder receives the exact scalar slice and requested present
count. Its own contract governs scalar byte consumption. This layer checks
that its returned list fills exactly the present slots. -/
def decode {α ε : Type} (schema : LevelSchema) (slots present : Nat) (limits : Hybrid.Limits)
    (body : Body) (scalar : Nat → Bytes → Except ε (List α)) :
    Except (DecodeError ε) (List (Option α)) :=
  match plan schema slots present limits body with
  | .error error => .error (.page error)
  | .ok checked =>
    match scalar present checked.scalars with
    | .error error => .error (.scalar error)
    | .ok values =>
      match reconstruct checked.mask values with
      | .error error => .error (.page error)
      | .ok output => .ok output

end Silmaril.Formats.Parquet.FlatPage
