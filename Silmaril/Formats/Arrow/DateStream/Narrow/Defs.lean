module

public import Silmaril.Formats.Arrow.DateStream.Defs

/-! # Exact Date32 payloads from checked Date64 IPC streams -/

@[expose] public section

namespace Silmaril.Formats.Arrow.DateStream.Narrow

open Silmaril.Numeric.Gregorian (CivilDate)
open Silmaril.Formats.DateInterop

abbrev Column := List (Option Date32.Payload)

structure Stream where
  name : String
  nullable : Bool
  batches : List Column
  deriving DecidableEq, Repr

inductive Error where
  | reader (cause : DateStream.Error)
  | wrongUnit (actual : SchemaReader.DateUnit)
  | invalidCivil (batch slot : Nat)
  | outOfRange (batch slot : Nat) (day : Int)
  deriving DecidableEq, Repr

namespace Internal

def narrowSlot (batch slot : Nat) : Option CivilDate → Except Error (Option Date32.Payload)
  | none => .ok none
  | some date => do
    let some day := date.toEpochDay? | .error (.invalidCivil batch slot)
    let some word := Date32.ofEpochDay? day | .error (.outOfRange batch slot day)
    return some word

def narrowBatch (batch : Nat) (dates : DateValues.Column) : Except Error Column :=
  dates.zipIdx.mapM fun (date, slot) => narrowSlot batch slot date

def narrowBatches (batches : List DateValues.Column) : Except Error (List Column) :=
  batches.zipIdx.mapM fun (dates, batch) => narrowBatch batch dates

end Internal

/-- Admit the complete IPC stream before narrowing. Reader errors therefore
take precedence over unit and range errors. Narrowing visits batches and their
slots from left to right. -/
def read (limits : Limits) (input : KBytes) : Except Error Stream := do
  let source ← (DateStream.read limits input).mapError .reader
  if source.field.unit ≠ .millisecond then .error (.wrongUnit source.field.unit)
  else do
    let batches ← Internal.narrowBatches source.batches
    return ⟨source.field.name, source.field.nullable, batches⟩

/-- Recover the original ordered nullable civil dates from the exact payloads. -/
def civilBatches (stream : Stream) : List DateValues.Column :=
  stream.batches.map (List.map (Option.map Date32.toCivil))

/-- The failing present day, preceded only by representable slots in wire order. -/
def FirstOutOfRange (batches : List DateValues.Column) (batch slot : Nat) (day : Int) : Prop :=
  ∃ (before after : List DateValues.Column) (earlierSlots suffix : DateValues.Column) (date : CivilDate),
    batches = before ++ (earlierSlots ++ some date :: suffix) :: after ∧
    before.length = batch ∧ earlierSlots.length = slot ∧
    (∃ words : List Column, words.map (List.map (Option.map Date32.toCivil)) = before) ∧
    (∃ words : Column, words.map (Option.map Date32.toCivil) = earlierSlots) ∧
    date.toEpochDay? = some day ∧ (day < -2147483648 ∨ 2147483647 < day)

end Silmaril.Formats.Arrow.DateStream.Narrow
