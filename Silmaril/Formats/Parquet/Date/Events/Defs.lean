module

public import Silmaril.Formats.Parquet.Date.Defs

/-! # Typed Date32 Arrow events from one checked Parquet DATE snapshot -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Events

open Silmaril.Relational

inductive Kind where
  | date32 (nullable : Bool)
  deriving DecidableEq, Repr

abbrev Cell (_ : Kind) := DateInterop.Date32.Payload

inductive Error where
  | openFailure (cause : Date.Error)
  | groupFailure (index : Nat) (cause : Date.Error)
  deriving DecidableEq, Repr

/-- The public schema retains the logical Date32 kind and the leaf's name and nullability. -/
def schema (checked : Date.Checked) : Scan.Schema String Kind :=
  ⟨1, fun _ => (checked.binding.leaf.name,
    .date32 (checked.binding.leaf.repetition == some .optional))⟩

def rows (checked : Date.Checked) (group : Date.RowGroup) :
    Reader.RowGroup (schema checked) Cell :=
  group.date32Slots.map fun slot _ => slot

def rowsAt (limits : Date.Limits) (checked : Date.Checked) (index : Nat) :
    Except Error (Reader.RowGroup (schema checked) Cell) :=
  ((checked.readGroup limits index).map (rows checked)).mapError (.groupFailure index)

/-- The cursor enumerates footer indices and pulls one checked group at a time. -/
def groupSource (limits : Date.Limits) (checked : Date.Checked) :
    Reader.Source Nat (schema checked) Cell Error :=
  ⟨List.range checked.snapshot.groupCount, rowsAt limits checked, fun _ => .ok ()⟩

def openSource (limits : Date.Limits) (input : Bytes) : Reader.OpenResult Nat String Cell Error :=
  ((Date.openChecked limits input).mapError .openFailure).map fun checked =>
    ⟨schema checked, groupSource limits checked⟩

def batchReader (limits : Date.Limits) :
    Arrow.Events.BatchReader Bytes String Cell Error (fun s => Reader.Source Nat s Cell Error) :=
  Reader.batchReader (openSource limits)

def readAll (limits : Date.Limits) (input : Bytes) : Arrow.Events.EventStream String Cell Error :=
  Reader.readAll (openSource limits input)

end Silmaril.Formats.Parquet.Date.Events
