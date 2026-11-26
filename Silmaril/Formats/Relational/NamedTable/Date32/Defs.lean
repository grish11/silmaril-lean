module

public import Silmaril.Formats.Relational.NamedTable.Defs
public import Silmaril.Formats.Parquet.Date.Events.Defs
public import Silmaril.Formats.Arrow.DateStream.Defs

/-! Atomic named imports from the checked one-column Date32 wire profiles. -/

@[expose] public section

namespace Silmaril.Formats.Relational.NamedTable.Date32

open Silmaril.Numeric.Gregorian (CivilDate)
open Silmaril.Relational
open Parquet
open Arrow

abbrev Slot := Option DateInterop.Date32.Payload

abbrev Database (Name : Type*) := Packed Name String Date.Events.Cell

/-- The shared ordered descriptor uses the existing Parquet DATE event kind. -/
def schema (field : String) (nullable : Bool) : Scan.Schema String Date.Events.Kind :=
  ⟨1, fun _ => (field, .date32 nullable)⟩

def rows (field : String) (nullable : Bool) (slots : List Slot) :
    Scan.Table (schema field nullable) Date.Events.Cell :=
  slots.map fun slot _ => slot

inductive IpcError where
  | source (cause : DateStream.Error)
  | date64
  | epochDayRange
  deriving DecidableEq, Repr

/-- Recover the signed word from the reader's civil observation. The error
case is unreachable for a successful checked Date32 read. -/
def recover (slot : Option CivilDate) : Except IpcError Slot :=
  match slot with
  | none => .ok none
  | some civil =>
    match DateInterop.Date32.ofCivil? civil with
    | some word => .ok (some word)
    | none => .error .epochDayRange

variable {Name : Type*} [DecidableEq Name]

/-- Consume the checked Parquet DATE events to EOF and use the named gate. -/
def importParquet (db : Database Name) (name : Name) (field : String) (nullable : Bool)
    (limits : Parquet.Date.Limits) (input : Bytes) :
    Except (ImportError Date.Events.Error) (Database Name) :=
  NamedTable.importArrow db name (schema field nullable) (Date.Events.readAll limits input)

/-- Import at a vacant name after exact IPC EOS. Batch errors keep their
original index and cause. A successful Date64 read is outside this profile. -/
def importIpc (db : Database Name) (name : Name) (field : String) (nullable : Bool)
    (limits : Arrow.Limits) (input : KBytes) :
    Except (ImportError IpcError) (Database Name) :=
  if (db name).isSome then .error .nameConflict
  else
    match DateStream.read limits input with
    | .error (.batch index cause) => .error (.readError (.source (.batch index cause)))
    | .error cause => .error (.openError (.source cause))
    | .ok stream =>
      if stream.field.unit ≠ .day then .error (.openError .date64)
      else
        match stream.batches.flatten.mapM recover with
        | .error cause => .error (.readError cause)
        | .ok slots =>
          let actual := stream.field
          importCollected db name (schema field nullable)
            (.ok ⟨⟨schema actual.name actual.nullable, rows actual.name actual.nullable slots⟩, .eos⟩)

end Silmaril.Formats.Relational.NamedTable.Date32
