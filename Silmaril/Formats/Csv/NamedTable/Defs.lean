module

public import Silmaril.Formats.Csv.Typed.Defs
public import Silmaril.Formats.Relational.NamedTable.Defs

/-!
# Named database tables at the typed CSV boundary

CSV headers check ordered field labels. A declared schema supplies kinds out of
band. Export returns that schema alongside the bytes, and named import checks it
against the expected destination schema using the same insertion policy as Arrow.
-/

@[expose] public section

namespace Silmaril.Formats.Csv.NamedTable

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Relational.NamedTable (Packed ImportError importCollected)

inductive ExportError where
  | missingName
  | encodeError (error : Typed.Error)
  deriving DecidableEq

variable {Name Kind : Type*} {Value : Kind → Type*}

/-- Fully decode the CSV before offering an EOS observation for insertion. A
decoding failure follows the existing collected-input error path. -/
def importCsv [DecidableEq Name] [DecidableEq Kind] (db : Packed Name Field Value)
    (name : Name) (expected declared : Typed.Schema Kind)
    (codecs : (kind : Kind) → Typed.CellCodec (Value kind)) (wire : Bytes) :
    Except (ImportError Typed.Error) (Packed Name Field Value) :=
  importCollected db name expected
    ((Typed.decode declared codecs wire).map fun rows => ⟨⟨declared, rows⟩, .eos⟩)

/-- Export the observed table at its original schema. The receiving adapter
gets the schema alongside the bytes as a separate value. -/
def exportCsv (db : Packed Name Field Value) (name : Name)
    (codecs : (kind : Kind) → Typed.CellCodec (Value kind)) :
    Except ExportError (Typed.Schema Kind × Bytes) :=
  match Scan.observePacked db name with
  | none => .error .missingName
  | some table =>
    match Typed.encode table.schema codecs table.rows with
    | .ok wire => .ok (table.schema, wire)
    | .error error => .error (.encodeError error)

/-- A complete CSV decode yields one aligned batch and EOS. Malformed or
unrepresentable input fails before emitting an event. -/
def eventsOfBytes (declared : Typed.Schema Kind)
    (codecs : (kind : Kind) → Typed.CellCodec (Value kind)) (wire : Bytes) :
    Events.EventStream Field Value Typed.Error :=
  (Typed.decode declared codecs wire).map fun rows =>
    ⟨declared, ⟨[AlignedColumns.ofRows rows], .eos⟩⟩

end Silmaril.Formats.Csv.NamedTable
