module

public import Silmaril.Formats.Arrow.Body.Defs
public import Silmaril.Formats.Csv.NamedTable.Defs
public import Silmaril.Formats.Csv.Typed.Codecs.Defs

/-!
# Arrow IPC streams through a named table to typed CSV

The merged reader checks modern EOS and fully observes the supported Int32 and
UTF-8 stream before insertion. The typed schema retains UTF-8 field-name bytes,
field kinds and nullability in position order. CSV encoding applies its existing
wire alphabet and returns the typed schema alongside the bytes.
-/

@[expose] public section

namespace Silmaril.Formats.Arrow.ToCsv

open Silmaril.Relational
open Silmaril.Formats.Relational.NamedTable (Packed ImportError importCollected)

abbrev Kind := FieldType × Bool

def Cell (kind : Kind) : Type :=
  match kind.1 with
  | .int32 => Int32
  | .utf8 => String

def labelOf (field : Field) : Csv.Field × Kind :=
  (field.name.toByteArray.data.toList, (field.type, field.nullable))

def schemaOf (fields : List Field) : Csv.Typed.Schema Kind :=
  ⟨fields.length, labelOf ∘ fields.get⟩

def codecs (kind : Kind) : Csv.Typed.CellCodec (Cell kind) :=
  match kind with
  | (.int32, _) => Csv.Typed.Codecs.int32
  | (.utf8, _) => Csv.Typed.Codecs.utf8

inductive InputError where
  | ipc (error : Error)
  | rowWidth
  | cellKind
  | requiredNull
  deriving DecidableEq, Repr

inductive ConvertError where
  | input (error : ImportError InputError)
  | output (error : Csv.NamedTable.ExportError)
  deriving DecidableEq

def typedCell (kind : Kind) (value : Option Value) : Except InputError (Option (Cell kind)) :=
  match kind, value with
  | (_, nullable), none => if nullable then .ok none else .error .requiredNull
  | (.int32, _), some (.int32 n) => .ok (some n)
  | (.utf8, _), some (.utf8 text) => .ok (some text)
  | _, _ => .error .cellKind

/-- Check width, value tags and required cells while building a schema-indexed row. -/
def typedRow : (fields : List Field) → Row → Except InputError (Scan.Row (schemaOf fields) Cell)
  | [], raw => if raw.isEmpty then .ok (fun i => i.elim0) else .error .rowWidth
  | field :: fields, raw =>
    match raw with
    | [] => .error .rowWidth
    | value :: rest => do
      let head ← typedCell (field.type, field.nullable) value
      let tail ← typedRow fields rest
      return Fin.cases (motive := fun i => Option (Cell ((schemaOf (field :: fields)).kind i).2)) head tail

def eraseCell (kind : Kind) : Option (Cell kind) → Option Value :=
  match kind with
  | (.int32, _) => Option.map Value.int32
  | (.utf8, _) => Option.map Value.utf8

def eraseRow (fields : List Field) (row : Scan.Row (schemaOf fields) Cell) : Row :=
  List.ofFn fun i => eraseCell ((schemaOf fields).kind i).2 (row i)

def typedRows (observed : ObservedStream) :
    Except InputError (Scan.Table (schemaOf observed.fields) Cell) :=
  observed.batches.flatten.mapM (typedRow observed.fields)

/-- A complete reader result becomes an EOS observation. Any byte or
translation error reaches the insertion gate before there is a table to insert. -/
def observeIpc (limits : ObservationLimits) (input : KBytes) :
    Except InputError (Events.Observation Csv.Field Cell InputError) := do
  let observed ← (readRows limits input).mapError InputError.ipc
  let rows ← typedRows observed
  return ⟨⟨schemaOf observed.fields, rows⟩, .eos⟩

def importIpc {Name : Type} [DecidableEq Name] (db : Packed Name Csv.Field Cell)
    (name : Name) (expected : Csv.Typed.Schema Kind) (limits : ObservationLimits) (input : KBytes) :
    Except (ImportError InputError) (Packed Name Csv.Field Cell) :=
  importCollected db name expected (observeIpc limits input)

/-- Load the requested name and export it through the existing typed CSV encoder. -/
def convert {Name : Type} [DecidableEq Name] (db : Packed Name Csv.Field Cell)
    (name : Name) (expected : Csv.Typed.Schema Kind) (limits : ObservationLimits) (input : KBytes) :
    Except ConvertError (Csv.Typed.Schema Kind × Csv.Bytes) := do
  let loaded ← (importIpc db name expected limits input).mapError ConvertError.input
  (Csv.NamedTable.exportCsv loaded name codecs).mapError ConvertError.output

end Silmaril.Formats.Arrow.ToCsv
