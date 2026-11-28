module

public import Silmaril.Formats.Parquet.Date.Events.ToIpc.Defs
public import Silmaril.Formats.Arrow.DateStream.ToCsv.Defs

/-! # Bounded typed civil-date CSV from checked Parquet DATE events -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.ToCsv

inductive Error where
  | source (cause : Date.Events.Error)
  | closed
  | fieldCount (actual : Nat)
  | descriptor (name : String) (kind : Date.Events.Kind)
  | encode (cause : Arrow.DateStream.ToCsv.Error)
  deriving DecidableEq, Repr

/-- Read the checked source through EOF and take its exact ordered signed
slots. The declared name and nullability must match the source. -/
def readRows (limits : Date.Limits) (name : String) (nullable : Bool) (input : Bytes) :
    Except Error Arrow.DateStream.Writer.Column :=
  match Date.Events.readAll limits input with
  | .error cause => .error (.source cause)
  | .ok ⟨schema, trace⟩ =>
    match trace.termination with
    | .readError cause | .closeError cause => .error (.source cause)
    | .closed => .error .closed
    | .eos =>
      if one : schema.width = 1 then
        let column : Fin schema.width := ⟨0, by omega⟩
        let actual := schema.kind column
        if actual = (name, .date32 nullable) then
          .ok (Date.Events.ToIpc.batchSlots trace column).flatten
        else .error (.descriptor actual.1 actual.2)
      else .error (.fieldCount schema.width)

/-- Apply the total CSV row cap and canonical byte cap after checked EOF.
Empty groups contribute no rows to the CSV. -/
def convert (limits : Date.Limits) (csv : Arrow.DateStream.FromCsv.CsvLimits)
    (name : String) (nullable : Bool) (input : Bytes) : Except Error Csv.Bytes := do
  let slots ← readRows limits name nullable input
  (Arrow.DateStream.ToCsv.Internal.encodeColumn csv name nullable slots).mapError .encode

end Silmaril.Formats.Parquet.Date.ToCsv
