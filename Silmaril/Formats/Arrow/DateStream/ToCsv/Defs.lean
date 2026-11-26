module

public import Silmaril.Formats.Arrow.DateStream.FromCsv.Defs

/-! # Canonical typed calendar CSV export from one explicit Date32 IPC batch -/

@[expose] public section

namespace Silmaril.Formats.Arrow.DateStream.ToCsv

open Csv.Typed.Codecs.Date32 (Cell)

inductive Error where
  | reader (cause : DateStream.Error)
  | descriptor (actual : DateStream.Field)
  | batchCount (actual : Nat)
  | unrepresentableDay
  | csvRowLimit (actual limit : Nat)
  | csv (cause : Csv.Typed.Codecs.Date32.Error)
  | csvByteLimit (actual limit : Nat)
  deriving DecidableEq, Repr

/-- Each slot becomes one row in the explicitly declared one-column schema. -/
def rows (name : String) (nullable : Bool) (slots : Writer.Column) :
    Csv.Typed.Table (FromCsv.schema name nullable) Cell :=
  slots.map fun slot _ => slot

/-- Read through EOS before checking the exact descriptor and requiring one
explicit batch. Its nullable civil dates must recover their signed words. -/
def readColumn (limits : Limits) (name : String) (nullable : Bool) (input : KBytes) :
    Except Error Writer.Column := do
  let source ← (DateStream.read limits input).mapError .reader
  if source.field ≠ ⟨name, nullable, .day⟩ then throw (.descriptor source.field)
  let [dates] := source.batches | .error (.batchCount source.batches.length)
  let some slots := dates.mapM (fun date => date.mapM DateInterop.Date32.ofCivil?)
    | .error .unrepresentableDay
  return slots

/-- Check the row cap before formatting and the canonical byte cap before
returning complete CSV. An explicit zero-row batch gives header-only CSV. -/
def convert (ipc : Limits) (csv : FromCsv.CsvLimits) (name : String) (nullable : Bool)
    (input : KBytes) : Except Error Csv.Bytes := do
  let slots ← readColumn ipc name nullable input
  if slots.length > csv.maxRows then throw (.csvRowLimit slots.length csv.maxRows)
  let output ← (Csv.Typed.Codecs.Date32.encode (FromCsv.schema name nullable) id
    (rows name nullable slots)).mapError .csv
  if output.length > csv.maxBytes then throw (.csvByteLimit output.length csv.maxBytes)
  return output

end Silmaril.Formats.Arrow.DateStream.ToCsv
