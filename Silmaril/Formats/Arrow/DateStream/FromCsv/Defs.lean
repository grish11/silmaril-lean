module

public import Silmaril.Formats.Arrow.DateStream.Writer.Defs
public import Silmaril.Formats.Csv.Typed.Codecs.Date32.Defs

/-! # Bounded typed calendar CSV import into a single Date32 IPC batch -/

@[expose] public section

namespace Silmaril.Formats.Arrow.DateStream.FromCsv

open Csv.Typed.Codecs.Date32 (Cell)

structure CsvLimits where
  maxBytes : Nat
  maxRows : Nat

inductive Error where
  | csvByteLimit (actual limit : Nat)
  | csv (cause : Csv.Typed.Codecs.Date32.Error)
  | csvRowLimit (actual limit : Nat)
  | writer (cause : Writer.Error)
  deriving DecidableEq, Repr

/-- The caller declares the exact UTF-8 header and field nullability. -/
def schema (name : String) (nullable : Bool) : Csv.Typed.Schema Bool :=
  ⟨1, fun _ => (name.toUTF8.data.toList, nullable)⟩

def slots {name : String} {nullable : Bool}
    (rows : Csv.Typed.Table (schema name nullable) Cell) : Writer.Column :=
  rows.map fun row => row ⟨0, Nat.zero_lt_succ 0⟩

/-- Limit input bytes before CSV parsing and rows before IPC emission. The
single record is explicit even for header-only input. -/
def convert (ipc : ObservationLimits) (csv : CsvLimits) (name : String) (nullable : Bool)
    (input : Csv.Bytes) : Except Error KBytes := do
  if input.length > csv.maxBytes then throw (.csvByteLimit input.length csv.maxBytes)
  let rows ← (Csv.Typed.Codecs.Date32.decode (schema name nullable) id input).mapError .csv
  if rows.length > csv.maxRows then throw (.csvRowLimit rows.length csv.maxRows)
  (Writer.emit ipc name nullable [slots rows]).mapError .writer

end Silmaril.Formats.Arrow.DateStream.FromCsv
