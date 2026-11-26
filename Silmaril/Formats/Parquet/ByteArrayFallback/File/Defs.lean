module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Defs

/-! One selected BYTE_ARRAY column with dictionary fallback in footer group order. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.File

open Silmaril.Relational Silmaril.Formats.Arrow

abbrev Value := Plain.ByteArray.File.Value
abbrev schema (name : String) := Plain.ByteArray.File.schema name .optional

inductive Error where
  | openFailure (cause : Plain.ByteArray.File.Error)
  | readFailure (cause : ByteArrayFallback.Error)
  deriving DecidableEq, Repr

variable {name : String}

def rowsAt (checked : Checked name) (limits : Limits) (index : Nat) :
    Except Error (Reader.RowGroup (schema name) Value) :=
  (ByteArrayFallback.readGroup checked limits index).map (Plain.ByteArray.File.rows name .optional)
    |>.mapError .readFailure

/-- The source descriptors are the original footer group ordinals. -/
def source (checked : Checked name) (limits : Limits) :
    Reader.Source Nat (schema name) Value Error :=
  ⟨List.range checked.snapshot.groupCount, rowsAt checked limits, fun _ => .ok ()⟩

/-- Reuse the selected checked snapshot and its file and total row caps. -/
def openSource (limits : Limits) (input : Bytes) (name : String) :
    Reader.OpenResult Nat String Value Error :=
  ((ByteArrayFallback.openFile limits input name).mapError .openFailure).map fun checked =>
    ⟨schema name, source checked limits⟩

/-- Emit one batch per successful group, including an admitted empty group. -/
def readAll (limits : Limits) (input : Bytes) (name : String) :
    Events.EventStream String Value Error :=
  Reader.readAll (openSource limits input name)

end Silmaril.Formats.Parquet.ByteArrayFallback.File
