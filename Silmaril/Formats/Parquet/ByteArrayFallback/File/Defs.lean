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

def rowsAtFor (profile : Profile) (checked : Checked name) (limits : Limits) (index : Nat) :
    Except Error (Reader.RowGroup (schema name) Value) :=
  (ByteArrayFallback.readGroupFor profile checked limits index).map (Plain.ByteArray.File.rows name .optional)
    |>.mapError .readFailure

/-- The source descriptors are the original footer group ordinals. -/
def sourceFor (profile : Profile) (checked : Checked name) (limits : Limits) :
    Reader.Source Nat (schema name) Value Error :=
  ⟨List.range checked.snapshot.groupCount, rowsAtFor profile checked limits, fun _ => .ok ()⟩

/-- Reuse the selected checked snapshot and its file and total row caps. -/
def openSourceFor (profile : Profile) (limits : Limits) (input : Bytes) (name : String) :
    Reader.OpenResult Nat String Value Error :=
  ((ByteArrayFallback.openFile limits input name).mapError .openFailure).map fun checked =>
    ⟨schema name, sourceFor profile checked limits⟩

/-- Emit one batch per successful group, including an admitted empty group. -/
def readAllFor (profile : Profile) (limits : Limits) (input : Bytes) (name : String) :
    Events.EventStream String Value Error :=
  Reader.readAll (openSourceFor profile limits input name)

def rowsAt {name : String} := rowsAtFor .rleDictionary (name := name)
def source {name : String} := sourceFor .rleDictionary (name := name)
def openSource := openSourceFor .rleDictionary
def readAll := readAllFor .rleDictionary

/-- Open the optional BYTE_ARRAY source under the parquet-java V1 profile. -/
def openLegacySource := openSourceFor .plainDictionaryV1

/-- Consume the legacy source in footer order and preserve original indexed errors. -/
def readAllLegacy := readAllFor .plainDictionaryV1

end Silmaril.Formats.Parquet.ByteArrayFallback.File
