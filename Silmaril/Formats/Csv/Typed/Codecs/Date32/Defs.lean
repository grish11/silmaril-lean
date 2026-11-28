module

public import Silmaril.Formats.Csv.Typed.Utf8.Defs
public import Silmaril.Formats.DateInterop.Defs

/-! # Canonical four-digit Date32 calendar cells in typed UTF-8 CSV -/

@[expose] public section

namespace Silmaril.Formats.Csv.Typed.Codecs.Date32

open Silmaril.Numeric.Gregorian (CivilDate)

abbrev Payload := DateInterop.Date32.Payload

/-- A signed Date32 day is printable when its astronomical civil year fits four digits. -/
def Admitted (value : Payload) : Prop :=
  let year := (DateInterop.Date32.toCivil value).year
  0 ≤ year ∧ year < 10000

instance (value : Payload) : Decidable (Admitted value) := by
  unfold Admitted
  infer_instance

namespace Internal

def digits : Nat → Nat → Field
  | 0, _ => []
  | width + 1, value =>
    UInt8.ofNat (48 + value / 10 ^ width) :: digits width (value % 10 ^ width)

def readDigits : Field → Option Nat
  | [] => some 0
  | byte :: rest => do
    if 48 ≤ byte.toNat ∧ byte.toNat ≤ 57 then
      let tail ← readDigits rest
      return (byte.toNat - 48) * 10 ^ rest.length + tail
    else none

def calendarText (date : CivilDate) : Field :=
  digits 4 date.year.toNat ++ [0x2D] ++ digits 2 date.month ++ [0x2D] ++ digits 2 date.day

/-- Inspect the whole field before reading its three fixed-width components. -/
def candidate (field : Field) : Option CivilDate := do
  if field.length ≠ 10 then none else
  let dash :: monthAndDay := field.drop 4 | none
  let separator :: dayDigits := monthAndDay.drop 2 | none
  if dash ≠ 0x2D ∨ separator ≠ 0x2D then none else do
    let year ← readDigits (field.take 4)
    let month ← readDigits (monthAndDay.take 2)
    let day ← readDigits dayDigits
    return ⟨year, month, day⟩

end Internal

def print (value : Payload) : Option Field :=
  if Admitted value then some (Internal.calendarText (DateInterop.Date32.toCivil value)) else none

/-- Check the Gregorian candidate, then require exact reproduction of the input. -/
def parse (field : Field) : Option Payload := do
  let date ← Internal.candidate field
  let value ← DateInterop.Date32.ofCivil? date
  if print value = some field then some value else none

def codec : CellCodec Payload := ⟨print, parse⟩

abbrev Cell {Kind : Type*} (_ : Kind) := Payload

inductive Error where
  | requiredNull (row column : Nat)
  | csv (cause : Typed.Error)
  deriving DecidableEq, Repr

variable {Kind : Type*}

/-- The first required null in row-major order. Both indices are zero-based. -/
def firstRequiredNull (schema : Schema Kind) (nullable : Kind → Bool)
    (table : Table schema Cell) : Option (Nat × Nat) :=
  table.zipIdx.findSome? fun (row, index) =>
    ((List.finRange schema.width).find? fun column =>
      !(nullable (schema.kind column).2) && (row column).isNone).map fun column =>
        (index, column.val)

/-- Enforce the caller's required fields before using the standard typed exporter. -/
def encode (schema : Schema Kind) (nullable : Kind → Bool) (table : Table schema Cell) :
    Except Error Bytes :=
  match firstRequiredNull schema nullable table with
  | some (row, column) => .error (.requiredNull row column)
  | none => (Typed.Utf8.encode schema (fun _ => codec) table).mapError .csv

/-- Preserve framing and cell errors from typed UTF-8 CSV, then check required fields. -/
def decode (schema : Schema Kind) (nullable : Kind → Bool) (bytes : Bytes) :
    Except Error (Table schema Cell) := do
  let table ← (Typed.Utf8.decode schema (Value := Cell) (fun _ => codec) bytes).mapError .csv
  match firstRequiredNull schema nullable table with
  | some (row, column) => .error (.requiredNull row column)
  | none => .ok table

end Silmaril.Formats.Csv.Typed.Codecs.Date32
