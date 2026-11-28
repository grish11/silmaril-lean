module

public import Silmaril.Formats.Parquet.Int96.Mixed.File.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Defs

/-! Exact Arrow TIMESTAMP events from a checked mixed INT96 leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Int96.Mixed.File.Events

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (ConversionError Ticks TickUnit)
open Parquet.Timestamp.Leaf.Events (Kind Cell)

structure NarrowError where
  slot : Nat
  cause : ConversionError
  deriving DecidableEq, Repr

inductive Error where
  | openFailure (cause : File.OpenError)
  | groupFailure (group : Nat) (cause : File.ReadError)
  | narrowFailure (group : Nat) (cause : NarrowError)
  deriving DecidableEq, Repr

/-- The caller's explicit epoch policy supplies the Arrow annotation. -/
def metadata (policy : Policy) (target : TickUnit) : ColumnarTimestamp.Arrow.Metadata :=
  ⟨target, match policy with | .prolepticUtc => some "UTC" | .prolepticLocal => none⟩

abbrev Output (policy : Policy) (target : TickUnit) :=
  Ticks (metadata policy target).kind target

abbrev Slots (policy : Policy) (target : TickUnit) := List (Option (Output policy target))

/-- Every present destination tick passes the signed Arrow payload check. -/
def narrowSlot (policy : Policy) (target : TickUnit) :
    Option (Int96.Page.Value policy) → Except ConversionError (Option (Output policy target))
  | none => .ok none
  | some tick => (tick.toInt64 target).map fun word => some ((metadata policy target).decode word)

def narrowSlots (policy : Policy) (target : TickUnit) (slots : Dictionary.Slots policy)
    (start : Nat := 0) : Except NarrowError (Slots policy target) :=
  (slots.zipIdx start).mapM fun (slot, index) =>
    (narrowSlot policy target slot).mapError (NarrowError.mk index)

/-- Match nulls or exact nanosecond coordinates with a signed Arrow word. -/
def SlotMatches {policy : Policy} {target : TickUnit} :
    Option (Int96.Page.Value policy) → Option (Output policy target) → Prop
  | none, none => True
  | some input, some output => output.denote.ticks = input.ticks ∧
      ∃ word : Int64, output.ticks = word.toInt
  | _, _ => False

variable {name : String} {layout : FlatColumn.Layout} {policy : Policy}

def schema (checked : File.Checked name layout policy) (target : TickUnit) : Scan.Schema String Kind :=
  let leaf := checked.selection.bound.binding.leaf
  ⟨1, fun _ => (leaf.name, ⟨metadata policy target, layout == .optional⟩)⟩

def rows (checked : File.Checked name layout policy) (target : TickUnit) (slots : Slots policy target) :
    Reader.RowGroup (schema checked target) Cell :=
  slots.map fun slot _ => slot

/-- Read the complete original group before narrowing any of its slots. -/
def slotsAt (checked : File.Checked name layout policy) (target : TickUnit) (index : Nat) :
    Except Error (Slots policy target) := do
  let source ← (checked.readGroup index).mapError (.groupFailure index)
  (narrowSlots policy target source).mapError (.narrowFailure index)

def rowsAt (checked : File.Checked name layout policy) (target : TickUnit) (index : Nat) :
    Except Error (Reader.RowGroup (schema checked target) Cell) :=
  (slotsAt checked target index).map (rows checked target)

def groupSource (checked : File.Checked name layout policy) (target : TickUnit) :
    Reader.Source Nat (schema checked target) Cell Error :=
  ⟨List.range checked.selection.bound.snapshot.groupCount, rowsAt checked target, fun _ => .ok ()⟩

def openSource (limits : File.Limits) (name : String) (layout : FlatColumn.Layout)
    (policy : Policy) (target : TickUnit) (source : Bytes) : Reader.OpenResult Nat String Cell Error :=
  ((File.openFile limits source name layout policy).mapError .openFailure).map fun checked =>
    ⟨schema checked target, groupSource checked target⟩

/-- Emit one batch per complete footer group, including admitted empty groups. -/
def readAll (limits : File.Limits) (name : String) (layout : FlatColumn.Layout)
    (policy : Policy) (target : TickUnit) (source : Bytes) : Arrow.Events.EventStream String Cell Error :=
  Reader.readAll (openSource limits name layout policy target source)

end Silmaril.Formats.Parquet.Int96.Mixed.File.Events
