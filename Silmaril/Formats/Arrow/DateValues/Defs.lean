module

public import Silmaril.Formats.Arrow.Body.Defs
public import Silmaril.Formats.DateInterop.Defs
public import Mathlib.Data.List.Forall2

/-! # Checked scalar DATE buffers

This layer accepts the Date tag, resolved unit and endianness from the caller,
together with a fixed-width view or a single-column IPC record batch. The
existing Arrow metadata readers still own schema FlatBuffers admission.
-/

@[expose] public section

namespace Silmaril.Formats.Arrow.DateValues

open Silmaril.Formats.DateInterop
open Silmaril.Numeric.Gregorian (CivilDate)

inductive Unit where
  | day
  | millisecond
  deriving DecidableEq, Repr

def Unit.code : Unit → Nat
  | .day => 0
  | .millisecond => 1

def Unit.width : Unit → Nat
  | .day => 4
  | .millisecond => 8

def Unit.toCivil? : Unit → Nat → Option CivilDate
  | .day, word => some (Date32.toCivil (Int32.ofNat word))
  | .millisecond, word => Date64.toCivil? (Int64.ofNat word)

/-- The already resolved Field union tag and Date payload unit. The caller
resolves the IDL default before passing a unit code. -/
structure Descriptor where
  typeTag : Nat
  dateUnit : Nat
  endianness : Nat
  nullable : Bool
  deriving DecidableEq, Repr

/-- An offset in slots shared by the bitmap and value buffer. IPC record bodies
start at slot zero. An in-memory array slice may start within a bitmap byte. -/
structure View where
  start : Nat
  node : FieldNode
  validity : KBytes
  values : KBytes

inductive Error where
  | ipc (error : Arrow.Error)
  | wrongUnit (expected : Unit) (actual : Nat)
  | nonWholeDay (slot : Nat)
  deriving DecidableEq, Repr

abbrev Column := List (Option CivilDate)

/-- Check the caller's resolved DATE descriptor against the selected decoder. -/
def Descriptor.validate (descriptor : Descriptor) (unit : Unit) : Except Error _root_.Unit :=
  if descriptor.typeTag ≠ 8 then .error (.ipc (.unsupported (.fieldType descriptor.typeTag)))
  else if descriptor.dateUnit ≠ unit.code then .error (.wrongUnit unit descriptor.dateUnit)
  else if descriptor.endianness ≠ 0 then .error (.ipc (.unsupported (.endianness descriptor.endianness)))
  else .ok ()

/-- Validate the full requested physical window before interpreting any slot. -/
def check (limits : Limits) (unit : Unit) (descriptor : Descriptor) (view : View) :
    Except Error _root_.Unit := do
  descriptor.validate unit
  if !view.validity.wf || !view.values.wf then throw (.ipc (.malformed .source))
  if view.node.length > limits.rows then throw (.ipc (.limit .rows))
  if view.validity.len + view.values.len > limits.bodyBytes then throw (.ipc (.limit .bodyBytes))
  if view.node.nullCount > view.node.length || (!descriptor.nullable && view.node.nullCount != 0) then
    throw (.ipc (.malformed .validityBitmap))
  let stop := view.start + view.node.length
  if ¬ Body.BitmapExtent view.validity stop then throw (.ipc (.malformed .validityBitmap))
  if unit.width * stop > view.values.len then throw (.ipc (.malformed .bodyValues))

/-- Read the physical word even for null slots to require its extent. Interpret
the word as a date only when the corresponding bit is set. -/
def readSlot (unit : Unit) (view : View) (slot : Nat) : Except Error (Option CivilDate) := do
  let index := view.start + slot
  let some valid := Body.validAt view.validity index
    | throw (.ipc (.malformed .validityBitmap))
  let some word := view.values.readLE (unit.width * index) unit.width
    | throw (.ipc (.malformed .bodyValues))
  if !valid then return none
  let some date := unit.toCivil? word | throw (.nonWholeDay slot)
  return some date

def decode (limits : Limits) (unit : Unit) (descriptor : Descriptor) (view : View) :
    Except Error Column := do
  check limits unit descriptor view
  let dates ← (List.range view.node.length).mapM (readSlot unit view)
  if dates.countP Option.isNone ≠ view.node.nullCount then throw (.ipc (.malformed .validityBitmap))
  return dates

/-- A single flat DATE column has one node and two ordered descriptors. Check
both descriptor extents before taking any slice of the record body. -/
def batchView (limits : Limits) (batch : RecordBatch) (body : KBytes) : Except Error View :=
  if !body.wf then .error (.ipc (.malformed .source))
  else if body.len > limits.bodyBytes then .error (.ipc (.limit .bodyBytes))
  else
    match batch.nodes, batch.buffers with
    | [node], [bitmap, data] =>
      if node.length = batch.rowCount ∧ BuffersFit body.len 0 [bitmap, data] then
        .ok ⟨0, node, Body.sliceBuffer body bitmap, Body.sliceBuffer body data⟩
      else .error (.ipc (.malformed .batchLayout))
    | _, _ => .error (.ipc (.malformed .batchLayout))

def decodeBatch (limits : Limits) (unit : Unit) (descriptor : Descriptor)
    (batch : RecordBatch) (body : KBytes) : Except Error Column := do
  let view ← batchView limits batch body
  decode limits unit descriptor view

def SlotWire (unit : Unit) (view : View) (slot : Nat) (date : Option CivilDate) : Prop :=
  ∃ valid word,
    Body.validAt view.validity (view.start + slot) = some valid ∧
    view.values.readLE (unit.width * (view.start + slot)) unit.width = some word ∧
    if valid then ∃ civil, unit.toCivil? word = some civil ∧ date = some civil else date = none

def ColumnWire (unit : Unit) (view : View) (dates : Column) : Prop :=
  List.Forall₂ (SlotWire unit view) (List.range view.node.length) dates ∧
    dates.countP Option.isNone = view.node.nullCount

end Silmaril.Formats.Arrow.DateValues
