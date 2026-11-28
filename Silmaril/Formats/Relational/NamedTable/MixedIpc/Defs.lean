module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Defs
public import Silmaril.Formats.Relational.NamedTable.Defs

/-! Atomic import of an exact two-field Int32/BinaryView IPC V5 stream. -/

@[expose] public section

namespace Silmaril.Formats.Relational.NamedTable.MixedIpc

open Silmaril.Formats.Arrow
open Silmaril.Relational

inductive Kind where
  | int32
  | binaryView
  deriving DecidableEq, Repr

def Cell : Kind → Type
  | .int32 => Int32
  | .binaryView => List UInt8

/-- A named table identity carries the field's exact name and nullability. -/
abbrev Label := String × Bool
abbrev Database (Name : Type*) := NamedTable.Packed Name Label Cell

structure Descriptor where
  viewFirst : Bool
  integer : Label
  binary : Label
  deriving DecidableEq, Repr

def Descriptor.intField (descriptor : Descriptor) : MixedFlat.Field :=
  ⟨descriptor.integer.1, descriptor.integer.2, .primitive .int32⟩

def Descriptor.viewField (descriptor : Descriptor) : MixedFlat.Field :=
  ⟨descriptor.binary.1, descriptor.binary.2, .view .binary⟩

def Descriptor.fields (descriptor : Descriptor) : List MixedFlat.Field :=
  if descriptor.viewFirst then [descriptor.viewField, descriptor.intField]
  else [descriptor.intField, descriptor.viewField]

def Descriptor.ofFields : List MixedFlat.Field → Option Descriptor
  | [⟨i, ni, .primitive .int32⟩, ⟨b, nb, .view .binary⟩] => some ⟨false, (i, ni), (b, nb)⟩
  | [⟨b, nb, .view .binary⟩, ⟨i, ni, .primitive .int32⟩] => some ⟨true, (i, ni), (b, nb)⟩
  | _ => none

def Descriptor.schema (descriptor : Descriptor) : Scan.Schema Label Kind :=
  if descriptor.viewFirst then ⟨2, Fin.cases (descriptor.binary, .binaryView) (fun _ => (descriptor.integer, .int32))⟩
  else ⟨2, Fin.cases (descriptor.integer, .int32) (fun _ => (descriptor.binary, .binaryView))⟩

/-- The two cells of a single row, indexed by kind independently of wire order. -/
abbrev Pair := Option Int32 × Option (List UInt8)

def Descriptor.row (descriptor : Descriptor) (pair : Pair) : Scan.Row descriptor.schema Cell := by
  cases descriptor with
  | mk order integer binary =>
    cases order
    · exact Fin.cases (motive := fun j => Option (Cell ((Prod.snd ∘
        (Descriptor.schema ⟨false, integer, binary⟩).kind) j))) pair.1 (fun _ => pair.2)
    · exact Fin.cases (motive := fun j => Option (Cell ((Prod.snd ∘
        (Descriptor.schema ⟨true, integer, binary⟩).kind) j))) pair.2 (fun _ => pair.1)

structure Prepared where
  descriptor : Descriptor
  batches : List (List Pair)

def Prepared.table (prepared : Prepared) : Scan.Observation Label Cell :=
  ⟨prepared.descriptor.schema, prepared.batches.flatten.map prepared.descriptor.row⟩

structure Limits where
  inputBytes : Nat := 128 * 1024 * 1024
  mixed : MixedFlat.Limits := {}

inductive Error where
  | inputBytes (actual limit : Nat)
  | reader (cause : MixedFlat.Stream.Error)
  | unsupportedFields (actual : List MixedFlat.Field)
  | batchShape (index : Nat)
  deriving DecidableEq, Repr

def intSlot : Option Arrow.Value → Option (Option Int32)
  | none => some none
  | some (.int32 value) => some (some value)
  | some (.utf8 _) => none

def batchPairs (descriptor : Descriptor) (batch : MixedFlat.Stream.Batch) : Option (List Pair) := do
  let columns := batch.observed.columns
  if columns.map Prod.fst ≠ descriptor.fields then none else
    let ordered := if descriptor.viewFirst then columns.reverse else columns
    match ordered with
    | [(_, .primitive ints), (_, .binaryView bytes)] => do
      let ints ← ints.mapM intSlot
      if ints.length = batch.observed.rowCount ∧ bytes.length = batch.observed.rowCount then
        some (ints.zip (bytes.map (Option.map KBytes.toList)))
      else none
    | _ => none

def prepareBatches (descriptor : Descriptor) : Nat → List MixedFlat.Stream.Batch →
    Except Error (List (List Pair))
  | _, [] => .ok []
  | index, batch :: rest => do
    let some pairs := batchPairs descriptor batch | throw (.batchShape index)
    return pairs :: (← prepareBatches descriptor (index + 1) rest)

def prepare (source : MixedFlat.Stream.Observed) : Except Error Prepared := do
  let some descriptor := Descriptor.ofFields source.fields | throw (.unsupportedFields source.fields)
  let batches ← prepareBatches descriptor 0 source.batches
  return ⟨descriptor, batches⟩

/-- Retain every record boundary, including a zero-row batch. The native reader
requires exact EOS before this function returns a prepared observation. -/
def read (limits : Limits) (input : KBytes) : Except Error Prepared :=
  if input.len > limits.inputBytes then .error (.inputBytes input.len limits.inputBytes)
  else ((MixedFlat.Stream.read limits.mixed input).mapError .reader).bind prepare

def collect (limits : Limits) (input : KBytes) :
    Except Error (Events.Observation Label Cell Error) :=
  (read limits input).map fun prepared => ⟨prepared.table, .eos⟩

def classify : ImportError Error → ImportError Error
  | .openError (.reader (.batch index cause)) => .readError (.reader (.batch index cause))
  | .openError (.batchShape index) => .readError (.batchShape index)
  | cause => cause

/-- Insert only at a vacant name and at the exact ordered schema. The table
stores flattened rows. Call `read` for the original batch boundaries. -/
def importIpc {Name : Type*} [DecidableEq Name]
    (db : Database Name) (name : Name) (expected : Descriptor) (limits : Limits)
    (input : KBytes) : Except (ImportError Error) (Database Name) :=
  (NamedTable.importCollected db name expected.schema (collect limits input)).mapError classify

end Silmaril.Formats.Relational.NamedTable.MixedIpc
