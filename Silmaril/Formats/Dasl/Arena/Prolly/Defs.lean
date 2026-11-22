module

public import Silmaril.Formats.Dasl.Prolly.Route.Defs
public import Silmaril.Formats.Dasl.RawStore.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Arena.Prolly

open Silmaril.Formats.Dasl.Prolly (Fault Read readBlock route)
open Silmaril.Semantics.Prolly (Block)

variable {Name Key Payload : Type}

abbrev Reader (Ref Key Payload : Type) := Ref → Except (Fault Ref) (Block Ref Key Payload)

def readRaw (decoder : RawStore.Decoder Name) [DecidablePred decoder.objectName]
    (fetch : Name → Option ByteArray) : Read Name := fun name =>
  if decoder.objectName name then
    match fetch name with
    | none => .missing
    | some bytes => match decoder.parse? bytes with
      | none => .invalidWire
      | some shallow => .found shallow
  else .invalidWire

abbrev BlockCodec (Name Key Payload : Type) := Encode.PartialCodec (Block Name Key Payload) (Shallow Name)

/-- A finite, explicitly acquired snapshot. The stored failures describe this observation
only. This type does not authorize reusing them as negative cache evidence. -/
structure Resident (Name Key Payload : Type) where
  cells : List (Name × Except (Fault Name) (Block Name Key Payload))

def Resident.capture (codec : BlockCodec Name Key Payload) (input : Read Name) (names : List Name) :
    Resident Name Key Payload :=
  ⟨names.map fun name => (name, readBlock codec input name)⟩

def Resident.read [DecidableEq Name] (resident : Resident Name Key Payload) : Reader Name Key Payload :=
  fun name => (resident.cells.lookup name).getD (.error (.missing name))

def Resident.lookup [DecidableEq Name] [LinearOrder Key] (resident : Resident Name Key Payload)
    (width fuel : Nat) (root : Name) (key : Key) : Except (Fault Name) (Option Payload) :=
  route resident.read width key fuel none root

/-- Retain successful observations of the acquisition list for the reference proof. -/
def restrict [DecidableEq Name] (input : Read Name) (names : List Name) : Read Name := fun name =>
  if name ∈ names then input name else .missing

end Silmaril.Formats.Dasl.Arena.Prolly
