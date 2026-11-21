module

public import Mathlib.Data.Finset.Card
public import Silmaril.Formats.Dasl.Encode.Map.Thms
public import Silmaril.Formats.Dasl.Resolve.Defs
public import Silmaril.Formats.Dasl.Wire.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.StringObjectMap

open Silmaril.Semantics (OrderedMap)

variable {Name : Type}

/-- An inline shallow object may itself contain links, including at its root.
The explicit storage tag distinguishes this from following a value link. -/
inductive Placement (Name : Type) where
  | inline (value : Shallow Name)
  | linked (name : Name)

def Placement.encode : Placement Name → Shallow Name
  | .inline value => Encode.pairEntry.encode (.string "inline", value)
  | .linked name => Encode.pairEntry.encode (.string "link", .ref (.obj name))

def Placement.decode? (source : Shallow Name) : Option (Placement Name) := do
  let (tag, value) ← Encode.pairEntry.decode? source
  match tag, value with
  | .string "inline", value => some (.inline value)
  | .string "link", .ref (.obj name) => some (.linked name)
  | _, _ => none

def Placement.codec : Encode.TotalCodec (Placement Name) (Shallow Name) :=
  ⟨Placement.encode, Placement.decode?, fun placement => by cases placement <;> rfl⟩

abbrev Layout (Name : Type) := OrderedMap String (Placement Name)

/-- Flat array of `[key, placement]` pairs in strict `String` order.
The order is on the source keys, not the CBOR dictionary key order. -/
def codec : Encode.TotalCodec (Layout Name) (Shallow Name) := Encode.pairMap Encode.text Placement.codec

def keySet (layout : Layout Name) : Finset String := layout.keys.toFinset

def cardinality (layout : Layout Name) : Nat := layout.entries.length

abbrev Read (Name : Type) := Name → Wire.ReadResult (Shallow Name)

def Read.Sound (read : Read Name) (store : Store Name) : Prop :=
  ∀ ⦃name value⦄, read name = .found value → store.objects name value

/-- Adapt a byte store with a selected object-kind guard and shallow parser.
The caller supplies the profile; this does not verify digests. -/
def readWire (objectName : Name → Bool) (parse? : ByteArray → Option (Shallow Name))
    (read : Name → Option ByteArray) : Read Name := fun name =>
  if objectName name then
    match read name with
    | none => .missing
    | some bytes => match parse? bytes with
      | none => .invalidWire
      | some value => .found value
  else .invalidWire

inductive ValueFault (Name : Type) where
  | missing (name : Name)
  | invalidWire (name : Name)
  deriving DecidableEq, Repr

/-- Recover a value by following at most the placement's one object link.
Links inside the returned shallow object are not followed. -/
def recover (read : Read Name) : Option (Placement Name) → Except (ValueFault Name) (Option (Shallow Name))
  | none => .ok none
  | some (.inline value) => .ok (some value)
  | some (.linked name) => match read name with
    | .found value => .ok (some value)
    | .missing => .error (.missing name)
    | .invalidWire => .error (.invalidWire name)

def lookup (layout : Layout Name) (read : Read Name) (key : String) := recover read (layout.lookup? key)

def LookupSpec (store : Store Name) : Option (Placement Name) → Option (Shallow Name) → Prop
  | none, none => True
  | some (.inline inlineValue), some value => inlineValue = value
  | some (.linked name), some value => store.objects name value
  | _, _ => False

end Silmaril.Formats.Dasl.StringObjectMap
