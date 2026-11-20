module

public import Silmaril.Formats.Dasl.Prolly.Thms
public import Silmaril.Formats.Dasl.Wire.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Prolly

open Silmaril.Semantics (OrderedMap)
open Silmaril.Semantics.Prolly (Block)

variable {Name Key Payload : Type}

inductive Fault (Name : Type) where
  | fuel (name : Name)
  | missing (name : Name)
  | invalidWire (name : Name)
  | invalidNode (name : Name)
  deriving DecidableEq, Repr

abbrev Read (Name : Type) := Name → Wire.ReadResult (Shallow Name)

/-- Claims only that successful shallow reads are included in the reference. -/
def Read.Sound (read : Read Name) (store : Store Name) : Prop :=
  ∀ ⦃name value⦄, read name = .found value → store.objects name value

def readBlock (codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)) (read : Read Name)
    (name : Name) : Except (Fault Name) (Block Name Key Payload) :=
  match read name with
  | .missing => .error (.missing name)
  | .invalidWire => .error (.invalidWire name)
  | .found value => match codec.decode? value with
    | none => .error (.invalidNode name)
    | some block => .ok block

def finishChild [DecidableEq Key] (parent : Name) (separator : Key) (entries : List (Key × Payload)) :
    Except (Fault Name) (List (Key × Payload)) :=
  if entries.getLast?.map Prod.fst = some separator then .ok entries else .error (.invalidNode parent)

/-- Read a closed tree view. Fuel counts block reads along a path. Every child must
be present before an answer, and levels, shapes, widths and separators are checked.
The final lookup checks global ordering separately. This is not a routed lookup. -/
def scan [DecidableEq Key] (read : Name → Except (Fault Name) (Block Name Key Payload)) (width : Nat) :
    (fuel : Nat) → Option Nat → Name → Except (Fault Name) (List (Key × Payload))
  | 0, _, name => .error (.fuel name)
  | fuel + 1, expected, name => do
    match ← read name with
    | .leaf entries =>
      if (expected = none ∨ expected = some 0) ∧ entries.length ≤ width then .ok entries
      else .error (.invalidNode name)
    | .branch level children =>
      if (expected = none ∨ expected = some level) ∧ 0 < level ∧ 0 < children.length ∧ children.length ≤ width then do
        let groups ← children.mapM fun child => do
          let entries ← scan read width fuel (some (level - 1)) child.2
          finishChild name child.1 entries
        pure groups.flatten
      else .error (.invalidNode name)

/-- `.ok none` is closed-view absence, never a translation of a read failure. -/
def lookup [LinearOrder Key] (codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)) (read : Read Name)
    (width fuel : Nat) (root : Name) (key : Key) : Except (Fault Name) (Option Payload) := do
  let entries ← scan (readBlock codec read) width fuel none root
  match OrderedMap.ofEntries? entries with
  | some map => .ok (map.lookup? key)
  | none => .error (.invalidNode root)

end Silmaril.Formats.Dasl.Prolly
