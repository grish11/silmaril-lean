module

public import Silmaril.Formats.Dasl.Prolly.Scan.Defs
public import Silmaril.Semantics.Prolly.Routing.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Prolly

open Silmaril.Semantics.Prolly (Block Node nodeBlock selectChild)

variable {Name Key Payload : Type} [LinearOrder Key]

/-- Visit only the selected path. Fuel counts node reads. Faults encountered on
that path are returned unchanged; siblings are neither visited nor certified. -/
def route (read : Name → Except (Fault Name) (Block Name Key Payload)) (width : Nat) (key : Key) :
    (fuel : Nat) → Option Nat → Name → Except (Fault Name) (Option Payload)
  | 0, _, name => .error (.fuel name)
  | fuel + 1, expected, name => do
    match ← read name with
    | .leaf entries =>
      if (expected = none ∨ expected = some 0) ∧ entries.length ≤ width ∧
          entries.Pairwise (fun left right => left.1 < right.1) then .ok (entries.lookup key)
      else .error (.invalidNode name)
    | .branch level children =>
      if (expected = none ∨ expected = some level) ∧ 0 < level ∧ 0 < children.length ∧
          children.length ≤ width ∧ children.Pairwise (fun left right => left.1 < right.1) then
        match selectChild key children with
        | none => .ok none
        | some child => route read width key fuel (some (level - 1)) child.2
      else .error (.invalidNode name)

def routedLookup (codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)) (read : Read Name)
    (width fuel : Nat) (root : Name) (key : Key) : Except (Fault Name) (Option Payload) :=
  route (readBlock codec read) width key fuel none root

/-- Precisely the decoded reference blocks needed on the selected path. A query
beyond the last separator needs no child, and other siblings are not required. -/
def PathReads (read : Name → Except (Fault Name) (Block Name Key Payload))
    (address : Block Name Key Payload → Name) (key : Key) :
    (level : Nat) → Node Key Payload level → Prop
  | 0, node => read (address (nodeBlock address 0 node)) = .ok (nodeBlock address 0 node)
  | level + 1, node =>
    read (address (nodeBlock address (level + 1) node)) = .ok (nodeBlock address (level + 1) node) ∧
      ∀ child, selectChild key node = some child → PathReads read address key level child.2

end Silmaril.Formats.Dasl.Prolly
