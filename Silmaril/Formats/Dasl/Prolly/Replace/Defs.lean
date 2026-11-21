module

public import Silmaril.Formats.Dasl.Prolly.Route.Defs
public import Silmaril.Formats.Dasl.Prolly.Root.Publish.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Prolly.RootProfile

open Silmaril.Semantics (OrderedMap)
open Silmaril.Semantics.Naming (Relation)
open Silmaril.Semantics.Prolly (Block Node selectChild blockOccurrences)

variable {Name Key Payload : Type}

inductive PlanFailure (Name : Type) where
  | read (fault : Fault Name)
  | absent
  | naming (old : Name)
  deriving DecidableEq, Repr

inductive ReplaceError (Name : Type) where
  | planning (reason : PlanFailure Name)
  | collision (name : Name)
  deriving DecidableEq, Repr

structure Replacement (Name Payload : Type) where
  previous : Payload
  root : Name
  writes : List (Name × ByteArray)

def Readback.pathReader {profile : RootProfile Name Key Payload} (reader : profile.Readback)
    (read : Name → Option ByteArray) : Read Name := fun name =>
  match read name with
  | none => .missing
  | some bytes => match reader.decode? bytes with
    | none => .invalidWire
    | some value => .found value

def patchFirst {Item : Type} (test : Item → Bool) (replacement : Item) (items : List Item) : List Item :=
  items.takeWhile (fun item => !test item) ++ replacement :: (items.dropWhile (fun item => !test item)).tail

def emitReplacement (profile : RootProfile Name Key Payload) (old : Name) (block : Block Name Key Payload)
    (previous : Payload) (writes : List (Name × ByteArray)) : Except (PlanFailure Name) (Replacement Name Payload) := do
  let some value := encodeBlock profile.key profile.payload block | .error (.naming old)
  let some bytes := profile.render? value | .error (.naming old)
  let some root := profile.hash? bytes | .error (.naming old)
  pure ⟨previous, root, (root, bytes) :: writes⟩

/-- Stage a value replacement at an existing key, visiting only the route.
Each ancestor keeps its level and separators; only the selected link is patched.
The batch is in root-to-leaf order. This does not certify unseen siblings. -/
def planReplacement [LinearOrder Key] (profile : RootProfile Name Key Payload)
    (read : Name → Except (Fault Name) (Block Name Key Payload)) (key : Key) (value : Payload) :
    (fuel : Nat) → Option Nat → Name → Except (PlanFailure Name) (Replacement Name Payload)
  | 0, _, name => .error (.read (.fuel name))
  | fuel + 1, expected, name => do
    match ← (read name).mapError PlanFailure.read with
    | .leaf entries =>
      if (expected = none ∨ expected = some 0) ∧ entries.length ≤ profile.policy.width ∧
          entries.Pairwise (fun left right => left.1 < right.1) then
        match entries.lookup key with
        | none => .error .absent
        | some previous =>
          profile.emitReplacement name (.leaf (patchFirst (fun entry => decide (key = entry.1)) (key, value) entries))
            previous []
      else .error (.read (.invalidNode name))
    | .branch level children =>
      if (expected = none ∨ expected = some level) ∧ 0 < level ∧ 0 < children.length ∧
          children.length ≤ profile.policy.width ∧ children.Pairwise (fun left right => left.1 < right.1) then
        match selectChild key children with
        | none => .error .absent
        | some child => do
          let planned ← profile.planReplacement read key value fuel (some (level - 1)) child.2
          profile.emitReplacement name
            (.branch level (patchFirst (fun entry => decide (key ≤ entry.1)) (child.1, planned.root) children))
            planned.previous planned.writes
      else .error (.read (.invalidNode name))

/-- The path reader may be incomplete. Admission must use an authoritative raw
snapshot. Failure returns no staged store, and no existing bytes are replaced. -/
def replaceValue [LinearOrder Key] [DecidableEq Name] (profile : RootProfile Name Key Payload)
    (reader : profile.Readback) (observed authoritative : Name → Option ByteArray) (fuel : Nat)
    (root : Name) (key : Key) (value : Payload) :
    Except (ReplaceError Name) (Replacement Name Payload × (Name → Option ByteArray)) := do
  let planned ← (profile.planReplacement (readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed))
    key value fuel none root).mapError ReplaceError.planning
  let staged ← (Silmaril.Semantics.Naming.admit authoritative planned.writes).mapError ReplaceError.collision
  pure (planned, staged)

/-- The semantic map after a value-only edit. On an absent key it is unchanged;
the path operation reports absence instead of publishing a no-op. -/
def replacedMap [LinearOrder Key] (map : OrderedMap Key Payload) (key : Key) (value : Payload) : OrderedMap Key Payload :=
  ⟨map.entries.map (fun entry => (entry.1, if key = entry.1 then value else entry.2)),
    List.pairwise_map.mpr map.ordered⟩

/-- All reachable blocks have readable renderings at their prescribed profile
names. This is a reference invariant, not a traversal performed by the editor. -/
def NodeBytes (profile : RootProfile Name Key Payload) (address : Block Name Key Payload → Name)
    (reference : Relation Name ByteArray) (level : Nat) (node : Node Key Payload level) : Prop :=
  ∀ block ∈ blockOccurrences address level node, ∃ value bytes,
    encodeBlock profile.key profile.payload block = some value ∧ profile.render? value = some bytes ∧
    profile.hash? bytes = some (address block) ∧ reference (address block) bytes

end Silmaril.Formats.Dasl.Prolly.RootProfile
