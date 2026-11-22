module

public import Silmaril.Formats.Dasl.Arena.Prolly.Index.Defs
public import Silmaril.Formats.Dasl.Prolly.Replace.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Arena.Prolly.Indexed

open Silmaril.Semantics.Prolly (Block selectChild)
open Silmaril.Formats.Dasl.Prolly (Fault RootProfile encodeBlock)
open Silmaril.Formats.Dasl.Prolly.RootProfile (Replacement patchFirst)

variable {Name Key Payload : Type}

inductive EditPlanError (Name : Type) where
  | read (fault : Fault (Handle Name))
  | external (name : Name)
  | absent
  | naming (index : Nat)
  | dangling (index : Nat)
  deriving DecidableEq, Repr

inductive EditError (Name : Type) where
  | planning (reason : EditPlanError Name)
  | collision (name : Name)
  deriving DecidableEq, Repr

structure Edit (Name Key Payload : Type) where
  arena : Indexed Name Key Payload
  root : Nat
  named : Replacement Name Payload
  project : Handle Name → Name

def pin (project : Handle Name → Name) (index : Nat) (name : Name) : Handle Name → Name
  | .external old => project (.external old)
  | .local old => if old = index then name else project (.local old)

def Edit.PreservesNames (base : Nat) (project : Handle Name → Name) (edit : Edit Name Key Payload) : Prop :=
  ∀ ref, KnownBefore base ref → edit.project ref = project ref

/-- Every newly allocated block has a backward-only local shape and a byte
witness in the proposed batch, under the edit's extended name projection. -/
def BlocksStaged (profile : RootProfile Name Key Payload) (base : Nat) (arena : Indexed Name Key Payload)
    (project : Handle Name → Name) (writes : List (Name × ByteArray)) : Prop :=
  ∀ index, base ≤ index → index < arena.blocks.size →
    ∃ block value bytes, arena.blocks[index]? = some block ∧ admissible index block = true ∧
      encodeBlock profile.key profile.payload (relabel project block) = some value ∧
      profile.render? value = some bytes ∧ (project (.local index), bytes) ∈ writes

/-- Only the resident route needs corresponding named reads. The certificate
does not assert that any unselected or external block can be read. -/
def PathAgrees [LinearOrder Key] (arena : Indexed Name Key Payload) (project : Handle Name → Name)
    (read : Reader Name Key Payload) (key : Key) : Nat → Handle Name → Prop
  | 0, _ | _ + 1, .external _ => True
  | fuel + 1, .local index =>
    ∀ block, arena.blocks[index]? = some block →
      read (project (.local index)) = .ok (relabel project block) ∧
      match block with
      | .leaf _ => True
      | .branch _ children => ∀ child, selectChild key children = some child →
        PathAgrees arena project read key fuel child.2

def copyBlock (profile : RootProfile Name Key Payload) (oldName : Name) (project : Handle Name → Name)
    (old : Nat) (arena : Indexed Name Key Payload) (block : Block (Handle Name) Key Payload)
    (previous : Payload) (writes : List (Name × ByteArray)) :
    Except (EditPlanError Name) (Edit Name Key Payload) :=
  match arena.append? block with
  | none => .error (.dangling old)
  | some (next, root) =>
    match profile.emitReplacement oldName (relabel project block) previous writes with
    | .error _ => .error (.naming old)
    | .ok replacement => .ok ⟨next, root, replacement, pin project root replacement.root⟩

/-- Read only the original resident path. Copy from leaf to root, retaining
the old handles and names of unselected children. An external child on the
selected path needs localization first; unselected external children are allowed. -/
def planValue [LinearOrder Key] (arena : Indexed Name Key Payload) (profile : RootProfile Name Key Payload)
    (project : Handle Name → Name) (key : Key) (value : Payload) :
    (fuel : Nat) → Option Nat → Handle Name → Except (EditPlanError Name) (Edit Name Key Payload)
  | 0, _, ref => .error (.read (.fuel ref))
  | _ + 1, _, .external name => .error (.external name)
  | fuel + 1, expected, .local index => do
    let some block := arena.blocks[index]? | .error (.read (.missing (.local index)))
    match block with
    | .leaf entries =>
      if (expected = none ∨ expected = some 0) ∧ entries.length ≤ profile.policy.width ∧
          entries.Pairwise (fun left right => left.1 < right.1) then
        match entries.lookup key with
        | none => .error .absent
        | some previous =>
          let entries := patchFirst (fun entry => decide (key = entry.1)) (key, value) entries
          copyBlock profile (project (.local index)) project index arena (.leaf entries) previous []
      else .error (.read (.invalidNode (.local index)))
    | .branch level children =>
      if !admissible arena.blocks.size (.branch (Payload := Payload) level children) then .error (.dangling index)
      else if (expected = none ∨ expected = some level) ∧ 0 < level ∧ 0 < children.length ∧
          children.length ≤ profile.policy.width ∧ children.Pairwise (fun left right => left.1 < right.1) then
        match selectChild key children with
        | none => .error .absent
        | some child => do
          let edit ← arena.planValue profile project key value fuel (some (level - 1)) child.2
          let localChildren := patchFirst (fun entry => decide (key ≤ entry.1)) (child.1, .local edit.root) children
          copyBlock profile (project (.local index)) edit.project index edit.arena (.branch level localChildren)
            edit.named.previous edit.named.writes
      else .error (.read (.invalidNode (.local index)))

/-- A pure transaction: neither candidate arena nor byte snapshot is returned
on collision. The caller may switch its root only after success. -/
def replaceValue [LinearOrder Key] [DecidableEq Name] (arena : Indexed Name Key Payload)
    (profile : RootProfile Name Key Payload) (project : Handle Name → Name)
    (authoritative : Name → Option ByteArray) (fuel root : Nat) (key : Key) (value : Payload) :
    Except (EditError Name) (Edit Name Key Payload × (Name → Option ByteArray)) := do
  let edit ← (arena.planValue profile project key value fuel none (.local root)).mapError EditError.planning
  let staged ← (Silmaril.Semantics.Naming.admit authoritative edit.named.writes).mapError EditError.collision
  pure (edit, staged)

end Silmaril.Formats.Dasl.Arena.Prolly.Indexed
