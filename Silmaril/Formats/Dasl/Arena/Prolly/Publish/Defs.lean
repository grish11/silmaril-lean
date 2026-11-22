module

public import Silmaril.Formats.Dasl.Arena.Prolly.Index.Defs
public import Silmaril.Formats.Dasl.Prolly.Root.Publish.Defs
public import Silmaril.Semantics.Naming.Admission.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Arena.Prolly.Publish

open Silmaril.Formats.Dasl.Prolly (RootProfile encodeBlock)
open Silmaril.Semantics.Prolly (Block)
open Silmaril.Semantics.Naming (admit)

variable {Name Key Payload : Type}

structure Packed (profile : RootProfile Name Key Payload) where
  block : Block Name Key Payload
  shallow : Shallow Name
  bytes : ByteArray
  name : Name
  encoded : encodeBlock profile.key profile.payload block = some shallow
  rendered : profile.render? shallow = some bytes
  named : profile.hash? bytes = some name

def pack (profile : RootProfile Name Key Payload) (block : Block Name Key Payload) : Option (Packed profile) :=
  match encoded : encodeBlock profile.key profile.payload block with
  | none => none
  | some shallow => match rendered : profile.render? shallow with
    | none => none
    | some bytes => match named : profile.hash? bytes with
      | none => none
      | some name => some ⟨block, shallow, bytes, name, encoded, rendered, named⟩

structure Plan (profile : RootProfile Name Key Payload) where
  root : Name
  blocks : List (Packed profile)

def Plan.writes {profile : RootProfile Name Key Payload} (plan : Plan profile) : List (Name × ByteArray) :=
  plan.blocks.map fun packed => (packed.name, packed.bytes)

/-- Name local blocks bottom-up, emitting bytes and their profile witnesses.
Do not fetch, rewrite or claim availability of a pre-existing external name. -/
def stage (arena : Indexed Name Key Payload) (profile : RootProfile Name Key Payload) :
    Nat → Handle Name → Option (Plan profile)
  | _, .external name => some ⟨name, []⟩
  | 0, .local _ => none
  | fuel + 1, .local index => do
    match ← arena.blocks[index]? with
    | .leaf entries =>
      let packed ← pack profile (.leaf entries)
      pure ⟨packed.name, [packed]⟩
    | .branch level children =>
      let groups ← children.mapM fun (key, child) => (stage arena profile fuel child).map (key, ·)
      let packed ← pack profile (.branch level (groups.map fun (key, plan) => (key, plan.root)))
      pure ⟨packed.name, (groups.flatMap fun pair => pair.2.blocks) ++ [packed]⟩

inductive Fault (Name : Type) where
  | naming
  | collision (name : Name)
  deriving DecidableEq, Repr

/-- The supplied raw reader must be authoritative, not a partial view. A failed
plan or collision returns neither a new root name nor a staged raw snapshot. -/
def publish [DecidableEq Name] (arena : Indexed Name Key Payload) (profile : RootProfile Name Key Payload)
    (fuel index : Nat) (read : Name → Option ByteArray) : Except (Fault Name) (Name × (Name → Option ByteArray)) :=
  match stage arena profile fuel (.local index) with
  | none => .error .naming
  | some plan => ((admit read plan.writes).map (plan.root, ·)).mapError .collision

end Silmaril.Formats.Dasl.Arena.Prolly.Publish
