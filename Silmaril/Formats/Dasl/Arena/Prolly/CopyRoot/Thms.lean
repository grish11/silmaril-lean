module

public import Silmaril.Formats.Dasl.Arena.Prolly.CopyRoot.Defs
import Silmaril.Proofs.Formats.Dasl.Arena.Prolly.CopyRoot

public section

namespace Silmaril.Formats.Dasl.Arena.Prolly.CopyRoot.Directory

open Silmaril.Formats.Dasl.Prolly (route)
open Silmaril.Semantics.Prolly (Block)

variable {Root Name Key Payload : Type} {before after : Directory Root Name Key Payload}

theorem empty_valid : (empty (Root := Root) (Name := Name) (Key := Key) (Payload := Payload)).Valid :=
  Proofs.Formats.Dasl.Arena.Prolly.CopyRoot.empty_valid

theorem copy_spec [DecidableEq Root] {root : Root} {block : Block (Handle Name) Key Payload} {index : Nat}
    (valid : before.Valid) (copied : before.copy? root block = some (after, index)) :
    after.Valid ∧ index = before.arena.blocks.size ∧ after.roots root = some (.local index) ∧
      (∀ other ≠ root, after.roots other = before.roots other) ∧ after.arena.blocks[index]? = some block ∧
      ∀ other : Nat, other ≠ index → after.arena.blocks[other]? = before.arena.blocks[other]? :=
  Proofs.Formats.Dasl.Arena.Prolly.CopyRoot.copy_spec valid copied

/-- Old live handles, including handles shared by alias roots, retain exact
routed observations. This theorem does not certify the newly supplied block. -/
theorem route_old [DecidableEq Root] [LinearOrder Key] {root : Root}
    {block : Block (Handle Name) Key Payload} {index : Nat} (valid : before.Valid)
    (copied : before.copy? root block = some (after, index)) (external : Reader Name Key Payload)
    (width fuel : Nat) (key : Key) {ref : Handle Name} (live : Indexed.KnownBefore before.arena.blocks.size ref) :
    route (after.arena.read external) width key fuel none ref = route (before.arena.read external) width key fuel none ref := by
  obtain ⟨_, atEnd, _, _, _, same⟩ := copy_spec valid copied
  exact Proofs.Formats.Dasl.Arena.Prolly.CopyRoot.route_frame valid external width fuel key
    (fun _ => Proofs.Formats.Dasl.Arena.Prolly.CopyRoot.read_frame atEnd same external) live

end Silmaril.Formats.Dasl.Arena.Prolly.CopyRoot.Directory
