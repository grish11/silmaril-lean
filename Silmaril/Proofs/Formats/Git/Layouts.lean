module

public import Silmaril.Formats.Git.Dasl.Layouts.Defs

public section

namespace Silmaril.Proofs.Formats.Git

open Silmaril.Formats.Git Silmaril.Formats.Git.Dasl
open Silmaril.Formats.Dasl (Shallow Store)
open Silmaril.Semantics.Prolly (Policy build blockOccurrences)

theorem prolly_stored {Key Name : Type} [LinearOrder Key] (policy : Policy Key)
    (key : Formats.Dasl.Encode.TotalCodec Key (Shallow Name)) (naming : Naming Name)
    (dir : ShallowTree Key Name) {root : Shallow Name} {store : Store Name}
    (hit : (Layout.prolly policy key).encode? naming dir = some (root, store)) :
    Formats.Dasl.Prolly.Stored (Formats.Dasl.Prolly.blockCodec key entryCodec)
      (prollyAddress naming key) (build policy dir.ordered) store ∧
    (build policy dir.ordered).rootName (prollyAddress naming key) = naming.object root := by
  unfold Layout.prolly at hit
  dsimp only at hit
  split at hit
  next good =>
    obtain ⟨encoded, rootHit, same⟩ := Option.bind_eq_some_iff.mp hit
    cases same
    constructor
    · intro block member
      have supported := List.all_eq_true.mp good block member
      obtain ⟨value, rendered⟩ := Option.isSome_iff_exists.mp supported
      exact ⟨value, rendered, block, member, rfl, rendered⟩
    · simp [Semantics.Prolly.Tree.rootName, prollyAddress, rootHit]
  next => contradiction

end Silmaril.Proofs.Formats.Git
