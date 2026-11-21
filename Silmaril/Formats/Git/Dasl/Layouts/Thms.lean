module

public import Silmaril.Formats.Git.Dasl.Layouts.Defs
import Silmaril.Proofs.Formats.Git.Layouts

public section

namespace Silmaril.Formats.Git.Dasl

open Silmaril.Formats.Dasl
open Silmaril.Semantics.Prolly (Policy build)

/-- Reuse the DASL Prolly store/read theorems for a successfully encoded Git
directory. The returned root block has the same name as the builder's root. -/
theorem Layout.prolly_stored {Key Name : Type} [LinearOrder Key] (policy : Policy Key)
    (key : Encode.TotalCodec Key (Shallow Name)) (naming : Naming Name)
    (dir : ShallowTree Key Name) {root : Shallow Name} {store : Store Name}
    (hit : (Layout.prolly policy key).encode? naming dir = some (root, store)) :
    Prolly.Stored (Prolly.blockCodec key entryCodec) (prollyAddress naming key) (build policy dir.ordered) store ∧
    (build policy dir.ordered).rootName (prollyAddress naming key) = naming.object root :=
  Proofs.Formats.Git.prolly_stored policy key naming dir hit

end Silmaril.Formats.Git.Dasl
