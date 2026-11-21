module

public import Silmaril.Semantics.Naming.Observations.Defs

public section

namespace Silmaril.Proofs.Semantics.Naming

open Silmaril.Semantics.Naming

theorem store_subset_antisymm {Name Obj Blob : Type} {left right : Stores Name Obj Blob}
    (first : left.Subset right) (second : right.Subset left) : left = right := by
  have objects : left.objects = right.objects := funext fun _ => funext fun _ =>
    propext ⟨fun hit => first.1 hit, fun hit => second.1 hit⟩
  have blobs : left.blobs = right.blobs := funext fun _ => funext fun _ =>
    propext ⟨fun hit => first.2 hit, fun hit => second.2 hit⟩
  cases left
  cases right
  cases objects
  cases blobs
  rfl

end Silmaril.Proofs.Semantics.Naming
