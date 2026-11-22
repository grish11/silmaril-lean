module

public import Silmaril.Semantics.Naming.Lift.Defs

public section

namespace Silmaril.Proofs.Semantics.Naming.Lift

open Silmaril.Semantics.Naming.Lift
open Silmaril.Semantics.Naming (Binding)

theorem matches_binding (coordinates : List Coordinate)
    (bound : ∀ coord ∈ coordinates, Binding coord.represents) : Binding (Matches coordinates) := by
  induction coordinates with
  | nil => intro _ left right _ _; cases left; cases right; rfl
  | cons coord rest ih =>
    intro input left right first second
    exact Prod.ext (bound coord (by simp) first.1 second.1)
      (ih (fun other member => bound other (List.mem_cons_of_mem _ member)) first.2 second.2)

end Silmaril.Proofs.Semantics.Naming.Lift
