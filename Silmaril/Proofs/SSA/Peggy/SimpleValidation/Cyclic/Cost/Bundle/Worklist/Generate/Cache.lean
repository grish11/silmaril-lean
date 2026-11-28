module

public import Silmaril.SSA.PEG.Reindex.Automatic.Defs

public section

namespace Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate

open Silmaril.SSA.PEG

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}

theorem cached_node (g : Graph P params results n l) (i : Fin n) :
    (Reindex.Automatic.cacheRows g).node i = g.node i := by
  let rows := Vector.ofFn fun (j : Fin n) =>
    (⟨j, g.node j⟩ : Σ k, Node P params (Fin l) g.sort (g.sort k))
  have found : rows.get i = ⟨i, g.node i⟩ := by simp [rows, Vector.get, Fin.cast]
  have second {a b : Σ k, Node P params (Fin l) g.sort (g.sort k)}
      (eq : a = b) : HEq a.2 b.2 := by
    cases eq
    rfl
  have address : (rows.get i).1 = i := congrArg Sigma.fst found
  change (address ▸ (rows.get i).2) = g.node i
  exact eq_of_heq ((eqRec_heq (φ := fun k => Node P params (Fin l) g.sort (g.sort k))
    address (rows.get i).2).trans (second found))

end Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate
