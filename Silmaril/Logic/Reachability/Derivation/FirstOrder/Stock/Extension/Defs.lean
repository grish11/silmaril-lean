module

public import Silmaril.Logic.Reachability.Derivation.FirstOrder.Stock.Thms

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation.FirstOrder
open Silmaril.Logic.Institution.Examples
variable {Sg : FOL.Signature}
namespace Embedding

/-- Every finite context embeds using its actual coordinate numbers. -/
def canonical {k : Nat} (Γ : Fin k → Sg.S) : Embedding Γ where
  tag := Fin.val
  injective := fun _ _ h => Fin.ext h

/-- Extend an arbitrary local assignment at its exact embedded names. All other
names receive explicit sorted defaults; configuration remains a separate value. -/
noncomputable def extendLocal {k : Nat} {Γ : Fin k → Sg.S}
    (e : Embedding Γ) (M : FOL.Structure Sg) (defaults : (s : Sg.S) → M.carrier s)
    (a : (i : Fin k) → M.carrier (Γ i)) : StockAssignment M := by
  classical
  intro j
  exact if h : ∃ i : Fin k, e.name i = j then
    cast (congrArg M.carrier (congrArg Prod.fst (Classical.choose_spec h)))
      (a (Classical.choose h))
    else defaults j.1

end Embedding
end Silmaril.Logic.Reachability.Derivation.FirstOrder
